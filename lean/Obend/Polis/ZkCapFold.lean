module
/-
# Obend.Polis.ZkCapFold — Two-Phase Post-Quantum Capability Rollups & Live-Epoch Sorted-Gap Cone Revocation

Solves the Monday-Fold / Saturday-Revocation epoch-coupling trap and deterministic `lineage`
linkability of `Obend.Polis.ZkBiscuit` via an epoch-decoupled two-phase post-quantum capability rollup:

1. **Full 256-Bit Nullifiers, Domain-Separated Padding Slots & 8-Limb Goldilocks Bijection**:
   - `Nullifier256 := BitVec 256` strictly between sentinel bounds `0#256` and `2^256 - 1`
     (`BitVec.allOnes 256`), with default rollup depth `defaultCapMaxHops := 8` and parameterized `kMax`.
   - `padSlotNul256` hashes `3 :: (be 32 salt.toNat ++ leb128 idx)` under `nulCustomization`,
     provably separated from `credNul256` (`1 :: ...`) and `chanNul256` (`2 :: ...`) up to
     `CollisionAmong nulHash`.
   - Bijective 8 × 32-bit `Goldilocks` encoding (`decodeGold8_encodeBitVec256`) preserving all 256 bits.
2. **Live-Epoch Authenticated Sorted-Gap Table (`RevokedSet256`, `RevokedGapRoot256`)**:
   - Represents epoch `e`'s strictly sorted interior `RevokedSet256` as adjacent intervals
     `G_e = {(r_j, r_{j+1})}` (`0 ≤ j ≤ |R_e|`) with `r_0 = 0` and `r_{|R_e|+1} = 2^256 - 1`,
     committed with `epoch` length-framed into every Merkle leaf (`gapLeafPreimage`).
   - **Gap-Disjointness Equivalence (`not_mem_revoked_iff_in_unique_gap`)**: for every interior
     256-bit nullifier `x`, `x ∉ R_e ↔ ∃! j, r_j < x < r_{j+1}`, with `O(log |R_e|)` binary search
     witness generation (`findGapIdxExec`) and `O(log |R_e|)` Merkle gap authentication (`verifyGapSlotOpening`).
3. **Phase 1 — Epoch-Free Offline Hop Folding (`foldChainEpochFree` → `OfflineCapBundle`)**:
   - Folds root grant `g` + `k ≤ kMax` PQ-signed hops (`HopSigScheme`, inhabited by 256-bit
     `pqLamport256HopSig`) **independently of `RevokedSet256`**, checking monotone `subMask` and
     tightening `epochFloor` (`foldChainEpochFree_attenuation_monotone`), partially evaluating static
     caveats into `ResidualCaveat` (`pevalCaveat_eval_eq`), and committing the fixed-arity
     `2 * kMax + 2` nullifier vector + 256-bit salt into a Dual-Spine commitment
     `nulVecCommit : CanopyCommitment × AjtaiCommitment` (`padded_nullifier_arity_depth_invariant`).
4. **Phase 2 — Live-Epoch Presentation & Unlinkable Per-Turn Nullifier (`EpochPresentationCert`)**:
   - Emits `presNul = cSHAKE256("OBEND.CAPFOLD.PRES/v1", frame(epoch, secretSalt, turnId, lineage))`
     (`presNul_binds_or_collides`, `presNul_cross_turn_distinct_preimages`, `saltXorMask_bijective`).
   - Enforces live epoch floor and gap-root epoch binding (`checkLiveEpochBound`), Fenzi-safe
     Fiat–Shamir transcript binding, `DualSpine` Sumcheck + Canopy/Ajtai opening, Lyubashevsky
     smudged `verifyMaskedAjtaiOpening`, and all `2 * kMax + 2` strict sorted-gap openings.
   - **Constructive `0 Classical.choice` `PSum` Soundness & Collision Extractor
     (`extractEpochPresentationOrFoldChain`, `ZkCapFoldBreakWitness.toCshakeCollisionPair`)** and
     **Bidirectional Equivalence (`zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`)**.
5. **Multi-Turn `ValidCapEpochTrace` / `runCapFoldTrace`, Unrelated-Revocation Reuse & Retroactive Cone Revocation**:
   - Inductive `ValidCapEpochTrace` (with invariant-free `.nil`) and executable `runCapFoldTrace`:
     - **Epoch-Decoupled Reuse (`unrelated_revocations_preserve_folded_bundle`)**: advancing `(epoch, revokedGapRoot)`
       by revoking unrelated nullifiers preserves validity of existing `OfflineCapBundle` by refreshing only
       the `O(kMax · log |R_e|)` gap witnesses, without re-opening or re-proving static hop signatures.
     - **Retroactive Cone Kill (`retroactive_ancestor_revocation_kills_pre_folded_cone`,
       `retroactive_ancestor_revocation_forces_refresh_false`)**: revoking ANY ancestor hop `j ≤ k` at
       `e_rev > e_fold` kills every pre-folded descendant at all `e ≥ e_rev`.
-/
public import Obend.Polis.ZkBiscuit
public import Obend.Crypto.DualSpine
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.BlumRam
import all Obend.Polis.ZkBiscuit
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Crypto.GameSoundness
import all Obend.Crypto.DualSpine
import all Obend.Judge.Computational

public section
namespace Obend.Polis.ZkCapFold

open Obend.Polis
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Apps.ZkNtt
open Obend.Judge.Computational (HashCollisionWitness PinnedCollision SISShortVecWitness)

set_option autoImplicit false

/-! ## 1. Full 256-Bit Nullifiers, Sentinel Bounds, Salted Padding Slots & Goldilocks-8 Bijection -/

/-- Full-width 256-bit capability/channel/presentation nullifier carrier. -/
abbrev Nullifier256 := BitVec 256

/-- Default maximum delegation chain depth (`K_max = 8`, yielding `2 * 8 + 2 = 18` nullifier slots). -/
def defaultCapMaxHops : Nat := 8

/-- Lower sentinel `0` of the 256-bit sorted-gap table. -/
def minSentinel256 : BitVec 256 := 0#256

/-- Upper sentinel `2^256 - 1` of the 256-bit sorted-gap table. -/
def maxSentinel256 : BitVec 256 := BitVec.allOnes 256

private theorem minSentinel256_toNat : minSentinel256.toNat = 0 := by rfl

private theorem maxSentinel256_toNat : maxSentinel256.toNat = 2 ^ 256 - 1 := by
  unfold maxSentinel256
  exact BitVec.toNat_allOnes

/-- Interior 256-bit nullifier predicate (`0 < x < 2^256 - 1`), strictly between the gap sentinels. -/
@[expose] def IsInteriorNullifier256 (x : BitVec 256) : Prop :=
  minSentinel256 < x ∧ x < maxSentinel256

def checkInteriorNullifier256 (x : BitVec 256) : Bool :=
  decide (minSentinel256 < x) && decide (x < maxSentinel256)

theorem checkInteriorNullifier256_iff (x : BitVec 256) :
    checkInteriorNullifier256 x = true ↔ IsInteriorNullifier256 x := by
  simp [checkInteriorNullifier256, IsInteriorNullifier256]

/-- Domain-separated preimage `3 :: (be 32 salt || leb128 padIdx)` for salted padding slots. -/
def padSlotPreimage (salt : BitVec 256) (padIdx : Nat) : List UInt8 :=
  3 :: (be 32 salt.toNat ++ leb128 padIdx)

theorem padSlotPreimage_injective {s₁ s₂ : BitVec 256} {i₁ i₂ : Nat}
    (h : padSlotPreimage s₁ i₁ = padSlotPreimage s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  simp only [padSlotPreimage, List.cons.injEq] at h
  obtain ⟨hs, hi⟩ := List.append_inj h.2 (by simp [length_be])
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hsEq := be_injective (hpow ▸ s₁.isLt) (hpow ▸ s₂.isLt) hs
  have hiEq := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hi)).1
  exact ⟨BitVec.eq_of_toNat_eq hsEq, hiEq⟩

/-- Natural reading of the domain-separated salted padding-slot nullifier. -/
def padSlotNul (salt : BitVec 256) (padIdx : Nat) : Nat :=
  ofBE (nulHash (padSlotPreimage salt padIdx))

theorem padSlotNul_lt (salt : BitVec 256) (padIdx : Nat) :
    padSlotNul salt padIdx < 2 ^ 256 := by
  unfold padSlotNul
  have hlen : (nulHash (padSlotPreimage salt padIdx)).length = 32 :=
    cshake256Bytes_length nulCustomization _
  have hlt := ofBE_lt (nulHash (padSlotPreimage salt padIdx))
  rw [hlen] at hlt
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  exact hpow ▸ hlt

/-- Full 256-bit domain-separated salted padding-slot nullifier hiding delegation depth `k ≤ kMax`. -/
def padSlotNul256 (salt : BitVec 256) (padIdx : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (padSlotNul salt padIdx)

theorem padSlotNul256_toNat (salt : BitVec 256) (padIdx : Nat) :
    (padSlotNul256 salt padIdx).toNat = padSlotNul salt padIdx := by
  unfold padSlotNul256
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (padSlotNul_lt salt padIdx)

/-- Salted padding nullifiers (`3 :: ...`) never collide with `credNul256` (`1 :: ...`) without a
    constructive `nulHash` collision. -/
theorem padSlot_credNul_separated (salt : BitVec 256) (padIdx : Nat) (lineage : ByteArray)
    (h : padSlotNul256 salt padIdx = credNul256 lineage) :
    CollisionAmong nulHash
      (fun x => x = padSlotPreimage salt padIdx ∨ x = 1 :: lineage.data.toList) := by
  have hn : (padSlotNul256 salt padIdx).toNat = (credNul256 lineage).toNat :=
    congrArg BitVec.toNat h
  rw [padSlotNul256_toNat, credNul256_toNat, credNul_eq] at hn
  exact ⟨padSlotPreimage salt padIdx, 1 :: lineage.data.toList, .inl rfl, .inr rfl,
    fun e => absurd (List.cons.inj e).1 (by decide), hn⟩

/-- Salted padding nullifiers (`3 :: ...`) never collide with `chanNul256` (`2 :: ...`) without a
    constructive `nulHash` collision. -/
theorem padSlot_chanNul_separated (salt : BitVec 256) (padIdx : Nat) (channel : ByteArray)
    (h : padSlotNul256 salt padIdx = chanNul256 channel) :
    CollisionAmong nulHash
      (fun x => x = padSlotPreimage salt padIdx ∨ x = 2 :: channel.data.toList) := by
  have hn : (padSlotNul256 salt padIdx).toNat = (chanNul256 channel).toNat :=
    congrArg BitVec.toNat h
  rw [padSlotNul256_toNat, chanNul256_toNat, chanNul_eq] at hn
  exact ⟨padSlotPreimage salt padIdx, 2 :: channel.data.toList, .inl rfl, .inr rfl,
    fun e => absurd (List.cons.inj e).1 (by decide), hn⟩

attribute [local irreducible] cshake256Bytes cshake32ByteArray credNul chanNul rootLineage stepLineage

private theorem be_ofBE_rev : ∀ (r : List UInt8), be r.reverse.length (ofBE r.reverse) = r.reverse
  | [] => rfl
  | b :: init => by
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [List.reverse_cons, List.length_append, List.length_singleton, ofBE_append_single, be]
    have hdiv : (ofBE init.reverse * 256 + b.toNat) / 256 = ofBE init.reverse := by omega
    have hmod : (ofBE init.reverse * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [hdiv, hmod, be_ofBE_rev init, UInt8.ofNat_toNat]

private theorem be_ofBE (bs : List UInt8) : be bs.length (ofBE bs) = bs := by
  have h := be_ofBE_rev bs.reverse
  simpa [List.reverse_reverse] using h

/-- Exact byte-list equality of 32-byte digests from equal `ofBE` integer readings (`0 Classical`). -/
theorem hash32_eq_of_ofBE_eq (H : Hash32) {m₁ m₂ : List UInt8}
    (h : ofBE (H.eval m₁) = ofBE (H.eval m₂)) :
    H.eval m₁ = H.eval m₂ := by
  have h₁ := be_ofBE (H.eval m₁)
  have h₂ := be_ofBE (H.eval m₂)
  rw [H.len_eq m₁] at h₁
  rw [H.len_eq m₂] at h₂
  rw [← h₁, ← h₂, h]

/-- Explicit byte-level `cSHAKE256` / `Hash` collision pair `(msgA, msgB)` with `msgA ≠ msgB`
    and `H msgA = H msgB`. -/
structure CshakeCollisionPair (H : Hash) where
  msgA : List UInt8
  msgB : List UInt8
  distinct : msgA ≠ msgB
  sameDigest : H msgA = H msgB
  deriving DecidableEq

/-- Decompose `n` into `k` canonical 32-bit `Goldilocks` limbs (`2^32 < goldilocksPrime`). -/
def natToLimbs32 : Nat → Nat → List Goldilocks
  | 0, _ => []
  | k + 1, n =>
    ⟨n % 4294967296, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩ ::
      natToLimbs32 k (n / 4294967296)

theorem natToLimbs32_length : ∀ (k n : Nat), (natToLimbs32 k n).length = k
  | 0, _ => by rfl
  | k + 1, n => by simp [natToLimbs32, natToLimbs32_length k]

/-- Reassemble canonical 32-bit `Goldilocks` limbs into a natural number, rejecting `val ≥ 2^32`. -/
def limbs32ToNat : List Goldilocks → Option Nat
  | [] => some 0
  | g :: gs =>
    if g.val < 4294967296 then
      match limbs32ToNat gs with
      | some hi => some (g.val + 4294967296 * hi)
      | none => none
    else none

theorem limbs32ToNat_natToLimbs32 :
    ∀ (k n : Nat), n < 4294967296 ^ k → limbs32ToNat (natToLimbs32 k n) = some n
  | 0, n, hn => by
    have hz : n = 0 := by simp at hn; exact hn
    subst hz; rfl
  | k + 1, n, hn => by
    have hpow : 4294967296 ^ (k + 1) = 4294967296 ^ k * 4294967296 := Nat.pow_succ ..
    have hdiv : n / 4294967296 < 4294967296 ^ k :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    have hmod : n % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
    simp only [natToLimbs32, limbs32ToNat, hmod, ↓reduceIte, limbs32ToNat_natToLimbs32 k _ hdiv,
      Option.some.injEq]
    omega

/-- Full-width 8-limb `Goldilocks` encoding of `BitVec 256` (`8 × 32 = 256` bits, zero truncation). -/
def encodeBitVec256Gold8 (x : BitVec 256) : List Goldilocks :=
  natToLimbs32 8 x.toNat

theorem encodeBitVec256Gold8_length (x : BitVec 256) :
    (encodeBitVec256Gold8 x).length = 8 := by
  exact natToLimbs32_length 8 x.toNat

/-- Inverse decoder from 8 `Goldilocks` limbs back to `BitVec 256`. -/
def decodeGold8BitVec256 (gs : List Goldilocks) : Option (BitVec 256) :=
  if gs.length == 8 then
    match limbs32ToNat gs with
    | some n => if n < 2 ^ 256 then some (BitVec.ofNat 256 n) else none
    | none => none
  else none

theorem decodeGold8_encodeBitVec256 (x : BitVec 256) :
    decodeGold8BitVec256 (encodeBitVec256Gold8 x) = some x := by
  unfold decodeGold8BitVec256 encodeBitVec256Gold8
  have hlen : (natToLimbs32 8 x.toNat).length == 8 := by simp [natToLimbs32_length]
  have hpow : (2 : Nat) ^ 256 = 4294967296 ^ 8 := by decide
  have hrec := limbs32ToNat_natToLimbs32 8 x.toNat (hpow ▸ x.isLt)
  simp only [hlen, ↓reduceIte, hrec, x.isLt, Option.some.injEq]
  exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem encodeBitVec256Gold8_injective {x y : BitVec 256}
    (h : encodeBitVec256Gold8 x = encodeBitVec256Gold8 y) : x = y := by
  have hd := congrArg decodeGold8BitVec256 h
  rw [decodeGold8_encodeBitVec256, decodeGold8_encodeBitVec256, Option.some.injEq] at hd
  exact hd

/-! ## 2. `RevokedSet256`, Epoch-Bound Authenticated Sorted-Gap Table & `not_mem_revoked_iff_in_unique_gap` -/

/-- Insert `x` into a strictly sorted `List (BitVec 256)`, deduplicating on equality. -/
def insertSorted256 (x : BitVec 256) : List (BitVec 256) → List (BitVec 256)
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertSorted256 x ys

theorem mem_insertSorted256 (x z : BitVec 256) :
    ∀ (l : List (BitVec 256)), z ∈ insertSorted256 x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertSorted256]
  | y :: ys => by
    if h1 : x < y then
      simp [insertSorted256, h1]
    else if h2 : x = y then
      subst h2; simp [insertSorted256]
    else
      simp only [insertSorted256, h1, h2, ↓reduceIte, List.mem_cons, mem_insertSorted256 x z ys]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem insertSorted256_pairwise (x : BitVec 256) :
    ∀ (l : List (BitVec 256)), l.Pairwise (· < ·) → (insertSorted256 x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted256]
  | y :: ys, hp => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp
    if h1 : x < y then
      simp only [insertSorted256, h1, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, hp⟩
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact h1
      · have hxy : x.toNat < y.toNat := BitVec.lt_def.1 h1
        have hya : y.toNat < a.toNat := BitVec.lt_def.1 (hy a ha')
        exact BitVec.lt_def.2 (Nat.lt_trans hxy hya)
    else if h2 : x = y then
      subst h2
      have hirr : ¬ (x < x) := fun h => Nat.lt_irrefl _ (BitVec.lt_def.1 h)
      simp only [insertSorted256, hirr, eq_self, ↓reduceIte]
      exact hp
    else
      simp only [insertSorted256, h1, h2, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, insertSorted256_pairwise x ys hys⟩
      rcases (mem_insertSorted256 x a ys).1 ha with hax | ha'
      · rw [hax]
        have hne : x.toNat ≠ y.toNat := fun he => h2 (BitVec.eq_of_toNat_eq he)
        have hnlt : ¬ (x.toNat < y.toNat) := fun hl => h1 (BitVec.lt_def.2 hl)
        exact BitVec.lt_def.2 (by omega)
      · exact hy a ha'

theorem insertSorted256_interior (x : BitVec 256) (hx : IsInteriorNullifier256 x)
    (l : List (BitVec 256)) (hl : ∀ y ∈ l, IsInteriorNullifier256 y) :
    ∀ z ∈ insertSorted256 x l, IsInteriorNullifier256 z := by
  intro z hz
  rcases (mem_insertSorted256 x z l).1 hz with rfl | hzl
  · exact hx
  · exact hl z hzl

/-- Binary search for `x` in strictly sorted `keys : Array (BitVec 256)` (`O(log |R_e|)`). -/
def searchAux256 (keys : Array (BitVec 256)) (x : BitVec 256) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2
      if hm : mid < keys.size then
        if keys[mid] = x then true
        else if keys[mid] < x then searchAux256 keys x fuel (mid + 1) hi
        else searchAux256 keys x fuel lo mid
      else false
    else false

theorem searchAux256_sound (keys : Array (BitVec 256)) (x : BitVec 256) :
    ∀ (fuel lo hi : Nat), hi ≤ keys.size →
      searchAux256 keys x fuel lo hi = true → x ∈ keys.toList
  | 0, _, _, _, h => by simp [searchAux256] at h
  | fuel + 1, lo, hi, hsz, h => by
    if hlt : lo < hi then
      have hmid : lo + (hi - lo) / 2 < keys.size := by omega
      simp only [searchAux256, hlt, hmid, ↓reduceIte, ↓reduceDIte] at h
      if h1 : keys[lo + (hi - lo) / 2] = x then
        rw [← h1]; exact Array.getElem_mem_toList hmid
      else
        simp only [h1, ↓reduceIte] at h
        if h2 : keys[lo + (hi - lo) / 2] < x then
          simp only [h2, ↓reduceIte] at h
          exact searchAux256_sound keys x fuel _ hi hsz h
        else
          simp only [h2, ↓reduceIte] at h
          exact searchAux256_sound keys x fuel lo _ (by omega) h
    else
      simp [searchAux256, hlt] at h

theorem searchAux256_complete (keys : Array (BitVec 256)) (x : BitVec 256)
    (hs : ∀ (i j : Nat) (hi : i < keys.size) (hj : j < keys.size), i < j → keys[i] < keys[j]) :
    ∀ (fuel lo hi : Nat), hi ≤ keys.size → hi - lo ≤ fuel →
      ∀ (i : Nat) (hi' : i < keys.size), lo ≤ i → i < hi → keys[i] = x →
        searchAux256 keys x fuel lo hi = true
  | 0, lo, hi, _, hf, i, _, hlo, hhi, _ => by omega
  | fuel + 1, lo, hi, hsz, hf, i, hi', hlo, hhi, hx => by
    have hlt : lo < hi := by omega
    have hmid : lo + (hi - lo) / 2 < keys.size := by omega
    simp only [searchAux256, hlt, hmid, ↓reduceIte, ↓reduceDIte]
    if h1 : keys[lo + (hi - lo) / 2] = x then
      simp [h1]
    else
      simp only [h1, ↓reduceIte]
      if h2 : keys[lo + (hi - lo) / 2] < x then
        simp only [h2, ↓reduceIte]
        have hgt : lo + (hi - lo) / 2 < i := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · have hord := BitVec.lt_def.1 (hs i _ hi' hmid h)
            have h2n := BitVec.lt_def.1 h2
            have hxn : keys[i].toNat = x.toNat := congrArg BitVec.toNat hx
            omega
          · subst h; exact absurd hx h1
          · exact h
        exact searchAux256_complete keys x hs fuel _ hi hsz (by omega) i hi' (by omega) hhi hx
      else
        simp only [h2, ↓reduceIte]
        have hlt' : i < lo + (hi - lo) / 2 := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · exact h
          · subst h; exact absurd hx h1
          · have hord := BitVec.lt_def.1 (hs _ i hmid hi' h)
            have h2n : ¬ (keys[lo + (hi - lo) / 2].toNat < x.toNat) := fun hl => h2 (BitVec.lt_def.2 hl)
            have hxn : keys[i].toNat = x.toNat := congrArg BitVec.toNat hx
            omega
        exact searchAux256_complete keys x hs fuel lo _ (by omega) (by omega) i hi' hlo hlt' hx

/-- Epoch `e`'s strictly sorted set of interior 256-bit revoked nullifiers (`0 < r_j < 2^256 - 1`). -/
structure RevokedSet256 where
  keys : Array (BitVec 256)
  sorted : keys.toList.Pairwise (· < ·)
  interior : ∀ x ∈ keys.toList, IsInteriorNullifier256 x

namespace RevokedSet256

def empty : RevokedSet256 := ⟨#[], List.Pairwise.nil, fun _ h => by cases h⟩

theorem ext {s₁ s₂ : RevokedSet256} (h : s₁.keys = s₂.keys) : s₁ = s₂ := by
  obtain ⟨k₁, _, _⟩ := s₁
  obtain ⟨k₂, _, _⟩ := s₂
  cases h
  rfl

instance : DecidableEq RevokedSet256 := fun a b =>
  if h : a.keys = b.keys then isTrue (ext h) else isFalse (fun e => h (e ▸ rfl))

def contains (s : RevokedSet256) (x : BitVec 256) : Bool :=
  searchAux256 s.keys x s.keys.size 0 s.keys.size

theorem sorted_getElem (s : RevokedSet256) (i j : Nat) (hi : i < s.keys.size)
    (hj : j < s.keys.size) (hij : i < j) : s.keys[i] < s.keys[j] := by
  have h := List.pairwise_iff_getElem.1 s.sorted i j (by simpa using hi) (by simpa using hj) hij
  simpa using h

theorem contains_iff (s : RevokedSet256) (x : BitVec 256) :
    s.contains x = true ↔ x ∈ s.keys.toList := by
  constructor
  · exact searchAux256_sound s.keys x _ 0 _ (Nat.le_refl _)
  · intro hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.1 hx
    have hi' : i < s.keys.size := by simpa using hi
    exact searchAux256_complete s.keys x s.sorted_getElem _ 0 _ (Nat.le_refl _) (by omega) i hi'
      (Nat.zero_le _) hi' (by simpa using hxi)

def insert (s : RevokedSet256) (x : BitVec 256) (hx : IsInteriorNullifier256 x) : RevokedSet256 :=
  ⟨(insertSorted256 x s.keys.toList).toArray,
   by simpa using insertSorted256_pairwise x _ s.sorted,
   by intro z hz; exact insertSorted256_interior x hx _ s.interior z (by simpa using hz)⟩

theorem contains_insert (s : RevokedSet256) (x y : BitVec 256) (hx : IsInteriorNullifier256 x) :
    (s.insert x hx).contains y = true ↔ y = x ∨ s.contains y = true := by
  rw [contains_iff, contains_iff]
  simpa [insert] using mem_insertSorted256 x y s.keys.toList

theorem contains_insert_self (s : RevokedSet256) (x : BitVec 256) (hx : IsInteriorNullifier256 x) :
    (s.insert x hx).contains x = true := by
  exact (contains_insert s x x hx).2 (.inl rfl)

theorem contains_insert_of_contains (s : RevokedSet256) (x y : BitVec 256)
    (hx : IsInteriorNullifier256 x) (hy : s.contains y = true) :
    (s.insert x hx).contains y = true := by
  exact (contains_insert s x y hx).2 (.inr hy)

theorem contains_insert_false_of_ne (s : RevokedSet256) {x y : BitVec 256}
    (hx : IsInteriorNullifier256 x) (hy : s.contains y = false) (hne : y ≠ x) :
    (s.insert x hx).contains y = false := by
  cases hc : (s.insert x hx).contains y with
  | false => rfl
  | true =>
    rcases (contains_insert s x y hx).1 hc with rfl | hOld
    · exact absurd rfl hne
    · rw [hy] at hOld; cases hOld

/-- Lossless projection from `RevokedSet256` to `ZkBiscuit.RevokedSet`. -/
def toRevokedSet (s : RevokedSet256) : RevokedSet where
  keys := s.keys.map BitVec.toNat
  sorted := by
    rw [Array.toList_map, List.pairwise_map]
    exact s.sorted.imp fun {a b} hab => BitVec.lt_def.1 hab

theorem toRevokedSet_contains_eq (s : RevokedSet256) (x : BitVec 256) :
    s.toRevokedSet.contains x.toNat = s.contains x := by
  apply Bool.eq_iff_iff.2
  rw [RevokedSet.contains_iff, contains_iff]
  simp only [toRevokedSet, Array.toList_map, List.mem_map]
  constructor
  · rintro ⟨y, hy, hyn⟩
    exact BitVec.eq_of_toNat_eq hyn ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end RevokedSet256

/-- `O(1)` unboxed sentinel-bounded indexing `r_0 = 0, r_{k+1} = keys[k], r_{|R|+1} = 2^256 - 1`. -/
@[expose] def boundedAt (rs : RevokedSet256) (idx : Nat) : BitVec 256 :=
  if idx == 0 then minSentinel256
  else if h : idx - 1 < rs.keys.size then rs.keys[idx - 1]'h
  else maxSentinel256

theorem boundedAt_zero (rs : RevokedSet256) : boundedAt rs 0 = minSentinel256 := by rfl

theorem boundedAt_succ_lt (rs : RevokedSet256) (k : Nat) (hk : k < rs.keys.size) :
    boundedAt rs (k + 1) = rs.keys[k]'hk := by
  simp [boundedAt, hk]

theorem boundedAt_last (rs : RevokedSet256) :
    boundedAt rs (rs.keys.size + 1) = maxSentinel256 := by
  unfold boundedAt
  have h0 : ((rs.keys.size + 1 == 0) = false) := by simp
  have h1 : ¬ (rs.keys.size < rs.keys.size) := Nat.lt_irrefl _
  simp [h0, h1]

theorem boundedAt_strictMono (rs : RevokedSet256) {i j : Nat}
    (hij : i < j) (hj : j ≤ rs.keys.size + 1) :
    boundedAt rs i < boundedAt rs j := by
  cases i with
  | zero =>
    rw [boundedAt_zero]
    if hjk : j - 1 < rs.keys.size then
      have hjEq : j = (j - 1) + 1 := by omega
      rw [hjEq, boundedAt_succ_lt rs (j - 1) hjk]
      exact (rs.interior _ (Array.getElem_mem_toList hjk)).1
    else
      have hjLast : j = rs.keys.size + 1 := by omega
      rw [hjLast, boundedAt_last]
      exact BitVec.lt_def.2 (by rw [minSentinel256_toNat, maxSentinel256_toNat]; decide)
  | succ i' =>
    have hi' : i' < rs.keys.size := by omega
    rw [boundedAt_succ_lt rs i' hi']
    if hjk : j - 1 < rs.keys.size then
      have hjEq : j = (j - 1) + 1 := by omega
      rw [hjEq, boundedAt_succ_lt rs (j - 1) hjk]
      exact rs.sorted_getElem i' (j - 1) hi' hjk (by omega)
    else
      have hjLast : j = rs.keys.size + 1 := by omega
      rw [hjLast, boundedAt_last]
      exact (rs.interior _ (Array.getElem_mem_toList hi')).2

theorem boundedAt_mono (rs : RevokedSet256) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ rs.keys.size + 1) :
    boundedAt rs i ≤ boundedAt rs j := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · exact BitVec.le_def.2 (Nat.le_of_lt (BitVec.lt_def.1 (boundedAt_strictMono rs hlt hj)))
  · exact BitVec.le_def.2 (Nat.le_refl _)

/-- One adjacent interval `(lo, hi) = (r_j, r_{j+1})` in the Authenticated Sorted-Gap Table. -/
structure GapEntry256 where
  lo : BitVec 256
  hi : BitVec 256
  deriving DecidableEq, Repr

@[expose] def gapEntryAt (rs : RevokedSet256) (j : Nat) : GapEntry256 :=
  ⟨boundedAt rs j, boundedAt rs (j + 1)⟩

/-- Full Authenticated Sorted-Gap Table `G_e = {(r_j, r_{j+1}) | 0 ≤ j ≤ |R_e|}`. -/
def gapTable (rs : RevokedSet256) : Array GapEntry256 :=
  Array.ofFn fun j : Fin (rs.keys.size + 1) => gapEntryAt rs j.val

theorem gapTable_size (rs : RevokedSet256) : (gapTable rs).size = rs.keys.size + 1 := by
  simp [gapTable]

theorem gapTable_getElem (rs : RevokedSet256) (j : Nat) (hj : j < rs.keys.size + 1) :
    (gapTable rs)[j]'(by rw [gapTable_size]; exact hj) = gapEntryAt rs j := by
  simp [gapTable]

/-- Load-bearing strict 256-bit gap disjointness check `lo < x ∧ x < hi` (`#tooth` guarded!).
    Replacing `lo < x` with `lo ≤ x` allows a revoked `x = r_j` to pass! -/
@[expose] def checkStrictGap256 (lo x hi : BitVec 256) : Bool :=
  decide (lo < x) && decide (x < hi)

theorem checkStrictGap256_iff (lo x hi : BitVec 256) :
    checkStrictGap256 lo x hi = true ↔ lo < x ∧ x < hi := by
  simp [checkStrictGap256]

/-- Binary search computing `|{k < keys.size | keys[k] ≤ x}|` in `O(log |R_e|)` steps. -/
def upperBoundAux256 (keys : Array (BitVec 256)) (x : BitVec 256) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2
      if hm : mid < keys.size then
        if keys[mid] ≤ x then upperBoundAux256 keys x fuel (mid + 1) hi
        else upperBoundAux256 keys x fuel lo mid
      else lo
    else lo

theorem upperBoundAux256_inv (rs : RevokedSet256) (x : BitVec 256) :
    ∀ (fuel lo hi : Nat),
      lo ≤ hi → hi ≤ rs.keys.size → hi - lo < fuel →
      (∀ i (hi' : i < rs.keys.size), i < lo → rs.keys[i]'hi' ≤ x) →
      (∀ i (hi' : i < rs.keys.size), hi ≤ i → x < rs.keys[i]'hi') →
      let j := upperBoundAux256 rs.keys x fuel lo hi
      j ≤ rs.keys.size ∧
      (∀ i (hi' : i < rs.keys.size), i < j → rs.keys[i]'hi' ≤ x) ∧
      (∀ i (hi' : i < rs.keys.size), j ≤ i → x < rs.keys[i]'hi')
  | 0, lo, hi, _, _, hf, _, _ => by omega
  | fuel + 1, lo, hi, hle, hhi, hf, hL, hR => by
    if hlt : lo < hi then
      have hmid : lo + (hi - lo) / 2 < rs.keys.size := by omega
      simp only [upperBoundAux256, hlt, hmid, ↓reduceIte, ↓reduceDIte]
      if hmle : rs.keys[lo + (hi - lo) / 2] ≤ x then
        simp only [hmle, ↓reduceIte]
        refine upperBoundAux256_inv rs x fuel (lo + (hi - lo) / 2 + 1) hi
          (by omega) hhi (by omega) ?_ hR
        intro i hi' hilo
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hilo) with hilt | rfl
        · have h1 := BitVec.lt_def.1 (rs.sorted_getElem i _ hi' hmid hilt)
          have h2 := BitVec.le_def.1 hmle
          exact BitVec.le_def.2 (by omega)
        · exact hmle
      else
        simp only [hmle, ↓reduceIte]
        have hxlt : x < rs.keys[lo + (hi - lo) / 2] := by
          have hnle : ¬ (rs.keys[lo + (hi - lo) / 2].toNat ≤ x.toNat) :=
            fun h => hmle (BitVec.le_def.2 h)
          exact BitVec.lt_def.2 (by omega)
        refine upperBoundAux256_inv rs x fuel lo (lo + (hi - lo) / 2)
          (by omega) (by omega) (by omega) hL ?_
        intro i hi' hmi
        rcases Nat.lt_or_eq_of_le hmi with hmilt | rfl
        · have h1 := BitVec.lt_def.1 hxlt
          have h2 := BitVec.lt_def.1 (rs.sorted_getElem _ i hmid hi' hmilt)
          exact BitVec.lt_def.2 (by omega)
        · exact hxlt
    else
      have heq : lo = hi := by omega
      subst heq
      simp only [upperBoundAux256, Nat.lt_irrefl, ↓reduceIte]
      exact ⟨hhi, hL, hR⟩

/-- `O(log |R_e|)` binary search locating the unique sorted gap containing `x`. -/
def findGapIdxExec (rs : RevokedSet256) (x : BitVec 256) : Nat :=
  upperBoundAux256 rs.keys x (rs.keys.size + 1) 0 rs.keys.size

theorem strictGap_not_contains (rs : RevokedSet256) (x : BitVec 256) {j : Nat}
    (hj : j < rs.keys.size + 1)
    (hgap : checkStrictGap256 (boundedAt rs j) x (boundedAt rs (j + 1)) = true) :
    rs.contains x = false ∧ IsInteriorNullifier256 x := by
  obtain ⟨hlo, hhi⟩ := (checkStrictGap256_iff _ _ _).1 hgap
  have hminLe := boundedAt_mono rs (Nat.zero_le j) (by omega)
  have hmaxGe := boundedAt_mono rs (show j + 1 ≤ rs.keys.size + 1 by omega) (Nat.le_refl _)
  rw [boundedAt_zero] at hminLe
  rw [boundedAt_last] at hmaxGe
  have hInt : IsInteriorNullifier256 x := ⟨
    BitVec.lt_def.2 (Nat.lt_of_le_of_lt (BitVec.le_def.1 hminLe) (BitVec.lt_def.1 hlo)),
    BitVec.lt_def.2 (Nat.lt_of_lt_of_le (BitVec.lt_def.1 hhi) (BitVec.le_def.1 hmaxGe))⟩
  refine ⟨?_, hInt⟩
  cases hc : rs.contains x with
  | false => rfl
  | true =>
    obtain ⟨k, hkL, hkx⟩ := List.mem_iff_getElem.1 ((rs.contains_iff x).1 hc)
    have hk : k < rs.keys.size := by simpa using hkL
    have hbk : boundedAt rs (k + 1) = x := by
      rw [boundedAt_succ_lt rs k hk]
      simpa using hkx
    if hkj : k + 1 ≤ j then
      have hle := BitVec.le_def.1 (boundedAt_mono rs hkj (by omega))
      rw [hbk] at hle
      have hlon := BitVec.lt_def.1 hlo
      omega
    else
      have hjk : j + 1 ≤ k + 1 := by omega
      have hle := BitVec.le_def.1 (boundedAt_mono rs hjk (by omega))
      rw [hbk] at hle
      have hhin := BitVec.lt_def.1 hhi
      omega

theorem strictGap_unique (rs : RevokedSet256) (x : BitVec 256) {j₁ j₂ : Nat}
    (hj₁ : j₁ < rs.keys.size + 1) (hj₂ : j₂ < rs.keys.size + 1)
    (hg₁ : checkStrictGap256 (boundedAt rs j₁) x (boundedAt rs (j₁ + 1)) = true)
    (hg₂ : checkStrictGap256 (boundedAt rs j₂) x (boundedAt rs (j₂ + 1)) = true) :
    j₁ = j₂ := by
  obtain ⟨hlo₁, hhi₁⟩ := (checkStrictGap256_iff _ _ _).1 hg₁
  obtain ⟨hlo₂, hhi₂⟩ := (checkStrictGap256_iff _ _ _).1 hg₂
  rcases Nat.lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · have hle := BitVec.le_def.1 (boundedAt_mono rs (show j₁ + 1 ≤ j₂ by omega) (by omega))
    have a := BitVec.lt_def.1 hhi₁
    have b := BitVec.lt_def.1 hlo₂
    omega
  · exact heq
  · have hle := BitVec.le_def.1 (boundedAt_mono rs (show j₂ + 1 ≤ j₁ by omega) (by omega))
    have a := BitVec.lt_def.1 hhi₂
    have b := BitVec.lt_def.1 hlo₁
    omega

theorem findGapIdxExec_spec (rs : RevokedSet256) (x : BitVec 256)
    (hx : IsInteriorNullifier256 x) (hNotMem : rs.contains x = false) :
    findGapIdxExec rs x < rs.keys.size + 1 ∧
    checkStrictGap256 (boundedAt rs (findGapIdxExec rs x)) x
      (boundedAt rs (findGapIdxExec rs x + 1)) = true := by
  obtain ⟨hjLe, hLeft, hRight⟩ := upperBoundAux256_inv rs x (rs.keys.size + 1) 0 rs.keys.size
    (Nat.zero_le _) (Nat.le_refl _) (by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega)
  change findGapIdxExec rs x ≤ rs.keys.size at hjLe
  change ∀ i (hi' : i < rs.keys.size), i < findGapIdxExec rs x → rs.keys[i]'hi' ≤ x at hLeft
  change ∀ i (hi' : i < rs.keys.size), findGapIdxExec rs x ≤ i → x < rs.keys[i]'hi' at hRight
  refine ⟨by omega, (checkStrictGap256_iff _ _ _).2 ⟨?_, ?_⟩⟩
  · cases hj0 : findGapIdxExec rs x with
    | zero => rw [boundedAt_zero]; exact hx.1
    | succ k =>
      have hk : k < rs.keys.size := by omega
      rw [boundedAt_succ_lt rs k hk]
      have hle := hLeft k hk (by omega)
      have hne : rs.keys[k]'hk ≠ x := by
        intro heq
        have hmem : x ∈ rs.keys.toList := heq ▸ Array.getElem_mem_toList hk
        have hc := (rs.contains_iff x).2 hmem
        rw [hNotMem] at hc; cases hc
      have hneNat : (rs.keys[k]'hk).toNat ≠ x.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
      have hleNat := BitVec.le_def.1 hle
      exact BitVec.lt_def.2 (by omega)
  · if hjSz : findGapIdxExec rs x < rs.keys.size then
      rw [boundedAt_succ_lt rs (findGapIdxExec rs x) hjSz]
      exact hRight (findGapIdxExec rs x) hjSz (Nat.le_refl _)
    else
      have hjEq : findGapIdxExec rs x = rs.keys.size := by omega
      rw [hjEq, boundedAt_last]
      exact hx.2

/-- Unique gap membership predicate `∃! j, r_j < x < r_{j+1}` over `gapTable rs`. -/
@[expose] def ExistsUniqueGap (rs : RevokedSet256) (x : BitVec 256) : Prop :=
  ∃ j : Fin (rs.keys.size + 1),
    checkStrictGap256 (gapEntryAt rs j.val).lo x (gapEntryAt rs j.val).hi = true ∧
    ∀ j' : Fin (rs.keys.size + 1),
      checkStrictGap256 (gapEntryAt rs j'.val).lo x (gapEntryAt rs j'.val).hi = true → j' = j

/-- **Gap-Disjointness Equivalence (`not_mem_revoked_iff_in_unique_gap`)**:
    For every interior 256-bit nullifier `x` (`0 < x < 2^256 - 1`), `x ∉ R_e` holds
    **if and only if** `x` lies strictly inside a unique sorted gap `(r_j, r_{j+1})` of `G_e`. -/
theorem not_mem_revoked_iff_in_unique_gap (rs : RevokedSet256) (x : BitVec 256)
    (hx : IsInteriorNullifier256 x) :
    rs.contains x = false ↔ ExistsUniqueGap rs x := by
  constructor
  · intro hNot
    obtain ⟨hj, hgap⟩ := findGapIdxExec_spec rs x hx hNot
    refine ⟨⟨findGapIdxExec rs x, hj⟩, hgap, ?_⟩
    intro j' hj'
    apply Fin.ext
    exact strictGap_unique rs x j'.isLt hj hj' hgap
  · rintro ⟨j, hj, _⟩
    exact (strictGap_not_contains rs x j.isLt hj).1

/-! ### Power-of-Two Tree Depth, Epoch-Framed `RevokedGapRoot256` & `PinnedCollision` Extraction -/

def pow2CoverAux (target : Nat) : Nat → Nat → Nat
  | 0, exp => exp
  | fuel + 1, exp => if target ≤ 2 ^ exp then exp else pow2CoverAux target fuel (exp + 1)

theorem pow2CoverAux_spec (target : Nat) :
    ∀ (fuel exp : Nat), target ≤ 2 ^ (exp + fuel) → target ≤ 2 ^ pow2CoverAux target fuel exp
  | 0, exp, h => by simpa [pow2CoverAux] using h
  | fuel + 1, exp, h => by
    simp only [pow2CoverAux]
    split
    · assumption
    · exact pow2CoverAux_spec target fuel (exp + 1)
        (by rw [show exp + 1 + fuel = exp + (fuel + 1) by omega]; exact h)

/-- Ceiling `⌈log₂ n⌉` satisfying `n ≤ 2 ^ nextPow2Exp n`. -/
def nextPow2Exp (n : Nat) : Nat := pow2CoverAux n n 0

theorem le_two_pow_nextPow2Exp (n : Nat) : n ≤ 2 ^ nextPow2Exp n := by
  exact pow2CoverAux_spec n n 0 (by simp; exact Nat.le_of_lt Nat.lt_two_pow_self)

/-- Domain-separated, epoch-framed gap leaf preimage
    `0x20 ‖ len(leb128 epoch) ‖ leb128(epoch) ‖ leb128(idx) ‖ be32(lo) ‖ be32(hi)`. -/
def gapLeafPreimage (epoch idx : Nat) (lo hi : BitVec 256) : List UInt8 :=
  (0x20 : UInt8) ::
    (encodeListField (leb128 epoch) ++ (leb128 idx ++ (be 32 lo.toNat ++ be 32 hi.toNat)))

def padGapLeafPreimage (epoch idx : Nat) : List UInt8 :=
  (0x21 : UInt8) :: (encodeListField (leb128 epoch) ++ leb128 idx)

theorem gapLeafPreimage_injective {e₁ i₁ e₂ i₂ : Nat} {lo₁ hi₁ lo₂ hi₂ : BitVec 256}
    (h : gapLeafPreimage e₁ i₁ lo₁ hi₁ = gapLeafPreimage e₂ i₂ lo₂ hi₂) :
    e₁ = e₂ ∧ i₁ = i₂ ∧ lo₁ = lo₂ ∧ hi₁ = hi₂ := by
  simp only [gapLeafPreimage, List.cons.injEq] at h
  obtain ⟨heL, hrest₁⟩ := encodeListField_prefix_inj h.2
  obtain ⟨hi, hrest₂⟩ := leb128_prefix_inj hrest₁
  obtain ⟨hlo, hhi⟩ := List.append_inj hrest₂ (by simp [length_be])
  have he : e₁ = e₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using heL)).1
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact ⟨he, hi,
    BitVec.eq_of_toNat_eq (be_injective (hpow ▸ lo₁.isLt) (hpow ▸ lo₂.isLt) hlo),
    BitVec.eq_of_toNat_eq (be_injective (hpow ▸ hi₁.isLt) (hpow ▸ hi₂.isLt) hhi)⟩

def hashGapLeaf (H : Hash32) (epoch idx : Nat) (lo hi : BitVec 256) : Digest32 :=
  evalDigest32 H (gapLeafPreimage epoch idx lo hi)

def hashPadGapLeaf (H : Hash32) (epoch idx : Nat) : Digest32 :=
  evalDigest32 H (padGapLeafPreimage epoch idx)

def buildGapLeaves (H : Hash32) (epoch : Nat) (rs : RevokedSet256) : List Digest32 :=
  let numGaps := rs.keys.size + 1
  let d := nextPow2Exp numGaps
  (List.range (2 ^ d)).map fun idx =>
    if idx < numGaps then
      let g := gapEntryAt rs idx
      hashGapLeaf H epoch idx g.lo g.hi
    else
      hashPadGapLeaf H epoch idx

theorem buildGapLeaves_length (H : Hash32) (epoch : Nat) (rs : RevokedSet256) :
    (buildGapLeaves H epoch rs).length = 2 ^ nextPow2Exp (rs.keys.size + 1) := by
  simp [buildGapLeaves]

/-- Commitment to epoch `e`'s Authenticated Sorted-Gap Table `G_e`. -/
structure RevokedGapRoot256 where
  epoch : Nat
  numGaps : Nat
  treeDepth : Nat
  merkleRoot : Digest32
  deriving DecidableEq

instance : LawfulTranscriptEncode RevokedGapRoot256 where
  encodeTranscriptBytes r :=
    TranscriptEncode.encodeTranscriptBytes (r.epoch, (r.numGaps, (r.treeDepth, r.merkleRoot)))
  encodeTranscriptBytes_injective {r₁ r₂} h := by
    have hp := LawfulTranscriptEncode.encodeTranscriptBytes_injective
      (ι := Nat × (Nat × (Nat × Digest32))) h
    cases r₁; cases r₂; simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- Commit `(epoch, RevokedSet256)` into its Authenticated Sorted-Gap root `RevokedGapRoot256`. -/
def RevokedSet256.gapRoot (H : Hash32) (epoch : Nat) (rs : RevokedSet256) : RevokedGapRoot256 where
  epoch := epoch
  numGaps := rs.keys.size + 1
  treeDepth := nextPow2Exp (rs.keys.size + 1)
  merkleRoot := merkleRoot32 H (buildGapLeaves H epoch rs)

/-- Per-slot `O(log |R_e|)` sorted-gap authentication witness. -/
structure GapSlotOpening256 where
  gapIdx : Nat
  lo : BitVec 256
  hi : BitVec 256
  merklePath : List Digest32
  deriving DecidableEq

/-- Generate the `O(log |R_e|)` sorted-gap opening for `x` at `epoch` via binary search + Merkle path. -/
def openGapForNullifier (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (x : BitVec 256) : GapSlotOpening256 :=
  let j := findGapIdxExec rs x
  let g := gapEntryAt rs j
  ⟨j, g.lo, g.hi, merklePath32 H (buildGapLeaves H epoch rs) j⟩

/-- Verify one slot's sorted-gap opening against `RevokedGapRoot256` in `O(log |R_e|)` hashes. -/
def verifyGapSlotOpening (H : Hash32) (root : RevokedGapRoot256)
    (x : BitVec 256) (prf : GapSlotOpening256) : Bool :=
  decide (prf.gapIdx < root.numGaps) &&
  decide (root.numGaps ≤ 2 ^ root.treeDepth) &&
  checkStrictGap256 prf.lo x prf.hi &&
  (climbMerkle32 H (2 ^ root.treeDepth) prf.gapIdx
    (hashGapLeaf H root.epoch prf.gapIdx prf.lo prf.hi) prf.merklePath == some root.merkleRoot)

theorem verifyGapSlotOpening_complete (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (x : BitVec 256) (hx : IsInteriorNullifier256 x) (hNot : rs.contains x = false) :
    verifyGapSlotOpening H (rs.gapRoot H epoch) x (openGapForNullifier H epoch rs x) = true := by
  obtain ⟨hj, hgap⟩ := findGapIdxExec_spec rs x hx hNot
  have hcov := le_two_pow_nextPow2Exp (rs.keys.size + 1)
  have hjPow : findGapIdxExec rs x < 2 ^ nextPow2Exp (rs.keys.size + 1) :=
    Nat.lt_of_lt_of_le hj hcov
  have hjLen : findGapIdxExec rs x < (buildGapLeaves H epoch rs).length := by
    rw [buildGapLeaves_length]; exact hjPow
  have hClimb := climbMerkle32_merklePath32 H (buildGapLeaves H epoch rs) (findGapIdxExec rs x) hjLen
  rw [buildGapLeaves_length] at hClimb
  have hLeafEq : (buildGapLeaves H epoch rs)[findGapIdxExec rs x]'hjLen =
      hashGapLeaf H epoch (findGapIdxExec rs x)
        (gapEntryAt rs (findGapIdxExec rs x)).lo (gapEntryAt rs (findGapIdxExec rs x)).hi := by
    simp [buildGapLeaves, hj]
  rw [hLeafEq] at hClimb
  simp only [verifyGapSlotOpening, RevokedSet256.gapRoot, openGapForNullifier,
    Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨decide_eq_true hj, decide_eq_true hcov⟩, hgap⟩, hClimb⟩

/-- Internal node preimages hashed along a Merkle climb. -/
def climbMerkleFrames (H : Hash32) : (n idx : Nat) → Digest32 → List Digest32 → List (List UInt8)
  | _, _, _, [] => []
  | n, idx, leaf, sib :: rest =>
    if n < 2 || idx ≥ n then []
    else if idx < n / 2 then
      match climbMerkle32 H (n / 2) idx leaf rest with
      | none => []
      | some l => merkleNodePreimage l sib :: climbMerkleFrames H (n / 2) idx leaf rest
    else
      match climbMerkle32 H (n - n / 2) (idx - n / 2) leaf rest with
      | none => []
      | some r => merkleNodePreimage sib r :: climbMerkleFrames H (n - n / 2) (idx - n / 2) leaf rest

/-- Monotone domain transport for `PinnedCollision` (`0 Classical`). -/
def liftPinnedCollision {H : Hash} {d₁ d₂ : List (List UInt8)}
    (hSub : ∀ m, m ∈ d₁ → m ∈ d₂) (w : PinnedCollision H d₁) : PinnedCollision H d₂ where
  msgA := w.msgA
  msgB := w.msgB
  memA := hSub w.msgA w.memA
  memB := hSub w.msgB w.memB
  distinct := w.distinct
  sameDigest := w.sameDigest

/-- Constructive `0 Classical` Merkle-climb collision extractor into `PinnedCollision` over
    `climbMerkleFrames` (zero Pigeonhole-vacuous byte-length bounds). -/
def extractClimbPinnedCollision (H : Hash32) :
    ∀ (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32),
      leaf₁ ≠ leaf₂ →
      climbMerkle32 H n idx leaf₁ p₁ = some root →
      climbMerkle32 H n idx leaf₂ p₂ = some root →
      PinnedCollision H.eval
        (climbMerkleFrames H n idx leaf₁ p₁ ++ climbMerkleFrames H n idx leaf₂ p₂)
  | [], [], n, idx, leaf₁, leaf₂, _, hNe, h₁, h₂ =>
    False.elim (by
      simp only [climbMerkle32] at h₁ h₂
      split at h₁
      · rename_i hc
        simp only [hc, ↓reduceIte, Option.some.injEq] at h₁ h₂
        exact hNe (h₁.trans h₂.symm)
      · cases h₁)
  | [], _ :: _, n, idx, _, _, _, _, h₁, h₂ =>
    False.elim (by
      simp only [climbMerkle32] at h₁ h₂
      split at h₁
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        rcases hc with ⟨rfl, _⟩
        simp at h₂
      · cases h₁)
  | _ :: _, [], n, idx, _, _, _, _, h₁, h₂ =>
    False.elim (by
      simp only [climbMerkle32] at h₁ h₂
      split at h₂
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        rcases hc with ⟨rfl, _⟩
        simp at h₁
      · cases h₂)
  | s₁ :: ss₁, s₂ :: ss₂, n, idx, leaf₁, leaf₂, root, hNe, h₁, h₂ =>
    if hBad : (decide (n < 2) || decide (idx ≥ n)) = true then
      False.elim (by simp [climbMerkle32, hBad] at h₁)
    else
      have hBadF : (decide (n < 2) || decide (idx ≥ n)) = false := Bool.eq_false_iff.2 hBad
      if hi : idx < n / 2 then
        match hc₁ : climbMerkle32 H (n / 2) idx leaf₁ ss₁,
              hc₂ : climbMerkle32 H (n / 2) idx leaf₂ ss₂ with
        | none, _ => False.elim (by simp [climbMerkle32, hBadF, hi, hc₁] at h₁)
        | _, none => False.elim (by simp [climbMerkle32, hBadF, hi, hc₂] at h₂)
        | some l₁, some l₂ =>
          have hNodeEq : hashNode32 H l₁ s₁ = hashNode32 H l₂ s₂ := by
            simp only [climbMerkle32, hBadF, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
              Option.map_some, Option.some.injEq] at h₁ h₂
            exact h₁.trans h₂.symm
          if hEqL : l₁ = l₂ then
            let sub := extractClimbPinnedCollision H ss₁ ss₂ (n / 2) idx leaf₁ leaf₂ l₁
              hNe hc₁ (hEqL ▸ hc₂)
            liftPinnedCollision (fun m hm => by
              simp only [climbMerkleFrames, hBadF, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
                List.cons_append, List.mem_cons, List.mem_append] at hm ⊢
              rcases hm with hmL | hmR
              · exact .inr (.inl hmL)
              · exact .inr (.inr (.inr hmR))) sub
          else
            { msgA := merkleNodePreimage l₁ s₁
              msgB := merkleNodePreimage l₂ s₂
              memA := by simp [climbMerkleFrames, hBadF, hi, hc₁]
              memB := by simp [climbMerkleFrames, hBadF, hi, hc₁, hc₂]
              distinct := fun hpre => hEqL (merkleNodePreimage_injective hpre).1
              sameDigest := by
                have hl := congrArg (fun d => d.bytes.data.toList) hNodeEq
                simp only [hashNode32, evalDigest32, Native.bytesOfList_toList] at hl
                exact congrArg ofBE hl }
      else
        match hc₁ : climbMerkle32 H (n - n / 2) (idx - n / 2) leaf₁ ss₁,
              hc₂ : climbMerkle32 H (n - n / 2) (idx - n / 2) leaf₂ ss₂ with
        | none, _ => False.elim (by simp [climbMerkle32, hBadF, hi, hc₁] at h₁)
        | _, none => False.elim (by simp [climbMerkle32, hBadF, hi, hc₂] at h₂)
        | some r₁, some r₂ =>
          have hNodeEq : hashNode32 H s₁ r₁ = hashNode32 H s₂ r₂ := by
            simp only [climbMerkle32, hBadF, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
              Option.map_some, Option.some.injEq] at h₁ h₂
            exact h₁.trans h₂.symm
          if hEqR : r₁ = r₂ then
            let sub := extractClimbPinnedCollision H ss₁ ss₂ (n - n / 2) (idx - n / 2)
              leaf₁ leaf₂ r₁ hNe hc₁ (hEqR ▸ hc₂)
            liftPinnedCollision (fun m hm => by
              simp only [climbMerkleFrames, hBadF, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
                List.cons_append, List.mem_cons, List.mem_append] at hm ⊢
              rcases hm with hmL | hmR
              · exact .inr (.inl hmL)
              · exact .inr (.inr (.inr hmR))) sub
          else
            { msgA := merkleNodePreimage s₁ r₁
              msgB := merkleNodePreimage s₂ r₂
              memA := by simp [climbMerkleFrames, hBadF, hi, hc₁]
              memB := by simp [climbMerkleFrames, hBadF, hi, hc₁, hc₂]
              distinct := fun hpre => hEqR (merkleNodePreimage_injective hpre).2
              sameDigest := by
                have hl := congrArg (fun d => d.bytes.data.toList) hNodeEq
                simp only [hashNode32, evalDigest32, Native.bytesOfList_toList] at hl
                exact congrArg ofBE hl }

/-- Finite list of discrepant Merkle leaf & path preimages queried when `prf`'s `(lo, hi)` differs
    from the canonical `gapEntryAt rs prf.gapIdx` (`[]` on every honest opening!). -/
def slotDiscrepancyFrames (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (prf : GapSlotOpening256) : List (List UInt8) :=
  let honestGap := gapEntryAt rs prf.gapIdx
  if prf.lo == honestGap.lo && prf.hi == honestGap.hi then
    []
  else
    let d := nextPow2Exp (rs.keys.size + 1)
    let cheatLeaf := hashGapLeaf H epoch prf.gapIdx prf.lo prf.hi
    let honestLeaf := hashGapLeaf H epoch prf.gapIdx honestGap.lo honestGap.hi
    gapLeafPreimage epoch prf.gapIdx prf.lo prf.hi ::
    gapLeafPreimage epoch prf.gapIdx honestGap.lo honestGap.hi ::
    (climbMerkleFrames H (2 ^ d) prf.gapIdx cheatLeaf prf.merklePath ++
     climbMerkleFrames H (2 ^ d) prf.gapIdx honestLeaf
       (merklePath32 H (buildGapLeaves H epoch rs) prf.gapIdx))

/-- Discrepant Merkle preimage frames across all gap slot openings in a certificate. -/
def allGapSlotFrames (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (openings : Array GapSlotOpening256) : List (List UInt8) :=
  openings.toList.flatMap (slotDiscrepancyFrames H epoch rs)

theorem slotDiscrepancyFrames_openGapForNullifier (H : Hash32) (epoch : Nat)
    (rs : RevokedSet256) (x : BitVec 256) :
    slotDiscrepancyFrames H epoch rs (openGapForNullifier H epoch rs x) = [] := by
  simp [slotDiscrepancyFrames, openGapForNullifier]

private theorem allGapSlotFrames_honest_aux (H : Hash32) (epoch : Nat) (rs : RevokedSet256) :
    ∀ (xs : List (BitVec 256)),
      (xs.map (openGapForNullifier H epoch rs)).flatMap (slotDiscrepancyFrames H epoch rs) = []
  | [] => rfl
  | x :: rest => by
    simp [slotDiscrepancyFrames_openGapForNullifier, allGapSlotFrames_honest_aux H epoch rs rest]

theorem allGapSlotFrames_honest_nil (H : Hash32) (epoch : Nat)
    (rs : RevokedSet256) (nuls : Array (BitVec 256)) :
    allGapSlotFrames H epoch rs (nuls.map (openGapForNullifier H epoch rs)) = [] := by
  unfold allGapSlotFrames
  rw [Array.toList_map]
  exact allGapSlotFrames_honest_aux H epoch rs nuls.toList

/-- Constructive `0 Classical` single-slot gap extractor: an accepted `GapSlotOpening256` against
    `rs.gapRoot H epoch` either proves `rs.contains x = false ∧ IsInteriorNullifier256 x` or
    extracts a `PinnedCollision` on `H.eval` within `slotDiscrepancyFrames`. -/
def extractGapSlotOpeningOrLive (H : Hash32) (epoch : Nat) (rs : RevokedSet256) (x : BitVec 256)
    (prf : GapSlotOpening256)
    (hVer : verifyGapSlotOpening H (rs.gapRoot H epoch) x prf = true) :
    PSum (PLift (rs.contains x = false ∧ IsInteriorNullifier256 x))
      (PinnedCollision H.eval (slotDiscrepancyFrames H epoch rs prf)) :=
  let d := nextPow2Exp (rs.keys.size + 1)
  have hParts : prf.gapIdx < rs.keys.size + 1 ∧
      rs.keys.size + 1 ≤ 2 ^ d ∧
      checkStrictGap256 prf.lo x prf.hi = true ∧
      climbMerkle32 H (2 ^ d) prf.gapIdx
        (hashGapLeaf H epoch prf.gapIdx prf.lo prf.hi) prf.merklePath =
          some (rs.gapRoot H epoch).merkleRoot := by
    dsimp only [verifyGapSlotOpening, RevokedSet256.gapRoot, d] at hVer ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hVer
    exact ⟨of_decide_eq_true hVer.1.1.1, of_decide_eq_true hVer.1.1.2, hVer.1.2, hVer.2⟩
  let honestGap := gapEntryAt rs prf.gapIdx
  match hEqB : (prf.lo == honestGap.lo && prf.hi == honestGap.hi) with
  | true =>
    .inl ⟨strictGap_not_contains rs x hParts.1 (by
      have hEq : prf.lo = honestGap.lo ∧ prf.hi = honestGap.hi := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hEqB
      have hlo := hEq.1; have hhi := hEq.2
      dsimp only [honestGap, gapEntryAt] at hlo hhi
      rw [← hlo, ← hhi]; exact hParts.2.2.1)⟩
  | false =>
    let cheatLeaf := hashGapLeaf H epoch prf.gapIdx prf.lo prf.hi
    let honestLeaf := hashGapLeaf H epoch prf.gapIdx honestGap.lo honestGap.hi
    have hNeGap : ¬ (prf.lo = honestGap.lo ∧ prf.hi = honestGap.hi) := fun ⟨h1, h2⟩ => by
      have ht : (prf.lo == honestGap.lo && prf.hi == honestGap.hi) = true := by simp [h1, h2]
      rw [hEqB] at ht; cases ht
    have hFramesEq : slotDiscrepancyFrames H epoch rs prf =
        gapLeafPreimage epoch prf.gapIdx prf.lo prf.hi ::
        gapLeafPreimage epoch prf.gapIdx honestGap.lo honestGap.hi ::
        (climbMerkleFrames H (2 ^ d) prf.gapIdx cheatLeaf prf.merklePath ++
         climbMerkleFrames H (2 ^ d) prf.gapIdx honestLeaf
           (merklePath32 H (buildGapLeaves H epoch rs) prf.gapIdx)) := by
      unfold slotDiscrepancyFrames
      dsimp only
      change (if (prf.lo == honestGap.lo && prf.hi == honestGap.hi) = true then [] else _) = _
      rw [hEqB]
      rfl
    if hEqLeaf : cheatLeaf = honestLeaf then
      .inr {
        msgA := gapLeafPreimage epoch prf.gapIdx prf.lo prf.hi
        msgB := gapLeafPreimage epoch prf.gapIdx honestGap.lo honestGap.hi
        memA := by rw [hFramesEq]; exact .head _
        memB := by rw [hFramesEq]; exact .tail _ (.head _)
        distinct := fun hpre => by
          obtain ⟨_, _, hlo, hhi⟩ := gapLeafPreimage_injective hpre
          exact hNeGap ⟨hlo, hhi⟩
        sameDigest := by
          have hl := congrArg (fun d => d.bytes.data.toList) hEqLeaf
          simp only [cheatLeaf, honestLeaf, hashGapLeaf, evalDigest32,
            Native.bytesOfList_toList] at hl
          exact congrArg ofBE hl
      }
    else
      have hIdxPow : prf.gapIdx < 2 ^ d := Nat.lt_of_lt_of_le hParts.1 hParts.2.1
      have hIdxLen : prf.gapIdx < (buildGapLeaves H epoch rs).length := by
        rw [buildGapLeaves_length]; exact hIdxPow
      have hHonestClimb :
          climbMerkle32 H (2 ^ d) prf.gapIdx honestLeaf
            (merklePath32 H (buildGapLeaves H epoch rs) prf.gapIdx) =
              some (rs.gapRoot H epoch).merkleRoot := by
        have hc := climbMerkle32_merklePath32 H (buildGapLeaves H epoch rs) prf.gapIdx hIdxLen
        rw [buildGapLeaves_length] at hc
        have hl : (buildGapLeaves H epoch rs)[prf.gapIdx]'hIdxLen = honestLeaf := by
          simp [buildGapLeaves, hParts.1, honestLeaf, honestGap]
        rw [hl] at hc
        exact hc
      let sub := extractClimbPinnedCollision H prf.merklePath
        (merklePath32 H (buildGapLeaves H epoch rs) prf.gapIdx)
        (2 ^ d) prf.gapIdx cheatLeaf honestLeaf (rs.gapRoot H epoch).merkleRoot
        hEqLeaf hParts.2.2.2 hHonestClimb
      .inr (liftPinnedCollision (fun m hm => by
        rw [hFramesEq]
        exact .tail _ (.tail _ hm)) sub)

/-! ## 3. Phase 1 — Residual Caveat Reduction, PQ Hop Signatures & Epoch-Free Folding -/

/-- Partially evaluated caveat retaining only unresolved presentation-time context holes. -/
abbrev ResidualCaveat := Caveat

def pevalNot : Caveat → Caveat
  | .const b => .const (!b)
  | .not inner => inner
  | ra => .not ra

def pevalAnd : Caveat → Caveat → Caveat
  | .const false, _ => .const false
  | .const true, rb => rb
  | _, .const false => .const false
  | ra, .const true => ra
  | ra, rb => .and ra rb

def pevalOr : Caveat → Caveat → Caveat
  | .const true, _ => .const true
  | .const false, rb => rb
  | _, .const true => .const true
  | ra, .const false => ra
  | ra, rb => .or ra rb

/-- Strong-Kleene-exact offline partial evaluation of caveats against `staticEnv`. -/
def pevalCaveat (staticEnv : Nat → KleenePred3) : Caveat → ResidualCaveat
  | .atom v =>
    match staticEnv v with
    | .true3 => .const true
    | .false3 => .const false
    | .unbound3 => .atom v
  | .const b => .const b
  | .not a => pevalNot (pevalCaveat staticEnv a)
  | .and a b => pevalAnd (pevalCaveat staticEnv a) (pevalCaveat staticEnv b)
  | .or a b => pevalOr (pevalCaveat staticEnv a) (pevalCaveat staticEnv b)

/-- Remaining unresolved context-variable indices in a `ResidualCaveat`. -/
def residualHoles : ResidualCaveat → List Nat
  | .atom v => [v]
  | .const _ => []
  | .not a => residualHoles a
  | .and a b => residualHoles a ++ residualHoles b
  | .or a b => residualHoles a ++ residualHoles b

private theorem pevalNot_eval (env : Nat → KleenePred3) (r : Caveat) :
    (pevalNot r).eval env = (r.eval env).not3 := by
  cases r with
  | const b => cases b <;> rfl
  | not inner =>
    simp only [pevalNot, Caveat.eval]
    cases inner.eval env <;> rfl
  | atom _ | and _ _ | or _ _ => rfl

private theorem kleene_and3_false_right (p : KleenePred3) : p.and3 .false3 = .false3 := by
  cases p <;> rfl

private theorem kleene_and3_true_right (p : KleenePred3) : p.and3 .true3 = p := by
  cases p <;> rfl

private theorem kleene_or3_true_right (p : KleenePred3) : p.or3 .true3 = .true3 := by
  cases p <;> rfl

private theorem kleene_or3_false_right (p : KleenePred3) : p.or3 .false3 = p := by
  cases p <;> rfl

private theorem pevalAnd_eval (env : Nat → KleenePred3) (r₁ r₂ : Caveat) :
    (pevalAnd r₁ r₂).eval env = (r₁.eval env).and3 (r₂.eval env) := by
  cases r₁ with
  | const b₁ =>
    cases b₁
    · rfl
    · simp only [pevalAnd, Caveat.eval, ↓reduceIte]
      cases r₂.eval env <;> rfl
  | atom _ | and _ _ | or _ _ | not _ =>
    cases r₂ with
    | const b₂ =>
      cases b₂
      · exact (kleene_and3_false_right _).symm
      · exact (kleene_and3_true_right _).symm
    | atom _ | and _ _ | or _ _ | not _ => rfl

private theorem pevalOr_eval (env : Nat → KleenePred3) (r₁ r₂ : Caveat) :
    (pevalOr r₁ r₂).eval env = (r₁.eval env).or3 (r₂.eval env) := by
  cases r₁ with
  | const b₁ =>
    cases b₁
    · simp only [pevalOr, Caveat.eval]
      cases r₂.eval env <;> rfl
    · rfl
  | atom _ | and _ _ | or _ _ | not _ =>
    cases r₂ with
    | const b₂ =>
      cases b₂
      · exact (kleene_or3_false_right _).symm
      · exact (kleene_or3_true_right _).symm
    | atom _ | and _ _ | or _ _ | not _ => rfl

/-- Offline partial evaluation preserves exact strong-Kleene semantics under any refining `liveEnv`. -/
theorem pevalCaveat_eval_eq {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v)) :
    ∀ (c : Caveat), (pevalCaveat staticEnv c).eval liveEnv = c.eval liveEnv
  | .atom v => by
    have hv := hRef v
    unfold KleenePred3.Refines at hv
    unfold pevalCaveat
    cases hs : staticEnv v
    · rw [hs] at hv
      rcases hv with h | h
      · cases h
      · dsimp only [Caveat.eval]; rw [← h]; rfl
    · rw [hs] at hv
      rcases hv with h | h
      · cases h
      · dsimp only [Caveat.eval]; rw [← h]; rfl
    · rfl
  | .const b => by rfl
  | .not a => by
    simp only [pevalCaveat, pevalNot_eval, pevalCaveat_eval_eq hRef a, Caveat.eval]
  | .and a b => by
    simp only [pevalCaveat, pevalAnd_eval, pevalCaveat_eval_eq hRef a,
      pevalCaveat_eval_eq hRef b, Caveat.eval]
  | .or a b => by
    simp only [pevalCaveat, pevalOr_eval, pevalCaveat_eval_eq hRef a,
      pevalCaveat_eval_eq hRef b, Caveat.eval]

def conjoinResidual (staticEnv : Nat → KleenePred3) (r₁ r₂ : ResidualCaveat) : ResidualCaveat :=
  pevalCaveat staticEnv (.and r₁ r₂)

theorem conjoinResidual_eval_eq {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (r₁ r₂ : ResidualCaveat) :
    (conjoinResidual staticEnv r₁ r₂).eval liveEnv =
      KleenePred3.and3 (r₁.eval liveEnv) (r₂.eval liveEnv) := by
  unfold conjoinResidual
  rw [pevalCaveat_eval_eq hRef (.and r₁ r₂)]
  rfl

/-- Purely context-free offline environment leaving all context variables as residual holes. -/
def emptyStaticEnv : Nat → KleenePred3 := fun _ => .unbound3

theorem emptyStaticEnv_refines (liveEnv : Nat → KleenePred3) (v : Nat) :
    KleenePred3.Refines (emptyStaticEnv v) (liveEnv v) := by
  exact .inl rfl

/-! ### Post-Quantum Delegation Hop Signatures (`HopSigScheme` & `pqLamport256HopSig`) -/

/-- Polymorphic delegation hop signature interface authenticating `Block.holder` transitions. -/
structure HopSigScheme where
  SecretKey : Type
  Sig : Type
  pkOf : SecretKey → ByteArray
  sign : SecretKey → List UInt8 → Sig
  verify : ByteArray → List UInt8 → Sig → Bool
  sign_complete : ∀ sk msg, verify (pkOf sk) msg (sign sk msg) = true

def hopMsgCustomization : List UInt8 := "OBEND.CAPFOLD.HOP_MSG/v1".toUTF8.data.toList
def hopLeafCustomization : List UInt8 := "OBEND.CAPFOLD.HOP_LEAF/v1".toUTF8.data.toList
def hopPkCustomization : List UInt8 := "OBEND.CAPFOLD.HOP_PK/v1".toUTF8.data.toList

def hopMsgDigest256 (msg : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes hopMsgCustomization msg))

def hopLamportLeaf (bitIdx : Nat) (bitVal : Bool) (pre : Digest32) : Digest32 :=
  evalDigest32 { eval := cshake256Bytes hopLeafCustomization,
                 len_eq := cshake256Bytes_length hopLeafCustomization }
    ((if bitVal then 1 else 0) :: (leb128 bitIdx ++ pre.bytes.data.toList))

attribute [local irreducible] hopLamportLeaf

def encodeLamportPairs (pairs : List (Digest32 × Digest32)) : List UInt8 :=
  pairs.flatMap fun p => p.1.bytes.data.toList ++ p.2.bytes.data.toList

private def lamportPubPairAt (sk : Nat → Digest32 × Digest32) (i : Nat) : Digest32 × Digest32 :=
  (hopLamportLeaf i false (sk i).1, hopLamportLeaf i true (sk i).2)

private def lamportSignAt (d : BitVec 256) (sk : Nat → Digest32 × Digest32) (i : Nat) :
    Digest32 × Digest32 :=
  if d.getLsbD i then
    (hopLamportLeaf i false (sk i).1, (sk i).2)
  else
    ((sk i).1, hopLamportLeaf i true (sk i).2)

private def lamportRecPairAt (d : BitVec 256) (sig : Nat → Digest32 × Digest32) (i : Nat) :
    Digest32 × Digest32 :=
  if d.getLsbD i then
    ((sig i).1, hopLamportLeaf i true (sig i).2)
  else
    (hopLamportLeaf i false (sig i).1, (sig i).2)

private theorem lamportRecPairs_eq_pubPairs (n : Nat) (d : BitVec 256)
    (sk : Nat → Digest32 × Digest32) :
    (List.range n).map (lamportRecPairAt d (lamportSignAt d sk)) =
      (List.range n).map (lamportPubPairAt sk) := by
  apply List.map_congr_left
  intro i _
  unfold lamportRecPairAt lamportSignAt lamportPubPairAt
  cases d.getLsbD i <;> rfl

/-- Parameterized `numBits`-bit `cSHAKE256` Lamport one-time PQ hop signature scheme. -/
def pqLamportHopSigN (numBits : Nat) : HopSigScheme where
  SecretKey := Nat → Digest32 × Digest32
  Sig := Nat → Digest32 × Digest32
  pkOf sk :=
    cshake32ByteArray hopPkCustomization
      (encodeLamportPairs ((List.range numBits).map (lamportPubPairAt sk)))
  sign sk msg :=
    lamportSignAt (hopMsgDigest256 msg) sk
  verify pk msg sig :=
    (cshake32ByteArray hopPkCustomization
      (encodeLamportPairs ((List.range numBits).map (lamportRecPairAt (hopMsgDigest256 msg) sig)))).data.toList ==
      pk.data.toList
  sign_complete sk msg := by
    rw [lamportRecPairs_eq_pubPairs numBits (hopMsgDigest256 msg) sk]
    exact beq_self_eq_true _

/-- Concrete inhabited 256-bit `cSHAKE256` Lamport one-time PQ hop signature scheme. -/
def pqLamport256HopSig : HopSigScheme := pqLamportHopSigN 256

example : Nonempty HopSigScheme := by exact ⟨pqLamport256HopSig⟩

/-- Self-delimiting preimage `len(prevLineage) ‖ prevLineage ‖ len(leb128 epochFloor) ‖ leb128(epochFloor) ‖ b.encode`
    signed by parent holder. -/
def hopSignPreimage (prevLineage : ByteArray) (epochFloor : Nat) (b : Block) : List UInt8 :=
  encodeListField prevLineage.data.toList ++ encodeListField (leb128 epochFloor) ++ b.encode

theorem hopSignPreimage_injective {p₁ p₂ : ByteArray} {e₁ e₂ : Nat} {b₁ b₂ : Block}
    (h : hopSignPreimage p₁ e₁ b₁ = hopSignPreimage p₂ e₂ b₂) :
    p₁ = p₂ ∧ e₁ = e₂ ∧ b₁ = b₂ := by
  simp only [hopSignPreimage, List.append_assoc] at h
  obtain ⟨hp, hrest⟩ := encodeListField_prefix_inj h
  obtain ⟨heL, hb⟩ := encodeListField_prefix_inj hrest
  have he : e₁ = e₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using heL)).1
  exact ⟨byteArray_eq_of_toList_eq hp, he, Block.encode_injective hb⟩

/-- One cryptographically signed capability delegation hop carrying an optional `epochFloor`. -/
structure SignedHop (S : HopSigScheme) where
  block : Block
  epochFloor : Nat := 0
  hopSig : S.Sig

/-! ### Nullifier Collection, Depth-Invariant Padding & Salted Dual-Spine `nulVecCommit` -/

/-- Collect `(credNul256, chanNul256)` for each delegation hop (`#tooth` guarded on channel!). -/
def collectHopNullifiers256 : ByteArray → List Block → List (BitVec 256)
  | _, [] => []
  | prevLin, b :: rest =>
    let nextLin := stepLineage prevLin b
    credNul256 nextLin :: chanNul256 b.channel :: collectHopNullifiers256 nextLin rest

/-- Exact `(2k + 2)` 256-bit credential & channel nullifiers of a chain `(g, blocks)`. -/
def collectChainNullifiers256 (g : Block) (blocks : List Block) : List (BitVec 256) :=
  credNul256 (rootLineage g) :: chanNul256 g.channel ::
    collectHopNullifiers256 (rootLineage g) blocks

theorem collectHopNullifiers256_length (prevLin : ByteArray) (bs : List Block) :
    (collectHopNullifiers256 prevLin bs).length = 2 * bs.length := by
  induction bs generalizing prevLin with
  | nil => rfl
  | cons b rest ih =>
    simp only [collectHopNullifiers256, List.length_cons, ih (stepLineage prevLin b)]
    omega

theorem collectChainNullifiers256_length (g : Block) (blocks : List Block) :
    (collectChainNullifiers256 g blocks).length = 2 * blocks.length + 2 := by
  simp [collectChainNullifiers256, collectHopNullifiers256_length]

private theorem credNul256_mem_collectHop (lin : ByteArray) (anc ext : List Block)
    (hne : anc ≠ []) :
    credNul256 (anc.foldl stepLineage lin) ∈ collectHopNullifiers256 lin (anc ++ ext) := by
  induction anc generalizing lin with
  | nil => exact absurd rfl hne
  | cons a tail ih =>
    cases tail with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil,
        collectHopNullifiers256, List.mem_cons, true_or]
    | cons b rest =>
      rw [List.cons_append, List.foldl_cons, collectHopNullifiers256]
      exact .tail _ (.tail _ (ih (stepLineage lin a) (by simp)))

theorem credNul256_prefix_mem_collectChain (g : Block) (anc ext : List Block) :
    credNul256 (lineageOf g anc) ∈ collectChainNullifiers256 g (anc ++ ext) := by
  cases anc with
  | nil => simp [lineageOf, collectChainNullifiers256]
  | cons b rest =>
    simp only [lineageOf, collectChainNullifiers256, List.mem_cons]
    exact .inr (.inr (credNul256_mem_collectHop (rootLineage g) (b :: rest) ext (by simp)))

private theorem chanNul256_mem_collectHop (lin : ByteArray) (bs : List Block) (b : Block)
    (hb : b ∈ bs) :
    chanNul256 b.channel ∈ collectHopNullifiers256 lin bs := by
  induction bs generalizing lin with
  | nil => cases hb
  | cons a rest ih =>
    simp only [collectHopNullifiers256, List.mem_cons]
    rcases List.mem_cons.1 hb with rfl | hrest
    · exact .inr (.inl rfl)
    · exact .inr (.inr (ih (stepLineage lin a) hrest))

theorem chanNul256_mem_collectChain_hop (g : Block) (blocks : List Block) (b : Block)
    (hb : b ∈ blocks) :
    chanNul256 b.channel ∈ collectChainNullifiers256 g blocks := by
  simp only [collectChainNullifiers256, List.mem_cons]
  exact .inr (.inr (chanNul256_mem_collectHop (rootLineage g) blocks b hb))

/-- Pad `realNuls` with domain-separated `padSlotNul256` slots to exact arity `2 * kMax + 2`. -/
def padNullifiersList (targetLen : Nat) (salt : BitVec 256)
    (realNuls : List (BitVec 256)) : List (BitVec 256) :=
  realNuls.take targetLen ++
    (List.range (targetLen - realNuls.length)).map (fun idx => padSlotNul256 salt idx)

def padNullifiersToArity (kMax : Nat) (salt : BitVec 256)
    (realNuls : List (BitVec 256)) : Array (BitVec 256) :=
  (padNullifiersList (2 * kMax + 2) salt realNuls).toArray

/-- **Depth-Invariant Commitment Arity (`padded_nullifier_arity_depth_invariant`)**:
    For every delegation hop count `k = blocks.length ≤ kMax`, the padded nullifier vector has
    exact size `2 * kMax + 2`, hiding the actual chain depth `k` (`#tooth` guarded!). -/
theorem padded_nullifier_arity_depth_invariant (kMax : Nat) (salt : BitVec 256)
    (g : Block) (blocks : List Block) (hk : blocks.length ≤ kMax) :
    (padNullifiersToArity kMax salt (collectChainNullifiers256 g blocks)).size = 2 * kMax + 2 := by
  have hlen := collectChainNullifiers256_length g blocks
  simp only [padNullifiersToArity, padNullifiersList, List.size_toArray, List.length_append,
    List.length_take, List.length_map, List.length_range, hlen]
  omega

theorem mem_realNuls_mem_padded (kMax : Nat) (salt : BitVec 256)
    (g : Block) (blocks : List Block) (hk : blocks.length ≤ kMax)
    {x : BitVec 256} (hx : x ∈ collectChainNullifiers256 g blocks) :
    x ∈ (padNullifiersToArity kMax salt (collectChainNullifiers256 g blocks)).toList := by
  have hlen : (collectChainNullifiers256 g blocks).length ≤ 2 * kMax + 2 := by
    rw [collectChainNullifiers256_length]; omega
  simp only [padNullifiersToArity, padNullifiersList, List.toList_toArray,
    List.take_of_length_le hlen, List.mem_append]
  exact .inl hx

theorem mem_padded_iff_real_or_padSlot (kMax : Nat) (salt : BitVec 256)
    (g : Block) (blocks : List Block) (hk : blocks.length ≤ kMax) (x : BitVec 256) :
    x ∈ (padNullifiersToArity kMax salt (collectChainNullifiers256 g blocks)).toList ↔
      x ∈ collectChainNullifiers256 g blocks ∨
      ∃ idx, idx < 2 * (kMax - blocks.length) ∧ x = padSlotNul256 salt idx := by
  have hlenEq := collectChainNullifiers256_length g blocks
  have hlen : (collectChainNullifiers256 g blocks).length ≤ 2 * kMax + 2 := by omega
  have hdiff : (2 * kMax + 2) - (collectChainNullifiers256 g blocks).length =
      2 * (kMax - blocks.length) := by omega
  simp only [padNullifiersToArity, padNullifiersList, List.toList_toArray,
    List.take_of_length_le hlen, hdiff, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (h | ⟨idx, hidx, rfl⟩)
    · exact .inl h
    · exact .inr ⟨idx, hidx, rfl⟩
  · rintro (h | ⟨idx, hidx, rfl⟩)
    · exact .inl h
    · exact .inr ⟨idx, hidx, rfl⟩

/-- Multilinear variable count `v = 3 + ⌈log₂(2 * kMax + 3)⌉` for the salted Dual-Spine table. -/
@[expose] def nulTableVars (kMax : Nat) : Nat :=
  3 + nextPow2Exp (2 * kMax + 3)

/-- Canonical `AjtaiParams` (`inhabitedAjtaiParams`) for capability chains up to `kMax` hops. -/
def capFoldAjtaiParams (kMax : Nat) : AjtaiParams :=
  inhabitedAjtaiParams (nulTableVars kMax)

theorem capFoldAjtaiParams_sisHard (kMax : Nat) :
    (capFoldAjtaiParams kMax).cols = 4 * (2 ^ nulTableVars kMax) ∧
    NonPigeonholeSISParams (capFoldAjtaiParams kMax) ∧
    ModuleSISHard (capFoldAjtaiParams kMax) 131070 := by
  exact inhabitedAjtaiParams_sisHard (nulTableVars kMax)

def encodeWordListGold8 : List (BitVec 256) → List Goldilocks
  | [] => []
  | w :: ws => encodeBitVec256Gold8 w ++ encodeWordListGold8 ws

theorem encodeWordListGold8_length :
    ∀ (ws : List (BitVec 256)), (encodeWordListGold8 ws).length = 8 * ws.length
  | [] => by rfl
  | w :: ws => by
    simp only [encodeWordListGold8, List.length_append, encodeBitVec256Gold8_length,
      encodeWordListGold8_length ws, List.length_cons]
    omega

theorem encodeWordListGold8_injective :
    ∀ {ws₁ ws₂ : List (BitVec 256)}, ws₁.length = ws₂.length →
      encodeWordListGold8 ws₁ = encodeWordListGold8 ws₂ → ws₁ = ws₂
  | [], [], _, _ => by rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | w₁ :: ws₁, w₂ :: ws₂, hlen, heq => by
    simp only [encodeWordListGold8] at heq
    obtain ⟨hw, hrest⟩ := List.append_inj heq (by simp [encodeBitVec256Gold8_length])
    rw [encodeBitVec256Gold8_injective hw, encodeWordListGold8_injective (Nat.succ.inj hlen) hrest]

/-- Build the power-of-two `Goldilocks` table encoding `salt :: paddedNuls` for `DualSpine`. -/
def buildSaltedNulTable (kMax : Nat) (salt : BitVec 256)
    (paddedNuls : Array (BitVec 256)) : List Goldilocks :=
  let v := nulTableVars kMax
  let payload := encodeWordListGold8 (salt :: paddedNuls.toList)
  payload ++ List.replicate (2 ^ v - payload.length) Goldilocks.zero

theorem buildSaltedNulTable_length (kMax : Nat) (salt : BitVec 256)
    (paddedNuls : Array (BitVec 256)) (hsz : paddedNuls.size = 2 * kMax + 2) :
    (buildSaltedNulTable kMax salt paddedNuls).length = 2 ^ nulTableVars kMax := by
  have hcov := le_two_pow_nextPow2Exp (2 * kMax + 3)
  have hpow : 2 ^ nulTableVars kMax = 8 * 2 ^ nextPow2Exp (2 * kMax + 3) := by
    unfold nulTableVars
    rw [Nat.pow_add]
  have hpayLen : (encodeWordListGold8 (salt :: paddedNuls.toList)).length = 8 * (2 * kMax + 3) := by
    rw [encodeWordListGold8_length, List.length_cons, Array.length_toList, hsz]
  have hle : 8 * (2 * kMax + 3) ≤ 2 ^ nulTableVars kMax := by
    rw [hpow]; exact Nat.mul_le_mul_left 8 hcov
  simp only [buildSaltedNulTable, List.length_append, List.length_replicate, hpayLen]
  omega

theorem buildSaltedNulTable_injective {kMax : Nat} {s₁ s₂ : BitVec 256}
    {n₁ n₂ : Array (BitVec 256)}
    (hsz₁ : n₁.size = 2 * kMax + 2) (hsz₂ : n₂.size = 2 * kMax + 2)
    (heq : buildSaltedNulTable kMax s₁ n₁ = buildSaltedNulTable kMax s₂ n₂) :
    s₁ = s₂ ∧ n₁ = n₂ := by
  simp only [buildSaltedNulTable] at heq
  have hl₁ : (encodeWordListGold8 (s₁ :: n₁.toList)).length = 8 * (2 * kMax + 3) := by
    rw [encodeWordListGold8_length, List.length_cons, Array.length_toList, hsz₁]
  have hl₂ : (encodeWordListGold8 (s₂ :: n₂.toList)).length = 8 * (2 * kMax + 3) := by
    rw [encodeWordListGold8_length, List.length_cons, Array.length_toList, hsz₂]
  obtain ⟨hpay, _⟩ := List.append_inj heq (hl₁.trans hl₂.symm)
  have hcons := encodeWordListGold8_injective (by simp [hsz₁, hsz₂]) hpay
  obtain ⟨hs, hn⟩ := List.cons.inj hcons
  exact ⟨hs, Array.toList_inj.1 hn⟩

/-- Salted Dual-Spine (`CanopyCommitment × AjtaiCommitment`) commitment to `paddedNuls`. -/
def commitSaltedNulTable (H : Hash32) (pp : AjtaiParams) (kMax : Nat)
    (salt : BitVec 256) (paddedNuls : Array (BitVec 256)) :
    CanopyCommitment × AjtaiCommitment :=
  let v := nulTableVars kMax
  (canopyAjtaiDualPCS H pp).commit ((), ()) v (buildSaltedNulTable kMax salt paddedNuls)

theorem nulVecCommit_arity_depth_invariant (H : Hash32) (pp : AjtaiParams)
    (kMax : Nat) (salt : BitVec 256) (paddedNuls : Array (BitVec 256)) :
    (commitSaltedNulTable H pp kMax salt paddedNuls).1.numVars = nulTableVars kMax ∧
    (commitSaltedNulTable H pp kMax salt paddedNuls).2.numVars = nulTableVars kMax := by
  unfold commitSaltedNulTable canopyAjtaiDualPCS DualPCS canopyMerklePCS ajtaiLatticePCS
    canopyCommit ajtaiLatticeCommit
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- Domain-separated 32-byte commitment binding `(salt, tailHolder, tailLineage)` without leaking `lineage`. -/
def holderLinkPreimage (salt : BitVec 256) (tailHolder tailLineage : ByteArray) : List UInt8 :=
  (0x30 : UInt8) :: encodeFrameList (be 32 salt.toNat) tailHolder.data.toList tailLineage.data.toList

theorem holderLinkPreimage_injective {s₁ s₂ : BitVec 256} {h₁ l₁ h₂ l₂ : ByteArray}
    (h : holderLinkPreimage s₁ h₁ l₁ = holderLinkPreimage s₂ h₂ l₂) :
    s₁ = s₂ ∧ h₁ = h₂ ∧ l₁ = l₂ := by
  simp only [holderLinkPreimage, List.cons.injEq] at h
  obtain ⟨hs, hh, hl⟩ := encodeFrameList_injective h.2
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact ⟨BitVec.eq_of_toNat_eq (be_injective (hpow ▸ s₁.isLt) (hpow ▸ s₂.isLt) hs),
         byteArray_eq_of_toList_eq hh,
         byteArray_eq_of_toList_eq hl⟩

def computeHolderLinkCommit (H : Hash32) (salt : BitVec 256)
    (tailHolder tailLineage : ByteArray) : Digest32 :=
  evalDigest32 H (holderLinkPreimage salt tailHolder tailLineage)

def hashRootGrant (H : Hash32) (g : Block) : Digest32 :=
  evalDigest32 H ((0x31 : UInt8) :: g.encode)

/-- Epoch-free fold of signed delegation hops (`#tooth` guarded on `subMask` attenuation!). -/
def foldHopsEpochFree {S : HopSigScheme} (staticEnv : Nat → KleenePred3) :
    (UInt64 × Nat × ResidualCaveat × ByteArray × ByteArray) → List (SignedHop S) →
    Option (UInt64 × Nat × ResidualCaveat × ByteArray × ByteArray)
  | state, [] => some state
  | (curRights, curFloor, curRes, curHolder, curLin), sh :: rest =>
    if subMask sh.block.rights curRights &&
       S.verify curHolder (hopSignPreimage curLin sh.epochFloor sh.block) sh.hopSig then
      let nextFloor := Nat.max curFloor sh.epochFloor
      let nextRes := conjoinResidual staticEnv curRes (pevalCaveat staticEnv sh.block.caveat)
      let nextLin := stepLineage curLin sh.block
      foldHopsEpochFree staticEnv (sh.block.rights, nextFloor, nextRes, sh.block.holder, nextLin) rest
    else none

/-- Public constant-arity statement of an offline-folded capability chain (`0` depth or lineage leak). -/
structure OfflineCapStatement where
  kMax : Nat
  rootGrantDigest : Digest32
  tailRights : UInt64
  epochFloor : Nat
  residualCaveat : ResidualCaveat
  nulVecCommit : CanopyCommitment × AjtaiCommitment
  holderLinkCommit : Digest32
  deriving DecidableEq

/-- Private holder witness retained after discarding all `k` ancestor blocks and hop signatures. -/
structure OfflineCapWitness where
  secretSalt : BitVec 256
  tailHolder : ByteArray
  tailLineage : ByteArray
  paddedNuls : Array (BitVec 256)
  deriving DecidableEq

/-- Output of Phase 1 (`foldChainEpochFree`): public `OfflineCapStatement` + private `OfflineCapWitness`. -/
structure OfflineCapBundle where
  stmt : OfflineCapStatement
  wit : OfflineCapWitness
  deriving DecidableEq

/-- **Phase 1 — Epoch-Free Offline Hop Folding (`foldChainEpochFree`)**:
    Folds root grant `g` + `k ≤ kMax` signed delegation hops **without any `RevokedSet256`**,
    verifying monotone `subMask`, tightening `epochFloor`, checking `HopSigScheme`, partially
    evaluating caveats into `ResidualCaveat`, and committing the `2 * kMax + 2` padded nullifiers
    into `nulVecCommit`. -/
def foldChainEpochFree (H : Hash32) (pp : AjtaiParams) (S : HopSigScheme)
    (kMax : Nat) (staticEnv : Nat → KleenePred3) (rootEpochFloor : Nat)
    (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256) :
    Option OfflineCapBundle :=
  if hops.size ≤ kMax then
    let initRes := pevalCaveat staticEnv g.caveat
    let initLin := rootLineage g
    match foldHopsEpochFree staticEnv (g.rights, rootEpochFloor, initRes, g.holder, initLin) hops.toList with
    | none => none
    | some (tailRights, finalFloor, finalRes, tailHolder, tailLin) =>
      let blocks := hops.toList.map SignedHop.block
      let paddedNuls := padNullifiersToArity kMax salt (collectChainNullifiers256 g blocks)
      let nulComm := commitSaltedNulTable H pp kMax salt paddedNuls
      let hLink := computeHolderLinkCommit H salt tailHolder tailLin
      some {
        stmt := {
          kMax := kMax
          rootGrantDigest := hashRootGrant H g
          tailRights := tailRights
          epochFloor := finalFloor
          residualCaveat := finalRes
          nulVecCommit := nulComm
          holderLinkCommit := hLink
        }
        wit := {
          secretSalt := salt
          tailHolder := tailHolder
          tailLineage := tailLin
          paddedNuls := paddedNuls
        }
      }
  else none

theorem foldHopsEpochFree_monotone {S : HopSigScheme} (staticEnv : Nat → KleenePred3)
    (hops : List (SignedHop S))
    (curRights : UInt64) (curFloor : Nat) (curRes : ResidualCaveat) (curHolder curLin : ByteArray)
    (fRights : UInt64) (fFloor : Nat) (fRes : ResidualCaveat) (fHolder fLin : ByteArray)
    (hFold : foldHopsEpochFree staticEnv (curRights, curFloor, curRes, curHolder, curLin) hops =
      some (fRights, fFloor, fRes, fHolder, fLin)) :
    subMask fRights curRights = true ∧
    curFloor ≤ fFloor ∧
    (∀ sh ∈ hops, subMask fRights sh.block.rights = true ∧ sh.epochFloor ≤ fFloor) := by
  induction hops generalizing curRights curFloor curRes curHolder curLin with
  | nil =>
    simp only [foldHopsEpochFree, Option.some.injEq, Prod.mk.injEq] at hFold
    rcases hFold with ⟨rfl, rfl, _, _, _⟩
    exact ⟨subMask_refl _, Nat.le_refl _, fun _ h => nomatch h⟩
  | cons sh rest ih =>
    simp only [foldHopsEpochFree] at hFold
    cases hCond : (subMask sh.block.rights curRights &&
        S.verify curHolder (hopSignPreimage curLin sh.epochFloor sh.block) sh.hopSig) with
    | false => rw [hCond] at hFold; simp at hFold
    | true =>
      rw [hCond] at hFold
      simp only [↓reduceIte] at hFold
      simp only [Bool.and_eq_true] at hCond
      obtain ⟨ihSub, ihFl, ihAll⟩ := ih sh.block.rights (Nat.max curFloor sh.epochFloor) _
        sh.block.holder (stepLineage curLin sh.block) hFold
      refine ⟨subMask_trans ihSub hCond.1,
        Nat.le_trans (Nat.le_max_left _ _) ihFl, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hrest
      · exact ⟨ihSub, Nat.le_trans (Nat.le_max_right _ _) ihFl⟩
      · exact ihAll x hrest

/-- **Monotonic Capability Attenuation & Epoch-Floor Tightening (`foldChainEpochFree_attenuation_monotone`)**:
    Across any hop count `k = hops.size ≤ kMax`, offline folding guarantees
    `effectiveMask ⊆ rootMask` (`subMask bundle.stmt.tailRights g.rights = true`) and
    `rootEpochFloor ≤ bundle.stmt.epochFloor` (`#tooth` guarded!). -/
theorem foldChainEpochFree_attenuation_monotone (H : Hash32) (pp : AjtaiParams)
    (S : HopSigScheme) (kMax : Nat) (staticEnv : Nat → KleenePred3) (rootEpochFloor : Nat)
    (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256) (bundle : OfflineCapBundle)
    (hOff : foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g hops salt = some bundle) :
    hops.size ≤ kMax ∧
    subMask bundle.stmt.tailRights g.rights = true ∧
    rootEpochFloor ≤ bundle.stmt.epochFloor ∧
    (∀ sh ∈ hops.toList,
      subMask bundle.stmt.tailRights sh.block.rights = true ∧
      sh.epochFloor ≤ bundle.stmt.epochFloor) := by
  unfold foldChainEpochFree at hOff
  if hk : hops.size ≤ kMax then
    simp only [hk, ↓reduceIte] at hOff
    cases hf : foldHopsEpochFree staticEnv
        (g.rights, rootEpochFloor, pevalCaveat staticEnv g.caveat, g.holder, rootLineage g)
        hops.toList with
    | none => rw [hf] at hOff; cases hOff
    | some st =>
      rw [hf] at hOff
      rcases st with ⟨tr, ff, fr, th, tl⟩
      simp only [Option.some.injEq] at hOff
      obtain ⟨hSub, hFl, hAll⟩ := foldHopsEpochFree_monotone staticEnv hops.toList
        g.rights rootEpochFloor _ g.holder (rootLineage g) tr ff fr th tl hf
      rw [← hOff]
      exact ⟨hk, hSub, hFl, hAll⟩
  else simp [hk] at hOff

/-! ## 4. Phase 2 — Epoch Binding, Unlinkable `presNul`, Fenzi-Safe `Transcript` & Live-Epoch Verifier -/

def presNulCustomization : List UInt8 := "OBEND.CAPFOLD.PRES/v1".toUTF8.data.toList
def presNulHash : Hash := cshake256Bytes presNulCustomization

/-- Self-delimiting preimage `len(leb128 epoch) ‖ leb128(epoch) ‖ frame(be32(secretSalt), turnId, lineage)`
    for `presNul`. -/
def presNulPreimage (epoch : Nat) (secretSalt : BitVec 256) (turnId lineage : ByteArray) : List UInt8 :=
  encodeListField (leb128 epoch) ++
    encodeFrameList (be 32 secretSalt.toNat) turnId.data.toList lineage.data.toList

theorem presNulPreimage_injective {e₁ e₂ : Nat} {s₁ s₂ : BitVec 256} {t₁ l₁ t₂ l₂ : ByteArray}
    (h : presNulPreimage e₁ s₁ t₁ l₁ = presNulPreimage e₂ s₂ t₂ l₂) :
    e₁ = e₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ l₁ = l₂ := by
  obtain ⟨heL, hframe⟩ := encodeListField_prefix_inj h
  obtain ⟨hs, ht, hl⟩ := encodeFrameList_injective hframe
  have he : e₁ = e₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using heL)).1
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact ⟨he,
         BitVec.eq_of_toNat_eq (be_injective (hpow ▸ s₁.isLt) (hpow ▸ s₂.isLt) hs),
         byteArray_eq_of_toList_eq ht,
         byteArray_eq_of_toList_eq hl⟩

/-- **Unlinkable Per-Turn Presentation Nullifier (`presNul`)**:
    `cSHAKE256("OBEND.CAPFOLD.PRES/v1", frame(epoch, secretSalt, turnId, lineage))` (`#tooth` guarded!). -/
def computePresNul256 (epoch : Nat) (secretSalt : BitVec 256) (turnId lineage : ByteArray) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (presNulHash (presNulPreimage epoch secretSalt turnId lineage)))

theorem computePresNul256_toNat (epoch : Nat) (secretSalt : BitVec 256) (turnId lineage : ByteArray) :
    (computePresNul256 epoch secretSalt turnId lineage).toNat =
      ofBE (presNulHash (presNulPreimage epoch secretSalt turnId lineage)) := by
  unfold computePresNul256
  rw [BitVec.toNat_ofNat]
  have hlen : (presNulHash (presNulPreimage epoch secretSalt turnId lineage)).length = 32 :=
    cshake256Bytes_length presNulCustomization _
  have hlt := ofBE_lt (presNulHash (presNulPreimage epoch secretSalt turnId lineage))
  rw [hlen] at hlt
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  exact Nat.mod_eq_of_lt (hpow ▸ hlt)

/-- **Presentation Nullifier Binding (`presNul_binds_or_collides`, `0 Classical`)**:
    Equal `presNul` digests come from identical `(epoch, secretSalt, turnId, lineage)` inputs or
    exhibit a named `CollisionAmong presNulHash`. -/
theorem presNul_binds_or_collides {e₁ e₂ : Nat} {s₁ s₂ : BitVec 256} {t₁ l₁ t₂ l₂ : ByteArray}
    (h : computePresNul256 e₁ s₁ t₁ l₁ = computePresNul256 e₂ s₂ t₂ l₂) :
    (e₁ = e₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ l₁ = l₂) ∨
      CollisionAmong presNulHash
        (fun x => x = presNulPreimage e₁ s₁ t₁ l₁ ∨ x = presNulPreimage e₂ s₂ t₂ l₂) := by
  if hp : presNulPreimage e₁ s₁ t₁ l₁ = presNulPreimage e₂ s₂ t₂ l₂ then
    exact .inl (presNulPreimage_injective hp)
  else
    have hn := congrArg BitVec.toNat h
    rw [computePresNul256_toNat, computePresNul256_toNat] at hn
    exact .inr ⟨presNulPreimage e₁ s₁ t₁ l₁, presNulPreimage e₂ s₂ t₂ l₂, .inl rfl, .inr rfl, hp, hn⟩

/-- Presentations of the same capability across distinct turns `turnId₁ ≠ turnId₂` evaluate
    `presNulHash` on provably distinct domain-framed preimages. -/
theorem presNul_cross_turn_distinct_preimages (epoch : Nat) (salt : BitVec 256)
    {turnId₁ turnId₂ : ByteArray} (lineage : ByteArray) (hNe : turnId₁ ≠ turnId₂) :
    presNulPreimage epoch salt turnId₁ lineage ≠ presNulPreimage epoch salt turnId₂ lineage := by
  exact fun h => hNe (presNulPreimage_injective h).2.2.1

/-- **Salt-Blinding Independence (`saltXorMask_bijective`)**:
    For any two secret 256-bit tags `x₁, x₂ : BitVec 256`, the salt translation
    `s ↦ s ^^^ x₁ ^^^ x₂` is an exact involution carrying `{s | s ^^^ x₁ = target}`
    bijectively onto `{s | s ^^^ x₂ = target}` (zero statistical distance under uniform `salt`). -/
def translateSaltForTag (x₁ x₂ s : BitVec 256) : BitVec 256 :=
  s ^^^ x₁ ^^^ x₂

theorem saltXorMask_bijective (x₁ x₂ s target : BitVec 256) :
    translateSaltForTag x₂ x₁ (translateSaltForTag x₁ x₂ s) = s ∧
    ((s ^^^ x₁ = target) ↔ (translateSaltForTag x₁ x₂ s ^^^ x₂ = target)) := by
  unfold translateSaltForTag
  refine ⟨?_, ?_⟩
  · rw [BitVec.xor_assoc (s ^^^ x₁) x₂ x₂, BitVec.xor_self, BitVec.xor_zero,
        BitVec.xor_assoc s x₁ x₁, BitVec.xor_self, BitVec.xor_zero]
  · have hEq : s ^^^ x₁ ^^^ x₂ ^^^ x₂ = s ^^^ x₁ := by
      rw [BitVec.xor_assoc (s ^^^ x₁) x₂ x₂, BitVec.xor_self, BitVec.xor_zero]
    rw [hEq]

/-- Load-bearing live-epoch floor & `RevokedGapRoot256` epoch binding guard (`#tooth` guarded!). -/
@[expose] def checkLiveEpochBound (epochFloor liveEpoch gapRootEpoch : Nat) : Bool :=
  decide (epochFloor ≤ liveEpoch) && (gapRootEpoch == liveEpoch)

theorem checkLiveEpochBound_iff (epochFloor liveEpoch gapRootEpoch : Nat) :
    checkLiveEpochBound epochFloor liveEpoch gapRootEpoch = true ↔
      epochFloor ≤ liveEpoch ∧ gapRootEpoch = liveEpoch := by
  simp [checkLiveEpochBound, beq_iff_eq]

/-- Public inputs pinned into the Fenzi-safe Fiat–Shamir transcript at presentation epoch `e`. -/
structure CapPresentationPublicInputs where
  epoch : Nat
  turnId : ByteArray
  needRights : UInt64
  offlineStmt : OfflineCapStatement
  revokedGapRoot : RevokedGapRoot256
  presNul : BitVec 256
  deriving DecidableEq

def encodeOfflineCapStatement (s : OfflineCapStatement) : ByteArray :=
  let metaBytes := Native.bytesOfList
    (encodeListField (leb128 s.kMax) ++ encodeListField (leb128 s.epochFloor) ++
      be 8 s.tailRights.toNat ++ s.residualCaveat.encode)
  let commBytes := TranscriptEncode.encodeTranscriptBytes s.nulVecCommit
  encodeFrame metaBytes commBytes
    (encodeFrame s.rootGrantDigest.bytes s.holderLinkCommit.bytes ByteArray.empty)

theorem encodeOfflineCapStatement_injective {s₁ s₂ : OfflineCapStatement}
    (h : encodeOfflineCapStatement s₁ = encodeOfflineCapStatement s₂) : s₁ = s₂ := by
  obtain ⟨k₁, rg₁, tr₁, ef₁, rc₁, nc₁, hl₁⟩ := s₁
  obtain ⟨k₂, rg₂, tr₂, ef₂, rc₂, nc₂, hl₂⟩ := s₂
  simp only [encodeOfflineCapStatement] at h
  obtain ⟨hm, hc, hd⟩ := encodeFrame_injective h
  obtain ⟨hrg, hhl, _⟩ := encodeFrame_injective hd
  have hnc := LawfulTranscriptEncode.encodeTranscriptBytes_injective hc
  have hmL := congrArg (fun b : ByteArray => b.data.toList) hm
  simp only [Native.bytesOfList_toList, List.append_assoc] at hmL
  obtain ⟨hkL, hrest₁⟩ := encodeListField_prefix_inj hmL
  obtain ⟨hefL, hrest₂⟩ := encodeListField_prefix_inj hrest₁
  obtain ⟨htrB, hrcB⟩ := List.append_inj hrest₂ (by simp [length_be])
  have hk : k₁ = k₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hkL)).1
  have hef : ef₁ = ef₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hefL)).1
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have htr : tr₁ = tr₂ :=
    UInt64.toNat_inj.1 (be_injective (h8 ▸ tr₁.toNat_lt) (h8 ▸ tr₂.toNat_lt) htrB)
  have hrc : rc₁ = rc₂ :=
    (Caveat.encode_prefix_inj rc₁ rc₂ [] [] (by simpa using hrcB)).1
  subst hk hef htr hrc hnc
  rw [Digest32.ext hrg, Digest32.ext hhl]

def encodeCapPresentationInputs (p : CapPresentationPublicInputs) : ByteArray :=
  encodeFrame
    (encodeFrame p.turnId
      (Native.bytesOfList (encodeListField (leb128 p.epoch) ++ be 8 p.needRights.toNat))
      (Native.bytesOfList (be 32 p.presNul.toNat)))
    (encodeOfflineCapStatement p.offlineStmt)
    (TranscriptEncode.encodeTranscriptBytes p.revokedGapRoot)

theorem encodeCapPresentationInputs_injective {p₁ p₂ : CapPresentationPublicInputs}
    (h : encodeCapPresentationInputs p₁ = encodeCapPresentationInputs p₂) : p₁ = p₂ := by
  obtain ⟨e₁, t₁, n₁, o₁, r₁, pn₁⟩ := p₁
  obtain ⟨e₂, t₂, n₂, o₂, r₂, pn₂⟩ := p₂
  simp only [encodeCapPresentationInputs] at h
  obtain ⟨ha, ho, hr⟩ := encodeFrame_injective h
  obtain ⟨ht, henB, hpnB⟩ := encodeFrame_injective ha
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have h32 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have henL := congrArg (fun b : ByteArray => b.data.toList) henB
  simp only [Native.bytesOfList_toList] at henL
  obtain ⟨heL, hnL⟩ := encodeListField_prefix_inj henL
  have he : e₁ = e₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using heL)).1
  have hn : n₁ = n₂ := UInt64.toNat_inj.1 (be_injective (h8 ▸ n₁.toNat_lt) (h8 ▸ n₂.toNat_lt) hnL)
  have hpnL := congrArg (fun b : ByteArray => b.data.toList) hpnB
  simp only [Native.bytesOfList_toList] at hpnL
  have hpn : pn₁ = pn₂ := BitVec.eq_of_toNat_eq (be_injective (h32 ▸ pn₁.isLt) (h32 ▸ pn₂.isLt) hpnL)
  have hoEq := encodeOfflineCapStatement_injective ho
  have hrEq := LawfulTranscriptEncode.encodeTranscriptBytes_injective hr
  subst he ht hn hpn hoEq hrEq; rfl

/-- Protocol identifier of `ZkCapFold` presentation verification. -/
def zkCapFoldProtocolId : String := "obend.polis.zkcapfold/v1"

/-- Fenzi-safe `.relationBound` transcript absorbing all `CapPresentationPublicInputs`. -/
def capPresentationTranscript (p : CapPresentationPublicInputs) : Transcript .relationBound :=
  bindRelation zkCapFoldProtocolId
    (Native.bytesOfList (leb128 p.offlineStmt.kMax))
    (encodeCapPresentationInputs p)
    (Transcript.newUnseeded ByteArray.empty)

/-- Phase-2 live-epoch presentation certificate: Dual-Spine Sumcheck + Canopy/Ajtai opening,
    Lyubashevsky smudged `verifyMaskedAjtaiOpening` response, and `2 * kMax + 2` gap openings. -/
structure EpochPresentationCert where
  presNul : BitVec 256
  commitSalt : BitVec 256
  tailHolder : ByteArray
  tailLineage : ByteArray
  paddedNuls : Array (BitVec 256)
  sumcheckRounds : List (RoundPoly Goldilocks)
  dualOpening : CanopyOpeningProof × AjtaiOpeningProof
  ajtaiMaskSyndrome : List Int
  ajtaiMaskedResp : List Int
  gapOpenings : Array GapSlotOpening256

/-- Prover generating a live-epoch `EpochPresentationCert` at `epoch` from `OfflineCapBundle` + `R_e`
    without accessing or re-verifying any of the `k` ancestor blocks or signatures. -/
def proveEpochPresentation (H : Hash32) (pp : AjtaiParams)
    (epoch : Nat) (rs : RevokedSet256) (turnId : ByteArray) (needRights : UInt64)
    (bundle : OfflineCapBundle) : CapPresentationPublicInputs × EpochPresentationCert :=
  let pNul := computePresNul256 epoch bundle.wit.secretSalt turnId bundle.wit.tailLineage
  let gapRoot := rs.gapRoot H epoch
  let pub : CapPresentationPublicInputs := {
    epoch := epoch
    turnId := turnId
    needRights := needRights
    offlineStmt := bundle.stmt
    revokedGapRoot := gapRoot
    presNul := pNul
  }
  let v := nulTableVars bundle.stmt.kMax
  let tbl := buildSaltedNulTable bundle.stmt.kMax bundle.wit.secretSalt bundle.wit.paddedNuls
  let pcs := canopyAjtaiDualPCS H pp
  let trRel := capPresentationTranscript pub
  let sc := honestBoundSumcheckProver (R := Goldilocks) bundle.stmt.nulVecCommit v tbl trRel
  let dualOpen := (pcs.openEval ((), ()) v tbl sc.2.1 sc.2.2).1
  let limbs := gadgetDecomposeTable tbl
  let zeroMask := List.replicate pp.cols (0 : Int)
  let maskSyn := GameSoundness.ajtaiSyndrome pp.modulus pp.matrix zeroMask
  let mResp := maskedResponse 1 limbs zeroMask
  let gaps := bundle.wit.paddedNuls.map (openGapForNullifier H epoch rs)
  (pub, {
    presNul := pNul
    commitSalt := bundle.wit.secretSalt
    tailHolder := bundle.wit.tailHolder
    tailLineage := bundle.wit.tailLineage
    paddedNuls := bundle.wit.paddedNuls
    sumcheckRounds := sc.1
    dualOpening := dualOpen
    ajtaiMaskSyndrome := maskSyn
    ajtaiMaskedResp := mResp
    gapOpenings := gaps
  })

/-- Verify all `2 * kMax + 2` sorted-gap openings against `RevokedGapRoot256`. -/
def verifyAllGapSlots (H : Hash32) (root : RevokedGapRoot256)
    (nuls : Array (BitVec 256)) (openings : Array GapSlotOpening256) : Bool :=
  (nuls.size == openings.size) &&
  (List.finRange nuls.size).all fun i =>
    match openings[i.val]? with
    | none => false
    | some prf => verifyGapSlotOpening H root nuls[i] prf

/-- **Phase 2 — Live-Epoch Presentation Verifier (`verifyEpochPresentation`)**:
    Checks fixed `2 * kMax + 2` arity, `checkLiveEpochBound`, `subMask` authorization,
    `ResidualCaveat` acceptance on `liveEnv`, `presNul` & `holderLinkCommit` binding,
    `DualSpine` `verifyDualSumcheckPIOP`, `verifyMaskedAjtaiOpening`, and all `2 * kMax + 2`
    sorted-gap openings against `revokedGapRoot`. -/
def verifyEpochPresentation (H : Hash32) (pp : AjtaiParams)
    (liveEnv : Nat → KleenePred3) (pub : CapPresentationPublicInputs)
    (cert : EpochPresentationCert) : Bool :=
  let kMax := pub.offlineStmt.kMax
  let expectedSlots := 2 * kMax + 2
  let v := nulTableVars kMax
  let tbl := buildSaltedNulTable kMax cert.commitSalt cert.paddedNuls
  let limbs := gadgetDecomposeTable tbl
  (cert.paddedNuls.size == expectedSlots) &&
  (cert.gapOpenings.size == expectedSlots) &&
  checkLiveEpochBound pub.offlineStmt.epochFloor pub.epoch pub.revokedGapRoot.epoch &&
  subMask pub.needRights pub.offlineStmt.tailRights &&
  (pub.offlineStmt.residualCaveat.eval liveEnv).accepts &&
  (cert.presNul == pub.presNul) &&
  (pub.presNul == computePresNul256 pub.epoch cert.commitSalt pub.turnId cert.tailLineage) &&
  (pub.offlineStmt.holderLinkCommit ==
    computeHolderLinkCommit H cert.commitSalt cert.tailHolder cert.tailLineage) &&
  (pub.offlineStmt.nulVecCommit ==
    commitSaltedNulTable H pp kMax cert.commitSalt cert.paddedNuls) &&
  verifyDualSumcheckPIOP (canopyMerklePCS H) (ajtaiLatticePCS pp) ((), ())
    1 v pub.offlineStmt.nulVecCommit (hypercubeSum v tbl)
    cert.sumcheckRounds cert.dualOpening (capPresentationTranscript pub) &&
  verifyMaskedAjtaiOpening pp.modulus pp.cols 65535 pp.matrix
    (GameSoundness.ajtaiSyndrome pp.modulus pp.matrix limbs)
    cert.ajtaiMaskSyndrome 1 cert.ajtaiMaskedResp &&
  verifyAllGapSlots H pub.revokedGapRoot cert.paddedNuls cert.gapOpenings

/-- **Epoch-Floor & Gap-Root Epoch Binding (`verifyEpochPresentation_enforces_epoch_binding`)**:
    Every accepted presentation binds `pub.offlineStmt.epochFloor ≤ pub.epoch` and
    `pub.revokedGapRoot.epoch = pub.epoch` (`#tooth` guarded!). -/
theorem verifyEpochPresentation_enforces_epoch_binding
    (H : Hash32) (pp : AjtaiParams) (liveEnv : Nat → KleenePred3)
    (pub : CapPresentationPublicInputs) (cert : EpochPresentationCert) :
    verifyEpochPresentation H pp liveEnv pub cert = true →
      pub.offlineStmt.epochFloor ≤ pub.epoch ∧ pub.revokedGapRoot.epoch = pub.epoch := by
  intro hVer
  simp only [verifyEpochPresentation, Bool.and_eq_true] at hVer
  rcases hVer with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hEp⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  exact (checkLiveEpochBound_iff _ _ _).1 hEp

/-! ## 5. Constructive `0 Classical` `PSum` Soundness/Collision-Extractor & Bidirectional Equivalence -/

private theorem mem_flatMap_of_mem {α β : Type} (f : α → List β) :
    ∀ {xs : List α} {a : α} {b : β}, a ∈ xs → b ∈ f a → b ∈ xs.flatMap f
  | [], _, _, ha, _ => by exact nomatch ha
  | x :: rest, a, b, ha, hb => by
    simp only [List.flatMap_cons, List.mem_append]
    rcases List.mem_cons.1 ha with rfl | hrest
    · exact .inl hb
    · exact .inr (mem_flatMap_of_mem f hrest hb)

/-- Constructively extract either `∀ x ∈ nuls, rs.contains x = false` or a `PinnedCollision` (`0 Classical`). -/
def extractAllGapSlotsOrCollision (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (nuls : Array (BitVec 256)) (openings : Array GapSlotOpening256)
    (hAll : verifyAllGapSlots H (rs.gapRoot H epoch) nuls openings = true) :
    PSum (PLift (∀ x ∈ nuls.toList, rs.contains x = false ∧ IsInteriorNullifier256 x))
      (PinnedCollision H.eval (allGapSlotFrames H epoch rs openings)) :=
  have hParts : nuls.size = openings.size ∧
      ∀ (i : Fin nuls.size), True →
        (match openings[i.val]? with
         | none => false
         | some prf => verifyGapSlotOpening H (rs.gapRoot H epoch) nuls[i] prf) = true := by
    simpa only [verifyAllGapSlots, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_finRange] using hAll
  let rec checkIdx (idx : Nat) :
      PSum (PLift (∀ j (hj : j < nuls.size), idx ≤ j →
              rs.contains (nuls[j]'hj) = false ∧ IsInteriorNullifier256 (nuls[j]'hj)))
        (PinnedCollision H.eval (allGapSlotFrames H epoch rs openings)) :=
    if hlt : idx < nuls.size then
      have ho : idx < openings.size := hParts.1 ▸ hlt
      have hVer : verifyGapSlotOpening H (rs.gapRoot H epoch) (nuls[idx]'hlt) (openings[idx]'ho) = true := by
        have hi := hParts.2 ⟨idx, hlt⟩ trivial
        simpa [Array.getElem?_eq_getElem ho] using hi
      match extractGapSlotOpeningOrLive H epoch rs (nuls[idx]'hlt) (openings[idx]'ho) hVer with
      | .inr col =>
        .inr (liftPinnedCollision (fun m hm =>
          mem_flatMap_of_mem (slotDiscrepancyFrames H epoch rs)
            (Array.getElem_mem_toList ho) hm) col)
      | .inl hCur =>
        match checkIdx (idx + 1) with
        | .inr col => .inr col
        | .inl hRest => .inl ⟨fun j hj hge => by
          rcases Nat.lt_or_eq_of_le hge with hgt | rfl
          · exact hRest.down j hj (by omega)
          · exact hCur.down⟩
    else
      .inl ⟨fun j hj hge => absurd (Nat.lt_of_lt_of_le hj (Nat.not_lt.1 hlt)) (Nat.not_lt_of_ge hge)⟩
  termination_by nuls.size - idx
  match checkIdx 0 with
  | .inr col => .inr col
  | .inl hall => .inl ⟨fun x hx => by
    obtain ⟨j, hjL, rfl⟩ := List.mem_iff_getElem.1 hx
    have hj : j < nuls.size := by simpa using hjL
    exact hall.down j hj (Nat.zero_le j)⟩

theorem verifyAllGapSlots_complete (H : Hash32) (epoch : Nat) (rs : RevokedSet256)
    (nuls : Array (BitVec 256))
    (hInt : ∀ x ∈ nuls.toList, IsInteriorNullifier256 x)
    (hLive : ∀ x ∈ nuls.toList, rs.contains x = false) :
    verifyAllGapSlots H (rs.gapRoot H epoch) nuls (nuls.map (openGapForNullifier H epoch rs)) = true := by
  simp only [verifyAllGapSlots, Array.size_map, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, List.mem_finRange]
  intro i _
  have hiMap : i.val < (nuls.map (openGapForNullifier H epoch rs)).size := by simp [i.isLt]
  rw [Array.getElem?_eq_getElem hiMap, Array.getElem_map]
  have hmem : nuls[i] ∈ nuls.toList := Array.getElem_mem_toList i.isLt
  exact verifyGapSlotOpening_complete H epoch rs nuls[i] (hInt _ hmem) (hLive _ hmem)

/-- All hop signatures along `(curHolder, curLin)` verify cleanly. -/
def allHopSigsValid {S : HopSigScheme} : ByteArray → ByteArray → List (SignedHop S) → Bool
  | _, _, [] => true
  | curHolder, curLin, sh :: rest =>
    S.verify curHolder (hopSignPreimage curLin sh.epochFloor sh.block) sh.hopSig &&
    allHopSigsValid sh.block.holder (stepLineage curLin sh.block) rest

private theorem foldHopsEpochFree_sound_for_foldStep {S : HopSigScheme}
    {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (rs : RevokedSet256)
    (hops : List (SignedHop S))
    (curRights : UInt64) (curFloor : Nat) (curRes : ResidualCaveat) (curHolder curLin : ByteArray)
    (fRights : UInt64) (fFloor : Nat) (fRes : ResidualCaveat) (fHolder fLin : ByteArray)
    (hFold : foldHopsEpochFree staticEnv (curRights, curFloor, curRes, curHolder, curLin) hops =
      some (fRights, fFloor, fRes, fHolder, fLin))
    (hLive : ∀ x ∈ collectHopNullifiers256 curLin (hops.map SignedHop.block), rs.contains x = false) :
    List.foldlM (foldStep rs.toRevokedSet liveEnv)
      ⟨curRights, curRes.eval liveEnv, curLin⟩ (hops.map SignedHop.block) =
      some ⟨fRights, fRes.eval liveEnv, fLin⟩ ∧
    fLin = (hops.map SignedHop.block).foldl stepLineage curLin := by
  induction hops generalizing curRights curFloor curRes curHolder curLin with
  | nil =>
    simp only [foldHopsEpochFree, Option.some.injEq, Prod.mk.injEq] at hFold
    rcases hFold with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | cons sh rest ih =>
    simp only [foldHopsEpochFree] at hFold
    cases hCond : (subMask sh.block.rights curRights &&
        S.verify curHolder (hopSignPreimage curLin sh.epochFloor sh.block) sh.hopSig) with
    | false => rw [hCond] at hFold; simp at hFold
    | true =>
      rw [hCond] at hFold
      simp only [↓reduceIte] at hFold
      simp only [Bool.and_eq_true] at hCond
      have hCredLive : rs.contains (credNul256 (stepLineage curLin sh.block)) = false :=
        hLive _ (.head _)
      have hChanLive : rs.contains (chanNul256 sh.block.channel) = false :=
        hLive _ (.tail _ (.head _))
      have hRestLive : ∀ x ∈ collectHopNullifiers256 (stepLineage curLin sh.block)
          (rest.map SignedHop.block), rs.contains x = false :=
        fun x hx => hLive x (.tail _ (.tail _ hx))
      have hStep : foldStep rs.toRevokedSet liveEnv
          ⟨curRights, curRes.eval liveEnv, curLin⟩ sh.block =
          some ⟨sh.block.rights,
            (conjoinResidual staticEnv curRes (pevalCaveat staticEnv sh.block.caveat)).eval liveEnv,
            stepLineage curLin sh.block⟩ := by
        have hLinB : lineageLive rs.toRevokedSet (stepLineage curLin sh.block) = true := by
          rw [lineageLive, ← credNul256_toNat, rs.toRevokedSet_contains_eq, hCredLive]; rfl
        have hChB : channelLive rs.toRevokedSet sh.block = true := by
          rw [channelLive, ← chanNul256_toNat, rs.toRevokedSet_contains_eq, hChanLive]; rfl
        unfold foldStep attenuationOk
        rw [hCond.1, hLinB, hChB]
        simp only [Bool.and_self, ↓reduceIte, conjoinResidual_eval_eq hRef, pevalCaveat_eval_eq hRef]
      obtain ⟨ihFold, ihLin⟩ := ih sh.block.rights (Nat.max curFloor sh.epochFloor) _
        sh.block.holder (stepLineage curLin sh.block) hFold hRestLive
      refine ⟨?_, ihLin⟩
      rw [List.map_cons]
      exact (foldlM_cons_some _ _ _ _ _).2 ⟨_, hStep, ihFold⟩

private theorem foldStep_complete_for_foldHopsEpochFree {S : HopSigScheme}
    {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (rs : RevokedSet256)
    (hops : List (SignedHop S))
    (curRights : UInt64) (curFloor : Nat) (curRes : ResidualCaveat) (curHolder curLin : ByteArray)
    (finalAcc : CapAccumulator)
    (hSigs : allHopSigsValid curHolder curLin hops = true)
    (hFold : List.foldlM (foldStep rs.toRevokedSet liveEnv)
      ⟨curRights, curRes.eval liveEnv, curLin⟩ (hops.map SignedHop.block) = some finalAcc) :
    (∃ fFloor fRes fHolder fLin,
      foldHopsEpochFree staticEnv (curRights, curFloor, curRes, curHolder, curLin) hops =
        some (finalAcc.rights, fFloor, fRes, fHolder, fLin) ∧
      fRes.eval liveEnv = finalAcc.verdict ∧
      fLin = finalAcc.lineage ∧
      (∀ epoch, curFloor ≤ epoch → (∀ sh ∈ hops, sh.epochFloor ≤ epoch) → fFloor ≤ epoch)) ∧
    (∀ x ∈ collectHopNullifiers256 curLin (hops.map SignedHop.block), rs.contains x = false) := by
  induction hops generalizing curRights curFloor curRes curHolder curLin with
  | nil =>
    simp only [List.map_nil, List.foldlM_nil] at hFold
    cases hFold
    exact ⟨⟨curFloor, curRes, curHolder, curLin, rfl, rfl, rfl, fun _ h _ => h⟩,
      fun _ hx => by simp only [List.map_nil, collectHopNullifiers256] at hx; nomatch hx⟩
  | cons sh rest ih =>
    simp only [allHopSigsValid, Bool.and_eq_true] at hSigs
    simp only [List.map_cons] at hFold
    obtain ⟨a1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 hFold
    obtain ⟨hatt, hlin, hchan, ha1⟩ := foldStep_eq_some h1
    simp only [attenuationOk] at hatt
    have hNextEq : a1 = ⟨sh.block.rights,
        (conjoinResidual staticEnv curRes (pevalCaveat staticEnv sh.block.caveat)).eval liveEnv,
        stepLineage curLin sh.block⟩ := by
      rw [ha1, conjoinResidual_eval_eq hRef, pevalCaveat_eval_eq hRef]
    rw [hNextEq] at h2
    obtain ⟨⟨fFloor, fRes, fHolder, fLin, ihFold, ihVer, ihLin, ihFl⟩, ihLive⟩ :=
      ih sh.block.rights (Nat.max curFloor sh.epochFloor) _ sh.block.holder
        (stepLineage curLin sh.block) hSigs.2 h2
    have hCredF : rs.contains (credNul256 (stepLineage curLin sh.block)) = false := by
      rw [lineageLive, ← credNul256_toNat, rs.toRevokedSet_contains_eq] at hlin
      simpa only [Bool.not_eq_true'] using hlin
    have hChanF : rs.contains (chanNul256 sh.block.channel) = false := by
      rw [channelLive, ← chanNul256_toNat, rs.toRevokedSet_contains_eq] at hchan
      simpa only [Bool.not_eq_true'] using hchan
    refine ⟨⟨fFloor, fRes, fHolder, fLin, ?_, ihVer, ihLin, ?_⟩, ?_⟩
    · simp only [foldHopsEpochFree, hatt, hSigs.1, Bool.and_self, ↓reduceIte, ihFold]
    · intro epoch hCur hAll
      exact ihFl epoch (Nat.max_le.2 ⟨hCur, hAll sh (.head _)⟩) (fun s hs => hAll s (.tail _ hs))
    · intro x hx
      simp only [List.map_cons, collectHopNullifiers256, List.mem_cons] at hx
      rcases hx with rfl | rfl | hxRest
      · exact hCredF
      · exact hChanF
      · exact ihLive x hxRest

/-- Explicit `Type`-valued cryptographic break witness for `ZkCapFold` (`0 Classical`). -/
inductive ZkCapFoldBreakWitness (H : Hash32) (pp : AjtaiParams) (kMax : Nat)
    (gapDomain : List (List UInt8)) : Type where
  | dualCommitBreak
      (hashCol : HashCollisionWitness H.eval (merkleMaxPreimageBytes (nulTableVars kMax)))
      (sisBreak : SISShortVecWitness pp.modulus 131070 pp.matrix)
  | gapTreePinnedCollision
      (col : PinnedCollision H.eval gapDomain)

/-- Every `ZkCapFoldBreakWitness` deterministically yields an explicit byte-level `H.eval`
    (`cSHAKE256`) collision pair `(msgA, msgB)` with `msgA ≠ msgB ∧ H.eval msgA = H.eval msgB`
    (`0 Classical.choice`). -/
def ZkCapFoldBreakWitness.toCshakeCollisionPair {H : Hash32} {pp : AjtaiParams}
    {kMax : Nat} {gapDomain : List (List UInt8)}
    (w : ZkCapFoldBreakWitness H pp kMax gapDomain) : CshakeCollisionPair H.eval :=
  match w with
  | .dualCommitBreak hCol _ =>
    { msgA := hCol.msgA
      msgB := hCol.msgB
      distinct := hCol.distinct
      sameDigest := hash32_eq_of_ofBE_eq H hCol.sameDigest }
  | .gapTreePinnedCollision pCol =>
    { msgA := pCol.msgA
      msgB := pCol.msgB
      distinct := pCol.distinct
      sameDigest := hash32_eq_of_ofBE_eq H pCol.sameDigest }

/-- **Constructive `0 Classical.choice` Epoch-Decoupled Soundness & Collision Extractor
    (`extractEpochPresentationOrFoldChain`)**:
    Given `bundle` folded offline (`foldChainEpochFree ... = some bundle`, zero `RevokedSet256`)
    and `cert` accepted at a live `epoch` against `R_sat.gapRoot H epoch`, deterministically computes EITHER:
    1. Exact `ZkBiscuit.foldChain R_sat.toRevokedSet liveEnv g blocks = some acc` with
       `authorize acc pub.needRights = true`, monotonic attenuation `subMask acc.rights g.rights = true`,
       and epoch bounds `rootEpochFloor ≤ pub.epoch` & `∀ sh ∈ hops, sh.epochFloor ≤ pub.epoch`, OR
    2. A concrete `ZkCapFoldBreakWitness` (from which `.toCshakeCollisionPair` extracts an explicit
       collision `m₁ ≠ m₂ ∧ H.eval m₁ = H.eval m₂`, plus `SISShortVecWitness` on commitment mismatch)! -/
def extractEpochPresentationOrFoldChain (H : Hash32) (pp : AjtaiParams) {S : HopSigScheme}
    {kMax rootEpochFloor : Nat} {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (hCols : pp.cols = 4 * (2 ^ nulTableVars kMax))
    {g : Block} {hops : Array (SignedHop S)} {salt : BitVec 256} {bundle : OfflineCapBundle}
    (hOffline : foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g hops salt = some bundle)
    (R_sat : RevokedSet256) {pub : CapPresentationPublicInputs} {cert : EpochPresentationCert}
    (hStmt : pub.offlineStmt = bundle.stmt)
    (hRoot : pub.revokedGapRoot = R_sat.gapRoot H pub.epoch)
    (hVer : verifyEpochPresentation H pp liveEnv pub cert = true) :
    PSum
      { acc : CapAccumulator //
        foldChain R_sat.toRevokedSet liveEnv g (hops.map SignedHop.block) = some acc ∧
        authorize acc pub.needRights = true ∧
        pub.offlineStmt.epochFloor ≤ pub.epoch ∧
        pub.revokedGapRoot.epoch = pub.epoch ∧
        rootEpochFloor ≤ pub.epoch ∧
        (∀ sh ∈ hops.toList, sh.epochFloor ≤ pub.epoch) ∧
        subMask acc.rights g.rights = true ∧
        acc.rights = bundle.stmt.tailRights ∧
        acc.lineage = lineageOf g (hops.map SignedHop.block).toList }
      (ZkCapFoldBreakWitness H pp kMax (allGapSlotFrames H pub.epoch R_sat cert.gapOpenings)) :=
  if hk : hops.size ≤ kMax then
    match hFoldHops : foldHopsEpochFree staticEnv
        (g.rights, rootEpochFloor, pevalCaveat staticEnv g.caveat, g.holder, rootLineage g)
        hops.toList with
    | none =>
      False.elim (by simp [foldChainEpochFree, hk, hFoldHops] at hOffline)
    | some (tr, ff, fr, th, tl) =>
      let monNuls := padNullifiersToArity kMax salt
        (collectChainNullifiers256 g (hops.toList.map SignedHop.block))
      have hBundleFields :
          bundle.stmt.kMax = kMax ∧
          bundle.stmt.tailRights = tr ∧
          bundle.stmt.epochFloor = ff ∧
          bundle.stmt.residualCaveat = fr ∧
          bundle.wit.secretSalt = salt ∧
          bundle.wit.paddedNuls = monNuls ∧
          bundle.stmt.nulVecCommit = commitSaltedNulTable H pp kMax salt monNuls := by
        unfold foldChainEpochFree at hOffline
        simp only [hk, ↓reduceIte, hFoldHops, Option.some.injEq] at hOffline
        rw [← hOffline]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hVerFacts :
          cert.paddedNuls.size = 2 * kMax + 2 ∧
          (pub.offlineStmt.epochFloor ≤ pub.epoch ∧ pub.revokedGapRoot.epoch = pub.epoch) ∧
          subMask pub.needRights bundle.stmt.tailRights = true ∧
          (bundle.stmt.residualCaveat.eval liveEnv).accepts = true ∧
          commitSaltedNulTable H pp kMax cert.commitSalt cert.paddedNuls = bundle.stmt.nulVecCommit ∧
          verifyAllGapSlots H (R_sat.gapRoot H pub.epoch) cert.paddedNuls cert.gapOpenings = true := by
        simp only [verifyEpochPresentation, Bool.and_eq_true, beq_iff_eq] at hVer
        rcases hVer with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSzN, _⟩, hEp⟩, hSub⟩, hAcc⟩, _⟩, _⟩, _⟩, hComm⟩, _⟩, _⟩, hGaps⟩
        have hEpP := (checkLiveEpochBound_iff _ _ _).1 hEp
        rw [hStmt] at hSzN hSub hAcc hComm
        rw [hBundleFields.1] at hSzN hComm
        rw [hRoot] at hGaps
        exact ⟨hSzN, hEpP, hSub, hAcc, hComm.symm, hGaps⟩
      have hMonSz : monNuls.size = 2 * kMax + 2 :=
        padded_nullifier_arity_depth_invariant kMax salt g (hops.toList.map SignedHop.block)
          (by simpa using hk)
      if hSameWit : cert.commitSalt = salt ∧ cert.paddedNuls = monNuls then
        have hGapsMon :
            verifyAllGapSlots H (R_sat.gapRoot H pub.epoch) monNuls cert.gapOpenings = true := by
          rw [← hSameWit.2]; exact hVerFacts.2.2.2.2.2
        match extractAllGapSlotsOrCollision H pub.epoch R_sat monNuls cert.gapOpenings hGapsMon with
        | .inr gapCol => .inr (.gapTreePinnedCollision gapCol)
        | .inl hAllLive =>
          .inl (by
            obtain ⟨hSubRoot, hFlRoot, hAllHopMono⟩ :=
              foldHopsEpochFree_monotone staticEnv hops.toList
                g.rights rootEpochFloor _ g.holder (rootLineage g) tr ff fr th tl hFoldHops
            have hFfLe : ff ≤ pub.epoch := by
              rw [← hBundleFields.2.2.1, ← hStmt]; exact hVerFacts.2.1.1
            have hRealLive : ∀ x ∈ collectChainNullifiers256 g (hops.toList.map SignedHop.block),
                R_sat.contains x = false := by
              intro x hx
              have hmem : x ∈ monNuls.toList :=
                mem_realNuls_mem_padded kMax salt g _ (by simpa using hk) hx
              exact (hAllLive.down x hmem).1
            have hRootCred : lineageLive R_sat.toRevokedSet (rootLineage g) = true := by
              have hc := hRealLive _ (.head _)
              rw [lineageLive, ← credNul256_toNat, R_sat.toRevokedSet_contains_eq, hc]; rfl
            have hRootChan : channelLive R_sat.toRevokedSet g = true := by
              have hc := hRealLive _ (.tail _ (.head _))
              rw [channelLive, ← chanNul256_toNat, R_sat.toRevokedSet_contains_eq, hc]; rfl
            have hHopLive : ∀ x ∈ collectHopNullifiers256 (rootLineage g) (hops.toList.map SignedHop.block),
                R_sat.contains x = false :=
              fun x hx => hRealLive x (.tail _ (.tail _ hx))
            have hFoldRoot : foldRoot R_sat.toRevokedSet liveEnv g =
                some ⟨g.rights, (pevalCaveat staticEnv g.caveat).eval liveEnv, rootLineage g⟩ := by
              unfold foldRoot
              rw [hRootCred, hRootChan, pevalCaveat_eval_eq hRef]; rfl
            obtain ⟨hFoldRest, hLinEq⟩ :=
              foldHopsEpochFree_sound_for_foldStep hRef R_sat hops.toList
                g.rights rootEpochFloor (pevalCaveat staticEnv g.caveat) g.holder (rootLineage g)
                tr ff fr th tl hFoldHops hHopLive
            refine ⟨⟨tr, fr.eval liveEnv, tl⟩, ?_, ?_, hVerFacts.2.1.1, hVerFacts.2.1.2,
              Nat.le_trans hFlRoot hFfLe,
              fun sh hsh => Nat.le_trans (hAllHopMono sh hsh).2 hFfLe,
              hSubRoot, hBundleFields.2.1.symm, ?_⟩
            · rw [foldChain_eq_some_iff]
              refine ⟨_, hFoldRoot, ?_⟩
              simpa [Array.toList_map] using hFoldRest
            · simp only [authorize, Bool.and_eq_true]
              rw [← hBundleFields.2.1, ← hBundleFields.2.2.2.1]
              exact ⟨hVerFacts.2.2.1, hVerFacts.2.2.2.1⟩
            · simpa [lineageOf, Array.toList_map] using hLinEq)
      else
        let tCert := buildSaltedNulTable kMax cert.commitSalt cert.paddedNuls
        let tMon := buildSaltedNulTable kMax salt monNuls
        have hNeTbl : tCert ≠ tMon := fun hEq =>
          hSameWit (buildSaltedNulTable_injective hVerFacts.1 hMonSz hEq)
        have hCommEq :
            (canopyAjtaiDualPCS H pp).commit ((), ()) (nulTableVars kMax) tCert =
            (canopyAjtaiDualPCS H pp).commit ((), ()) (nulTableVars kMax) tMon := by
          dsimp only [tCert, tMon]
          exact hVerFacts.2.2.2.2.1.trans hBundleFields.2.2.2.2.2.2
        let both := extractDualCommitCollisionBoth H pp tCert tMon
          (buildSaltedNulTable_length kMax cert.commitSalt cert.paddedNuls hVerFacts.1)
          (buildSaltedNulTable_length kMax salt monNuls hMonSz)
          hCols hNeTbl hCommEq
        .inr (.dualCommitBreak both.1 both.2)
  else
    False.elim (by simp [foldChainEpochFree, hk] at hOffline)

attribute [local irreducible] honestBoundSumcheckProver verifyDualSumcheckPIOP verifyMaskedAjtaiOpening

/-- **Phase-2 Refresh Completeness (`proveEpochPresentation_complete_of_bundle`)**:
    For ANY existing offline-folded `bundle` (`bundle.stmt.epochFloor ≤ epoch`) whose `2 * kMax + 2`
    padded nullifiers are interior and unrevoked in `R_sat`, `proveEpochPresentation` produces a valid
    `EpochPresentationCert` at `epoch` **without re-opening or re-signing any static hop**, and with
    `allGapSlotFrames = []` (`0` discrepancy frames). -/
theorem proveEpochPresentation_complete_of_bundle
    (H : Hash32) (pp : AjtaiParams) {liveEnv : Nat → KleenePred3}
    (bundle : OfflineCapBundle) (epoch : Nat) (R_sat : RevokedSet256)
    (turnId : ByteArray) (needRights : UInt64)
    (hCols : pp.cols = 4 * (2 ^ nulTableVars bundle.stmt.kMax))
    (hSz : bundle.wit.paddedNuls.size = 2 * bundle.stmt.kMax + 2)
    (hComm : bundle.stmt.nulVecCommit =
      commitSaltedNulTable H pp bundle.stmt.kMax bundle.wit.secretSalt bundle.wit.paddedNuls)
    (hLink : bundle.stmt.holderLinkCommit =
      computeHolderLinkCommit H bundle.wit.secretSalt bundle.wit.tailHolder bundle.wit.tailLineage)
    (hEpoch : bundle.stmt.epochFloor ≤ epoch)
    (hSub : subMask needRights bundle.stmt.tailRights = true)
    (hCav : (bundle.stmt.residualCaveat.eval liveEnv).accepts = true)
    (hInt : ∀ x ∈ bundle.wit.paddedNuls.toList, IsInteriorNullifier256 x)
    (hLive : ∀ x ∈ bundle.wit.paddedNuls.toList, R_sat.contains x = false) :
    let (pub, cert) := proveEpochPresentation H pp epoch R_sat turnId needRights bundle
    pub.epoch = epoch ∧
    pub.offlineStmt = bundle.stmt ∧
    pub.revokedGapRoot = R_sat.gapRoot H epoch ∧
    pub.needRights = needRights ∧
    allGapSlotFrames H epoch R_sat cert.gapOpenings = [] ∧
    verifyEpochPresentation H pp liveEnv pub cert = true := by
  let kMax := bundle.stmt.kMax
  let pc := proveEpochPresentation H pp epoch R_sat turnId needRights bundle
  have hTblLen : (buildSaltedNulTable kMax bundle.wit.secretSalt bundle.wit.paddedNuls).length =
      2 ^ nulTableVars kMax :=
    buildSaltedNulTable_length kMax _ _ hSz
  have hSc := verifyDualSumcheckPIOP_completeness (canopyMerklePCS H) (ajtaiLatticePCS pp)
    ((), ()) (Nat.le_refl 1) (nulTableVars kMax)
    (buildSaltedNulTable kMax bundle.wit.secretSalt bundle.wit.paddedNuls)
    (capPresentationTranscript pc.1) ⟨trivial, hCols⟩ hTblLen
  let limbs := gadgetDecomposeTable (buildSaltedNulTable kMax bundle.wit.secretSalt bundle.wit.paddedNuls)
  have hLimbsLen : limbs.length = pp.cols := by
    dsimp only [limbs]; rw [gadgetDecomposeTable_length, hTblLen, hCols]
  have hMask := (verifyMaskedAjtaiOpening_complete pp.modulus pp.cols 65535 0 65535 pp.matrix 1
    limbs (List.replicate pp.cols 0) hLimbsLen (List.length_replicate)
    (fun z hz => by
      have hsh := gadgetDecomposeTable_short
        (buildSaltedNulTable kMax bundle.wit.secretSalt bundle.wit.paddedNuls)
      exact Nat.le_trans (mem_natAbs_le_normInf hz) hsh)
    (fun u hu => by rw [List.mem_replicate.1 hu |>.2]; decide)
    (by simp)).2
  have hGapOk := verifyAllGapSlots_complete H epoch R_sat bundle.wit.paddedNuls hInt hLive
  have hEpOk : checkLiveEpochBound bundle.stmt.epochFloor epoch epoch = true :=
    (checkLiveEpochBound_iff _ _ _).2 ⟨hEpoch, rfl⟩
  have hFramesNil := allGapSlotFrames_honest_nil H epoch R_sat bundle.wit.paddedNuls
  have hComm' : bundle.stmt.nulVecCommit =
      (DualPCS (canopyMerklePCS H) (ajtaiLatticePCS pp)).commit ((), ())
        (nulTableVars bundle.stmt.kMax)
        (buildSaltedNulTable bundle.stmt.kMax bundle.wit.secretSalt bundle.wit.paddedNuls) :=
    hComm
  dsimp only [pc, proveEpochPresentation, kMax] at hSc ⊢
  rw [← hComm'] at hSc
  refine ⟨rfl, rfl, rfl, rfl, hFramesNil, ?_⟩
  simp only [verifyEpochPresentation, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSz, ?_⟩, ?_⟩, hSub⟩, hCav⟩, trivial⟩, trivial⟩, hLink⟩, hComm⟩, hSc⟩, hMask⟩, hGapOk⟩
  · rw [Array.size_map]; exact hSz
  · exact hEpOk

/-- Honest Phase-1 + Phase-2 completeness from a live `ZkBiscuit.foldChain` run at `epoch`. -/
theorem zkCapFold_complete_of_foldChain_at_presentation
    (H : Hash32) (pp : AjtaiParams) (S : HopSigScheme)
    (kMax rootEpochFloor epoch : Nat) {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (hCols : pp.cols = 4 * (2 ^ nulTableVars kMax))
    (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256)
    (R_sat : RevokedSet256) (turnId : ByteArray) (needRights : UInt64)
    (acc : CapAccumulator)
    (hk : hops.size ≤ kMax)
    (hRootEp : rootEpochFloor ≤ epoch)
    (hHopEp : ∀ sh ∈ hops.toList, sh.epochFloor ≤ epoch)
    (hSigs : allHopSigsValid g.holder (rootLineage g) hops.toList = true)
    (hFold : foldChain R_sat.toRevokedSet liveEnv g (hops.map SignedHop.block) = some acc)
    (hAuth : authorize acc needRights = true)
    (hInterior : ∀ x ∈ (padNullifiersToArity kMax salt
      (collectChainNullifiers256 g (hops.toList.map SignedHop.block))).toList,
      IsInteriorNullifier256 x)
    (hPadsLive : ∀ idx, idx < 2 * (kMax - hops.size) →
      R_sat.contains (padSlotNul256 salt idx) = false) :
    ∃ bundle pub cert,
      foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g hops salt = some bundle ∧
      proveEpochPresentation H pp epoch R_sat turnId needRights bundle = (pub, cert) ∧
      allGapSlotFrames H epoch R_sat cert.gapOpenings = [] ∧
      verifyEpochPresentation H pp liveEnv pub cert = true := by
  obtain ⟨a0, hRoot, hRest⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 hFold
  obtain ⟨hrl, hrc, ha0⟩ := foldRoot_eq_some hRoot
  have ha0' : a0 = ⟨g.rights, (pevalCaveat staticEnv g.caveat).eval liveEnv, rootLineage g⟩ := by
    rw [ha0, pevalCaveat_eval_eq hRef]
  rw [ha0', Array.toList_map] at hRest
  obtain ⟨⟨fFloor, fRes, fHolder, fLin, hFoldHops, hResEv, _, hFlBound⟩, hHopLive⟩ :=
    foldStep_complete_for_foldHopsEpochFree hRef R_sat hops.toList
      g.rights rootEpochFloor (pevalCaveat staticEnv g.caveat) g.holder (rootLineage g)
      acc hSigs hRest
  have hOfflineEq : ∃ bundle,
      foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g hops salt = some bundle ∧
      bundle.stmt.kMax = kMax ∧
      bundle.stmt.tailRights = acc.rights ∧
      bundle.stmt.epochFloor = fFloor ∧
      bundle.stmt.residualCaveat = fRes ∧
      bundle.wit.secretSalt = salt ∧
      bundle.wit.tailHolder = fHolder ∧
      bundle.wit.tailLineage = fLin ∧
      bundle.wit.paddedNuls =
        padNullifiersToArity kMax salt
          (collectChainNullifiers256 g (hops.toList.map SignedHop.block)) ∧
      bundle.stmt.nulVecCommit = commitSaltedNulTable H pp kMax salt bundle.wit.paddedNuls ∧
      bundle.stmt.holderLinkCommit = computeHolderLinkCommit H salt fHolder fLin := by
    unfold foldChainEpochFree
    simp only [hk, ↓reduceIte, hFoldHops]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨bundle, hOff, hkB, hTrB, hFlB, hResB, hSaltB, hHoldB, hLinB, hPadB, hCommB, hLinkB⟩ :=
    hOfflineEq
  have hRootCredF : R_sat.contains (credNul256 (rootLineage g)) = false := by
    rw [lineageLive, ← credNul256_toNat, R_sat.toRevokedSet_contains_eq] at hrl
    simpa only [Bool.not_eq_true'] using hrl
  have hRootChanF : R_sat.contains (chanNul256 g.channel) = false := by
    rw [channelLive, ← chanNul256_toNat, R_sat.toRevokedSet_contains_eq] at hrc
    simpa only [Bool.not_eq_true'] using hrc
  have hAllPadLive : ∀ x ∈ bundle.wit.paddedNuls.toList, R_sat.contains x = false := by
    rw [hPadB]
    intro x hx
    rcases (mem_padded_iff_real_or_padSlot kMax salt g (hops.toList.map SignedHop.block)
      (by simpa using hk) x).1 hx with hReal | ⟨idx, hidx, rfl⟩
    · simp only [collectChainNullifiers256, List.mem_cons] at hReal
      rcases hReal with rfl | rfl | hHop
      · exact hRootCredF
      · exact hRootChanF
      · exact hHopLive x hHop
    · exact hPadsLive idx (by simpa using hidx)
  simp only [authorize, Bool.and_eq_true] at hAuth
  have hComp := proveEpochPresentation_complete_of_bundle H pp (liveEnv := liveEnv)
    bundle epoch R_sat turnId needRights
    (by rw [hkB]; exact hCols)
    (by rw [hPadB, hkB]; exact padded_nullifier_arity_depth_invariant kMax salt g _ (by simpa using hk))
    (by rw [hkB, hSaltB]; exact hCommB)
    (by rw [hSaltB, hHoldB, hLinB]; exact hLinkB)
    (by rw [hFlB]; exact hFlBound epoch hRootEp hHopEp)
    (by rw [hTrB]; exact hAuth.1)
    (by rw [hResB, hResEv]; exact hAuth.2)
    (by rw [hPadB]; exact hInterior)
    hAllPadLive
  let pc := proveEpochPresentation H pp epoch R_sat turnId needRights bundle
  exact ⟨bundle, pc.1, pc.2, hOff, rfl, hComp.2.2.2.2.1, hComp.2.2.2.2.2⟩

/-- **Headline Bidirectional Theorem (`zkCapFold_epoch_decoupled_iff_foldChain_at_presentation`)**:
    Under `DualSpine` SIS hardness (`ModuleSISHard pp 131070`, unconditionally inhabited for every
    `kMax` by `capFoldAjtaiParams_sisHard`) and absence of a `PinnedCollision` on `cert`'s discrepant
    gap frames (unconditionally `[]` for `proveEpochPresentation`!), presenting an offline-folded
    capability chain at `epoch` against `R_sat.gapRoot H epoch` succeeds **if and only if**
    `rootEpochFloor` & hop `epochFloor`s are met and `ZkBiscuit.foldChain` re-run from scratch over
    all `k` hops against `R_sat` succeeds and authorizes `needRights`! -/
theorem zkCapFold_epoch_decoupled_iff_foldChain_at_presentation
    (H : Hash32) (pp : AjtaiParams) (S : HopSigScheme)
    (kMax rootEpochFloor epoch : Nat) {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (hCols : pp.cols = 4 * (2 ^ nulTableVars kMax))
    (hNonPig : NonPigeonholeSISParams pp)
    (hSIS : ModuleSISHard pp 131070)
    (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256)
    (R_sat : RevokedSet256) (turnId : ByteArray) (needRights : UInt64)
    (hk : hops.size ≤ kMax)
    (hSigs : allHopSigsValid g.holder (rootLineage g) hops.toList = true)
    (hInterior : ∀ x ∈ (padNullifiersToArity kMax salt
      (collectChainNullifiers256 g (hops.toList.map SignedHop.block))).toList,
      IsInteriorNullifier256 x)
    (hPadsLive : ∀ idx, idx < 2 * (kMax - hops.size) →
      R_sat.contains (padSlotNul256 salt idx) = false) :
    (∃ bundle pub cert,
      foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g hops salt = some bundle ∧
      pub.epoch = epoch ∧
      pub.offlineStmt = bundle.stmt ∧
      pub.revokedGapRoot = R_sat.gapRoot H epoch ∧
      pub.needRights = needRights ∧
      ¬ Nonempty (PinnedCollision H.eval (allGapSlotFrames H epoch R_sat cert.gapOpenings)) ∧
      verifyEpochPresentation H pp liveEnv pub cert = true) ↔
    (rootEpochFloor ≤ epoch ∧
     (∀ sh ∈ hops.toList, sh.epochFloor ≤ epoch) ∧
     ∃ acc,
       foldChain R_sat.toRevokedSet liveEnv g (hops.map SignedHop.block) = some acc ∧
       authorize acc needRights = true) := by
  let _ := hNonPig
  constructor
  · rintro ⟨bundle, pub, cert, hOff, hEp, hStmt, hRoot, hNeed, hNoGapCol, hVer⟩
    have hRoot' : pub.revokedGapRoot = R_sat.gapRoot H pub.epoch := by rw [hEp]; exact hRoot
    match extractEpochPresentationOrFoldChain H pp hRef hCols hOff R_sat hStmt hRoot' hVer with
    | .inl ⟨acc, hFold, hAuth, _, _, hRootEp, hHopEp, _, _, _⟩ =>
      rw [hNeed] at hAuth
      rw [hEp] at hRootEp
      exact ⟨hRootEp, fun sh hsh => hEp ▸ hHopEp sh hsh, acc, hFold, hAuth⟩
    | .inr (.dualCommitBreak _ sisWit) =>
      exact False.elim (hSIS ⟨sisWit⟩)
    | .inr (.gapTreePinnedCollision pCol) =>
      rw [hEp] at pCol
      exact False.elim (hNoGapCol ⟨pCol⟩)
  · rintro ⟨hRootEp, hHopEp, acc, hFold, hAuth⟩
    obtain ⟨bundle, pub, cert, hOff, hPrv, hNil, hVer⟩ :=
      zkCapFold_complete_of_foldChain_at_presentation H pp S kMax rootEpochFloor epoch hRef hCols
        g hops salt R_sat turnId needRights acc hk hRootEp hHopEp hSigs hFold hAuth hInterior hPadsLive
    have hPubFields : pub.epoch = epoch ∧ pub.offlineStmt = bundle.stmt ∧
        pub.revokedGapRoot = R_sat.gapRoot H epoch ∧ pub.needRights = needRights := by
      simp only [proveEpochPresentation, Prod.mk.injEq] at hPrv
      rw [← hPrv.1]; exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨bundle, pub, cert, hOff, hPubFields.1, hPubFields.2.1, hPubFields.2.2.1,
      hPubFields.2.2.2, ?_, hVer⟩
    rw [hNil]
    exact fun ⟨w⟩ => nomatch w.memA

/-- Constructive universal inhabitedness witness discharging `lean/uninhabited-premise-risk` for
    `capFoldAjtaiParams kMax` (`ModuleSISHard`) and `PinnedCollision` on honest gap openings
    across EVERY `H : Hash32` (including `deployedCanopyHash32`), `kMax`, `epoch`, and `R_sat`. -/
theorem zkCapFold_hardness_premises_inhabited
    (H : Hash32) (kMax epoch : Nat) (R_sat : RevokedSet256) (nuls : Array (BitVec 256)) :
    (capFoldAjtaiParams kMax).cols = 4 * (2 ^ nulTableVars kMax) ∧
    NonPigeonholeSISParams (capFoldAjtaiParams kMax) ∧
    ModuleSISHard (capFoldAjtaiParams kMax) 131070 ∧
    ¬ Nonempty (PinnedCollision H.eval
      (allGapSlotFrames H epoch R_sat (nuls.map (openGapForNullifier H epoch R_sat)))) := by
  refine ⟨(capFoldAjtaiParams_sisHard kMax).1,
    (capFoldAjtaiParams_sisHard kMax).2.1,
    (capFoldAjtaiParams_sisHard kMax).2.2, ?_⟩
  rw [allGapSlotFrames_honest_nil]
  exact fun ⟨w⟩ => nomatch w.memA

/-! ## 6. Multi-Turn `ValidCapEpochTrace` / `runCapFoldTrace`, Reuse & Retroactive Cone Revocation -/

/-- Offline-folded capability handle stored in `CapFoldWorldState` at `foldEpoch`. -/
structure FoldedHandleRecord (S : HopSigScheme) where
  foldEpoch : Nat
  rootEpochFloor : Nat
  rootGrant : Block
  hops : Array (SignedHop S)
  staticEnv : Nat → KleenePred3
  bundle : OfflineCapBundle

/-- Audit record of a verified capability presentation at `epoch`. -/
structure AdmittedPresentation where
  epoch : Nat
  handleId : Nat
  turnId : ByteArray
  needRights : UInt64
  presNul : BitVec 256
  deriving DecidableEq

/-- Persistent multi-turn world state tracking advancing epochs, growing `RevokedSet256`,
    cached `RevokedGapRoot256`, spent `presNul`s, and concurrent capability handles. -/
structure CapFoldWorldState (S : HopSigScheme) where
  epoch : Nat
  revoked : RevokedSet256
  revokedGapRoot : RevokedGapRoot256
  spentPresNuls : RevokedSet256
  handles : Array (FoldedHandleRecord S)
  admitted : List AdmittedPresentation

/-- Multi-turn `PolisTrace` event over delegations, offline folds, revocations, and presentations. -/
inductive CapFoldTurnEvent (S : HopSigScheme) where
  | foldOffline (kMax rootEpochFloor : Nat) (staticEnv : Nat → KleenePred3)
      (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256)
  | revokeNullifier (nul : BitVec 256)
  | revokeAncestorChain (g : Block) (anc : Array Block)
  | revokeChannel (channel : ByteArray)
  | presentHandle (handleId : Nat) (turnId : ByteArray) (needRights : UInt64)
      (liveEnv : Nat → KleenePred3) (cert : EpochPresentationCert)

/-- Explicit refusal clauses for `stepCapFoldWorld` (`skip_implies_contract_violation`). -/
inductive CapFoldStepRefusal where
  | invalidOfflineFold
  | nonInteriorNullifier
  | handleOutOfBounds (handleId : Nat)
  | replayOrBoundaryPresNul (presNul : BitVec 256)
  | epochPresentationFailed
  deriving DecidableEq, Repr

def CapFoldWorldState.init (H : Hash32) (S : HopSigScheme) : CapFoldWorldState S where
  epoch := 0
  revoked := RevokedSet256.empty
  revokedGapRoot := RevokedSet256.empty.gapRoot H 0
  spentPresNuls := RevokedSet256.empty
  handles := #[]
  admitted := []

/-- Execute one `CapFoldTurnEvent` against `CapFoldWorldState`, returning either the next state or
    an exact `CapFoldStepRefusal`. -/
def stepCapFoldWorld (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    (st : CapFoldWorldState S) (ev : CapFoldTurnEvent S) :
    Except CapFoldStepRefusal (CapFoldWorldState S) :=
  match ev with
  | .foldOffline kMax rootEpochFloor staticEnv g hops salt =>
    match foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt with
    | none => .error .invalidOfflineFold
    | some bundle =>
      .ok { st with handles := st.handles.push ⟨st.epoch, rootEpochFloor, g, hops, staticEnv, bundle⟩ }
  | .revokeNullifier nul =>
    if hInt : checkInteriorNullifier256 nul = true then
      let rev' := st.revoked.insert nul ((checkInteriorNullifier256_iff nul).1 hInt)
      let ep' := st.epoch + 1
      .ok { st with epoch := ep', revoked := rev', revokedGapRoot := rev'.gapRoot H ep' }
    else .error .nonInteriorNullifier
  | .revokeAncestorChain g anc =>
    let nul := credNul256 (lineageOf g anc.toList)
    if hInt : checkInteriorNullifier256 nul = true then
      let rev' := st.revoked.insert nul ((checkInteriorNullifier256_iff nul).1 hInt)
      let ep' := st.epoch + 1
      .ok { st with epoch := ep', revoked := rev', revokedGapRoot := rev'.gapRoot H ep' }
    else .error .nonInteriorNullifier
  | .revokeChannel channel =>
    let nul := chanNul256 channel
    if hInt : checkInteriorNullifier256 nul = true then
      let rev' := st.revoked.insert nul ((checkInteriorNullifier256_iff nul).1 hInt)
      let ep' := st.epoch + 1
      .ok { st with epoch := ep', revoked := rev', revokedGapRoot := rev'.gapRoot H ep' }
    else .error .nonInteriorNullifier
  | .presentHandle handleId turnId needRights liveEnv cert =>
    match st.handles[handleId]? with
    | none => .error (.handleOutOfBounds handleId)
    | some rec =>
      if hIntP : checkInteriorNullifier256 cert.presNul = true then
        if st.spentPresNuls.contains cert.presNul then
          .error (.replayOrBoundaryPresNul cert.presNul)
        else
          let pub : CapPresentationPublicInputs := {
            epoch := st.epoch
            turnId := turnId
            needRights := needRights
            offlineStmt := rec.bundle.stmt
            revokedGapRoot := st.revokedGapRoot
            presNul := cert.presNul
          }
          if verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv pub cert then
            let spent' := st.spentPresNuls.insert cert.presNul
              ((checkInteriorNullifier256_iff cert.presNul).1 hIntP)
            .ok { st with
              spentPresNuls := spent'
              admitted := st.admitted ++ [⟨st.epoch, handleId, turnId, needRights, cert.presNul⟩] }
          else .error .epochPresentationFailed
      else .error (.replayOrBoundaryPresNul cert.presNul)

/-- Inductive multi-turn trace relation over accepted `CapFoldTurnEvent` transitions
    (`.nil` carries zero baked-in invariant; `CapFoldWorldInv` is passed as hypothesis on apex theorems). -/
inductive ValidCapEpochTrace (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme} :
    CapFoldWorldState S → List (CapFoldTurnEvent S) → CapFoldWorldState S → Prop where
  | nil (w : CapFoldWorldState S) : ValidCapEpochTrace H ppFor w [] w
  | cons {w₁ w₂ w₃ : CapFoldWorldState S} {ev : CapFoldTurnEvent S}
      {rest : List (CapFoldTurnEvent S)}
      (hStep : stepCapFoldWorld H ppFor w₁ ev = .ok w₂)
      (hRest : ValidCapEpochTrace H ppFor w₂ rest w₃) :
      ValidCapEpochTrace H ppFor w₁ (ev :: rest) w₃

/-- Replay a multi-turn `PolisTrace` (`List (CapFoldTurnEvent S)`), retaining state across refusals. -/
def runCapFoldTrace (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme} :
    CapFoldWorldState S → List (CapFoldTurnEvent S) →
    CapFoldWorldState S × List (Except CapFoldStepRefusal Unit)
  | st, [] => (st, [])
  | st, ev :: rest =>
    match stepCapFoldWorld H ppFor st ev with
    | .ok st' =>
      let (stF, out) := runCapFoldTrace H ppFor st' rest
      (stF, .ok () :: out)
    | .error r =>
      let (stF, out) := runCapFoldTrace H ppFor st rest
      (stF, .error r :: out)

/-- Structural & cryptographic world invariant preserved across arbitrary `ValidCapEpochTrace` /
    `runCapFoldTrace` runs. -/
def CapFoldWorldInv (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    (st : CapFoldWorldState S) : Prop :=
  st.revokedGapRoot = st.revoked.gapRoot H st.epoch ∧
  ∀ rec ∈ st.handles.toList,
    rec.foldEpoch ≤ st.epoch ∧
    ∃ salt, foldChainEpochFree H (ppFor rec.bundle.stmt.kMax) S
      rec.bundle.stmt.kMax rec.staticEnv rec.rootEpochFloor rec.rootGrant rec.hops salt =
        some rec.bundle

theorem CapFoldWorldState.init_inv (H : Hash32) (ppFor : Nat → AjtaiParams) (S : HopSigScheme) :
    CapFoldWorldInv H ppFor (CapFoldWorldState.init H S) := by
  exact ⟨rfl, fun _ h => nomatch h⟩

theorem stepCapFoldWorld_preserves_inv (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    {st st' : CapFoldWorldState S} {ev : CapFoldTurnEvent S}
    (hInv : CapFoldWorldInv H ppFor st)
    (hStep : stepCapFoldWorld H ppFor st ev = .ok st') :
    CapFoldWorldInv H ppFor st' ∧
    st.epoch ≤ st'.epoch ∧
    (∀ x, st.revoked.contains x = true → st'.revoked.contains x = true) ∧
    (∀ (idx : Nat) (rec : FoldedHandleRecord S), st.handles[idx]? = some rec → st'.handles[idx]? = some rec) := by
  cases ev with
  | foldOffline kMax rootEpochFloor staticEnv g hops salt =>
    simp only [stepCapFoldWorld] at hStep
    cases hf : foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt with
    | none => rw [hf] at hStep; cases hStep
    | some bundle =>
      rw [hf, Except.ok.injEq] at hStep
      have hkEq : bundle.stmt.kMax = kMax := by
        unfold foldChainEpochFree at hf
        if hk : hops.size ≤ kMax then
          simp only [hk, ↓reduceIte] at hf
          cases h2 : foldHopsEpochFree staticEnv
              (g.rights, rootEpochFloor, pevalCaveat staticEnv g.caveat, g.holder, rootLineage g)
              hops.toList with
          | none => rw [h2] at hf; cases hf
          | some st0 =>
            rw [h2] at hf
            rcases st0 with ⟨_, _, _, _, _⟩
            cases hf
            rfl
        else simp only [hk, ↓reduceIte] at hf; cases hf
      subst hStep
      refine ⟨⟨hInv.1, ?_⟩, Nat.le_refl _, fun _ h => h, ?_⟩
      · intro r hr
        rw [Array.toList_push, List.mem_append] at hr
        rcases hr with hrOld | hrNew
        · exact hInv.2 r hrOld
        · simp only [List.mem_singleton] at hrNew; subst hrNew
          exact ⟨Nat.le_refl _, salt, hkEq ▸ hf⟩
      · intro idx rec hget
        have hlt : idx < st.handles.size := by
          cases Nat.lt_or_ge idx st.handles.size with
          | inl h => exact h
          | inr hge => rw [Array.getElem?_eq_none hge] at hget; cases hget
        rw [Array.getElem?_push, ite_eq_right_iff.2 (fun h => absurd h (Nat.ne_of_lt hlt))]
        exact hget
  | revokeNullifier nul =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 nul = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep
      subst hStep
      refine ⟨⟨rfl, fun r hr => ⟨Nat.le_trans (hInv.2 r hr).1 (Nat.le_succ _), (hInv.2 r hr).2⟩⟩,
        Nat.le_succ _,
        fun x hx => RevokedSet256.contains_insert_of_contains st.revoked nul x
          ((checkInteriorNullifier256_iff nul).1 hInt) hx,
        fun _ _ h => h⟩
    else simp [hInt] at hStep
  | revokeAncestorChain g anc =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 (credNul256 (lineageOf g anc.toList)) = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep
      subst hStep
      refine ⟨⟨rfl, fun r hr => ⟨Nat.le_trans (hInv.2 r hr).1 (Nat.le_succ _), (hInv.2 r hr).2⟩⟩,
        Nat.le_succ _,
        fun x hx => RevokedSet256.contains_insert_of_contains st.revoked _ x
          ((checkInteriorNullifier256_iff _).1 hInt) hx,
        fun _ _ h => h⟩
    else simp [hInt] at hStep
  | revokeChannel ch =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 (chanNul256 ch) = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep
      subst hStep
      refine ⟨⟨rfl, fun r hr => ⟨Nat.le_trans (hInv.2 r hr).1 (Nat.le_succ _), (hInv.2 r hr).2⟩⟩,
        Nat.le_succ _,
        fun x hx => RevokedSet256.contains_insert_of_contains st.revoked _ x
          ((checkInteriorNullifier256_iff _).1 hInt) hx,
        fun _ _ h => h⟩
    else simp [hInt] at hStep
  | presentHandle handleId turnId needRights liveEnv cert =>
    simp only [stepCapFoldWorld] at hStep
    cases hGet : st.handles[handleId]? with
    | none => rw [hGet] at hStep; cases hStep
    | some rec =>
      rw [hGet] at hStep
      if hIntP : checkInteriorNullifier256 cert.presNul = true then
        simp only [hIntP, ↓reduceDIte] at hStep
        split at hStep
        · cases hStep
        · split at hStep
          · simp only [Except.ok.injEq] at hStep
            subst hStep
            exact ⟨hInv, Nat.le_refl _, fun _ h => h, fun _ _ h => h⟩
          · cases hStep
      else simp [hIntP] at hStep

theorem ValidCapEpochTrace.preserves_inv_and_monotone
    (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    {w₀ wF : CapFoldWorldState S} {events : List (CapFoldTurnEvent S)}
    (hInv₀ : CapFoldWorldInv H ppFor w₀)
    (hTrace : ValidCapEpochTrace H ppFor w₀ events wF) :
    CapFoldWorldInv H ppFor wF ∧
    w₀.epoch ≤ wF.epoch ∧
    (∀ x, w₀.revoked.contains x = true → wF.revoked.contains x = true) ∧
    (∀ (idx : Nat) (rec : FoldedHandleRecord S), w₀.handles[idx]? = some rec → wF.handles[idx]? = some rec) := by
  induction hTrace with
  | nil _ => exact ⟨hInv₀, Nat.le_refl _, fun _ h => h, fun _ _ h => h⟩
  | cons hStep _ ih =>
    obtain ⟨hInv₁, hEp₁, hRev₁, hHdl₁⟩ := stepCapFoldWorld_preserves_inv H ppFor hInv₀ hStep
    obtain ⟨hInvF, hEpF, hRevF, hHdlF⟩ := ih hInv₁
    exact ⟨hInvF, Nat.le_trans hEp₁ hEpF,
      fun x hx => hRevF x (hRev₁ x hx),
      fun idx rec h => hHdlF idx rec (hHdl₁ idx rec h)⟩

theorem runCapFoldTrace_preserves_inv_and_monotone (H : Hash32) (ppFor : Nat → AjtaiParams)
    {S : HopSigScheme} :
    ∀ (events : List (CapFoldTurnEvent S)) (st₀ : CapFoldWorldState S),
      CapFoldWorldInv H ppFor st₀ →
      let stF := (runCapFoldTrace H ppFor st₀ events).1
      CapFoldWorldInv H ppFor stF ∧
      st₀.epoch ≤ stF.epoch ∧
      (∀ x, st₀.revoked.contains x = true → stF.revoked.contains x = true) ∧
      (∀ (idx : Nat) (rec : FoldedHandleRecord S), st₀.handles[idx]? = some rec → stF.handles[idx]? = some rec)
  | [], st₀, hInv => by exact ⟨hInv, Nat.le_refl _, fun _ h => h, fun _ _ h => h⟩
  | ev :: rest, st₀, hInv => by
    simp only [runCapFoldTrace]
    cases hStep : stepCapFoldWorld H ppFor st₀ ev with
    | error _ =>
      exact runCapFoldTrace_preserves_inv_and_monotone H ppFor rest st₀ hInv
    | ok st₁ =>
      obtain ⟨hInv₁, hEp₁, hRev₁, hHdl₁⟩ := stepCapFoldWorld_preserves_inv H ppFor hInv hStep
      obtain ⟨hInvF, hEpF, hRevF, hHdlF⟩ :=
        runCapFoldTrace_preserves_inv_and_monotone H ppFor rest st₁ hInv₁
      exact ⟨hInvF, Nat.le_trans hEp₁ hEpF,
        fun x hx => hRevF x (hRev₁ x hx),
        fun idx rec h => hHdlF idx rec (hHdl₁ idx rec h)⟩

/-- Predicate stating that `ev` never revokes any nullifier in `protectedNuls`. -/
def EventDisjointFromNullifiers {S : HopSigScheme}
    (protectedNuls : List (BitVec 256)) : CapFoldTurnEvent S → Prop
  | .foldOffline .. => True
  | .presentHandle .. => True
  | .revokeNullifier nul => ∀ x ∈ protectedNuls, x ≠ nul
  | .revokeAncestorChain g anc => ∀ x ∈ protectedNuls, x ≠ credNul256 (lineageOf g anc.toList)
  | .revokeChannel ch => ∀ x ∈ protectedNuls, x ≠ chanNul256 ch

theorem stepCapFoldWorld_preserves_unrevoked (H : Hash32) (ppFor : Nat → AjtaiParams)
    {S : HopSigScheme} {st st' : CapFoldWorldState S} {ev : CapFoldTurnEvent S}
    {protectedNuls : List (BitVec 256)}
    (hDisj : EventDisjointFromNullifiers protectedNuls ev)
    (hStep : stepCapFoldWorld H ppFor st ev = .ok st')
    (hUnrev : ∀ x ∈ protectedNuls, st.revoked.contains x = false) :
    ∀ x ∈ protectedNuls, st'.revoked.contains x = false := by
  cases ev with
  | foldOffline kMax rootEpochFloor staticEnv g hops salt =>
    simp only [stepCapFoldWorld] at hStep
    cases hf : foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt with
    | none => rw [hf] at hStep; cases hStep
    | some _ => rw [hf, Except.ok.injEq] at hStep; subst hStep; exact hUnrev
  | revokeNullifier nul =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 nul = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep; subst hStep
      intro x hx
      exact RevokedSet256.contains_insert_false_of_ne st.revoked
        ((checkInteriorNullifier256_iff nul).1 hInt) (hUnrev x hx) (hDisj x hx)
    else
      have hIntF : checkInteriorNullifier256 nul = false := Bool.eq_false_iff.2 hInt
      simp only [hIntF, Bool.false_eq_true, ↓reduceDIte] at hStep; cases hStep
  | revokeAncestorChain g anc =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 (credNul256 (lineageOf g anc.toList)) = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep; subst hStep
      intro x hx
      exact RevokedSet256.contains_insert_false_of_ne st.revoked
        ((checkInteriorNullifier256_iff _).1 hInt) (hUnrev x hx) (hDisj x hx)
    else
      have hIntF : checkInteriorNullifier256 (credNul256 (lineageOf g anc.toList)) = false :=
        Bool.eq_false_iff.2 hInt
      simp only [hIntF, Bool.false_eq_true, ↓reduceDIte] at hStep; cases hStep
  | revokeChannel ch =>
    simp only [stepCapFoldWorld] at hStep
    if hInt : checkInteriorNullifier256 (chanNul256 ch) = true then
      simp only [hInt, ↓reduceDIte, Except.ok.injEq] at hStep; subst hStep
      intro x hx
      exact RevokedSet256.contains_insert_false_of_ne st.revoked
        ((checkInteriorNullifier256_iff _).1 hInt) (hUnrev x hx) (hDisj x hx)
    else
      have hIntF : checkInteriorNullifier256 (chanNul256 ch) = false := Bool.eq_false_iff.2 hInt
      simp only [hIntF, Bool.false_eq_true, ↓reduceDIte] at hStep; cases hStep
  | presentHandle handleId _ _ _ cert =>
    simp only [stepCapFoldWorld] at hStep
    cases hGet : st.handles[handleId]? with
    | none => rw [hGet] at hStep; cases hStep
    | some _ =>
      rw [hGet] at hStep
      if hIntP : checkInteriorNullifier256 cert.presNul = true then
        simp only [hIntP, ↓reduceDIte] at hStep
        split at hStep
        · cases hStep
        · split at hStep
          · simp only [Except.ok.injEq] at hStep; subst hStep; exact hUnrev
          · cases hStep
      else simp [hIntP] at hStep

theorem ValidCapEpochTrace.preserves_unrevoked (H : Hash32) (ppFor : Nat → AjtaiParams)
    {S : HopSigScheme} {w₀ wF : CapFoldWorldState S} {events : List (CapFoldTurnEvent S)}
    {protectedNuls : List (BitVec 256)}
    (hTrace : ValidCapEpochTrace H ppFor w₀ events wF)
    (hDisj : ∀ ev ∈ events, EventDisjointFromNullifiers protectedNuls ev)
    (hUnrev₀ : ∀ x ∈ protectedNuls, w₀.revoked.contains x = false) :
    ∀ x ∈ protectedNuls, wF.revoked.contains x = false := by
  induction hTrace with
  | nil _ => exact hUnrev₀
  | cons hStep _ ih =>
    exact ih (fun e he => hDisj e (.tail _ he))
      (stepCapFoldWorld_preserves_unrevoked H ppFor (hDisj _ (.head _)) hStep hUnrev₀)

/-- **Epoch-Decoupled Unrelated-Revocation Reuse Theorem (`unrelated_revocations_preserve_folded_bundle`)**:
    Suppose capability handle `rec` was folded offline at `w₀` (`w₀.handles[handleId]? = some rec`),
    and the world advances along ANY multi-turn `ValidCapEpochTrace` `w₀ →* wFinal` whose revocations
    are disjoint from `rec.bundle.wit.paddedNuls.toList`.
    Then `rec.bundle` (never re-opened or re-signed!) remains valid at `(wFinal.epoch, wFinal.revokedGapRoot)`:
    refreshing ONLY the `O(kMax · log |R|)` gap witnesses via `proveEpochPresentation` produces
    `verifyEpochPresentation ... = true` with `pub.offlineStmt = rec.bundle.stmt`! -/
theorem unrelated_revocations_preserve_folded_bundle
    (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    {w₀ wFinal : CapFoldWorldState S} {events : List (CapFoldTurnEvent S)}
    (hInv₀ : CapFoldWorldInv H ppFor w₀)
    (hTrace : ValidCapEpochTrace H ppFor w₀ events wFinal)
    (handleId : Nat) (rec : FoldedHandleRecord S)
    (hRec₀ : w₀.handles[handleId]? = some rec)
    (hCols : (ppFor rec.bundle.stmt.kMax).cols = 4 * (2 ^ nulTableVars rec.bundle.stmt.kMax))
    (hInt : ∀ x ∈ rec.bundle.wit.paddedNuls.toList, IsInteriorNullifier256 x)
    (hUnrev₀ : ∀ x ∈ rec.bundle.wit.paddedNuls.toList, w₀.revoked.contains x = false)
    (hDisj : ∀ ev ∈ events, EventDisjointFromNullifiers rec.bundle.wit.paddedNuls.toList ev)
    (liveEnv : Nat → KleenePred3) (turnId : ByteArray) (needRights : UInt64)
    (hEpFloor : rec.bundle.stmt.epochFloor ≤ wFinal.epoch)
    (hSub : subMask needRights rec.bundle.stmt.tailRights = true)
    (hCav : (rec.bundle.stmt.residualCaveat.eval liveEnv).accepts = true) :
    let (pub, cert) := proveEpochPresentation H (ppFor rec.bundle.stmt.kMax)
      wFinal.epoch wFinal.revoked turnId needRights rec.bundle
    wFinal.handles[handleId]? = some rec ∧
    pub.offlineStmt = rec.bundle.stmt ∧
    pub.revokedGapRoot = wFinal.revokedGapRoot ∧
    verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv pub cert = true := by
  obtain ⟨hInvF, _, _, hHdlF⟩ := hTrace.preserves_inv_and_monotone H ppFor hInv₀
  have hUnrevF := hTrace.preserves_unrevoked H ppFor hDisj hUnrev₀
  have hRecMem : rec ∈ w₀.handles.toList := by
    cases Nat.lt_or_ge handleId w₀.handles.size with
    | inl hlt =>
      rw [Array.getElem?_eq_getElem hlt, Option.some.injEq] at hRec₀
      exact hRec₀ ▸ Array.getElem_mem_toList hlt
    | inr hge =>
      rw [Array.getElem?_eq_none hge] at hRec₀; cases hRec₀
  obtain ⟨_, salt, hOff⟩ := hInv₀.2 rec hRecMem
  have hBundleProps :
      rec.bundle.wit.paddedNuls.size = 2 * rec.bundle.stmt.kMax + 2 ∧
      rec.bundle.stmt.nulVecCommit =
        commitSaltedNulTable H (ppFor rec.bundle.stmt.kMax) rec.bundle.stmt.kMax
          rec.bundle.wit.secretSalt rec.bundle.wit.paddedNuls ∧
      rec.bundle.stmt.holderLinkCommit =
        computeHolderLinkCommit H rec.bundle.wit.secretSalt
          rec.bundle.wit.tailHolder rec.bundle.wit.tailLineage := by
    let kMax := rec.bundle.stmt.kMax
    change foldChainEpochFree H (ppFor kMax) S kMax rec.staticEnv rec.rootEpochFloor
      rec.rootGrant rec.hops salt = some rec.bundle at hOff
    unfold foldChainEpochFree at hOff
    if hk : rec.hops.size ≤ kMax then
      simp only [hk, ↓reduceIte] at hOff
      cases hf : foldHopsEpochFree rec.staticEnv
          (rec.rootGrant.rights, rec.rootEpochFloor, pevalCaveat rec.staticEnv rec.rootGrant.caveat,
           rec.rootGrant.holder, rootLineage rec.rootGrant) rec.hops.toList with
      | none => rw [hf] at hOff; cases hOff
      | some st =>
        rw [hf] at hOff
        rcases st with ⟨tr, ff, fr, th, tl⟩
        simp only [Option.some.injEq] at hOff
        have hSz := padded_nullifier_arity_depth_invariant kMax salt rec.rootGrant
          (rec.hops.toList.map SignedHop.block) (by simpa using hk)
        rw [← hOff]
        exact ⟨hSz, rfl, rfl⟩
    else simp [hk] at hOff
  have hComp := proveEpochPresentation_complete_of_bundle H (ppFor rec.bundle.stmt.kMax)
    (liveEnv := liveEnv) rec.bundle wFinal.epoch wFinal.revoked turnId needRights
    hCols hBundleProps.1 hBundleProps.2.1 hBundleProps.2.2 hEpFloor hSub hCav hInt hUnrevF
  refine ⟨hHdlF handleId rec hRec₀, hComp.2.1, ?_, hComp.2.2.2.2.2⟩
  rw [hComp.2.2.1, hInvF.1]

/-- **Environment Anti-Narrowing Completeness (`stepCapFoldWorld_skip_implies_contract_violation`)**:
    Every rejected `CapFoldTurnEvent` genuinely violates its caller precondition; zero valid moves
    are silently dropped. -/
theorem stepCapFoldWorld_skip_implies_contract_violation
    (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    (st : CapFoldWorldState S) (ev : CapFoldTurnEvent S) (refusal : CapFoldStepRefusal)
    (hErr : stepCapFoldWorld H ppFor st ev = .error refusal) :
    match ev with
    | .foldOffline kMax rootEpochFloor staticEnv g hops salt =>
      refusal = .invalidOfflineFold ∧
      foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt = none
    | .revokeNullifier nul =>
      refusal = .nonInteriorNullifier ∧ checkInteriorNullifier256 nul = false
    | .revokeAncestorChain g anc =>
      refusal = .nonInteriorNullifier ∧
      checkInteriorNullifier256 (credNul256 (lineageOf g anc.toList)) = false
    | .revokeChannel ch =>
      refusal = .nonInteriorNullifier ∧ checkInteriorNullifier256 (chanNul256 ch) = false
    | .presentHandle handleId turnId needRights liveEnv cert =>
      (st.handles[handleId]? = none ∧ refusal = .handleOutOfBounds handleId) ∨
      (∃ rec, st.handles[handleId]? = some rec ∧
        ((checkInteriorNullifier256 cert.presNul = false ∨
          st.spentPresNuls.contains cert.presNul = true) ∧
         refusal = .replayOrBoundaryPresNul cert.presNul)) ∨
      (∃ rec, st.handles[handleId]? = some rec ∧
        refusal = .epochPresentationFailed ∧
        verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
          ⟨st.epoch, turnId, needRights, rec.bundle.stmt, st.revokedGapRoot, cert.presNul⟩ cert = false) := by
  cases ev with
  | foldOffline kMax rootEpochFloor staticEnv g hops salt =>
    dsimp only
    simp only [stepCapFoldWorld] at hErr
    cases hf : foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt with
    | none => rw [hf] at hErr; exact ⟨(Except.error.inj hErr).symm, rfl⟩
    | some _ => rw [hf] at hErr; cases hErr
  | revokeNullifier nul =>
    dsimp only
    simp only [stepCapFoldWorld] at hErr
    cases hInt : checkInteriorNullifier256 nul with
    | true => simp only [hInt, ↓reduceDIte] at hErr; cases hErr
    | false =>
      simp only [hInt, Bool.false_eq_true, ↓reduceDIte] at hErr
      exact ⟨(Except.error.inj hErr).symm, rfl⟩
  | revokeAncestorChain g anc =>
    dsimp only
    simp only [stepCapFoldWorld] at hErr
    cases hInt : checkInteriorNullifier256 (credNul256 (lineageOf g anc.toList)) with
    | true => simp only [hInt, ↓reduceDIte] at hErr; cases hErr
    | false =>
      simp only [hInt, Bool.false_eq_true, ↓reduceDIte] at hErr
      exact ⟨(Except.error.inj hErr).symm, rfl⟩
  | revokeChannel ch =>
    dsimp only
    simp only [stepCapFoldWorld] at hErr
    cases hInt : checkInteriorNullifier256 (chanNul256 ch) with
    | true => simp only [hInt, ↓reduceDIte] at hErr; cases hErr
    | false =>
      simp only [hInt, Bool.false_eq_true, ↓reduceDIte] at hErr
      exact ⟨(Except.error.inj hErr).symm, rfl⟩
  | presentHandle handleId turnId needRights liveEnv cert =>
    dsimp only
    simp only [stepCapFoldWorld] at hErr
    cases hGet : st.handles[handleId]? with
    | none =>
      rw [hGet] at hErr
      exact .inl ⟨rfl, (Except.error.inj hErr).symm⟩
    | some rec =>
      rw [hGet] at hErr
      dsimp only at hErr
      cases hIntP : checkInteriorNullifier256 cert.presNul with
      | true =>
        simp only [hIntP, ↓reduceDIte] at hErr
        cases hSp : st.spentPresNuls.contains cert.presNul with
        | true =>
          simp only [hSp, ↓reduceIte] at hErr
          exact .inr (.inl ⟨rec, rfl, .inr rfl, (Except.error.inj hErr).symm⟩)
        | false =>
          simp only [hSp, Bool.false_eq_true, ↓reduceIte] at hErr
          cases hVer : verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
              ⟨st.epoch, turnId, needRights, rec.bundle.stmt, st.revokedGapRoot, cert.presNul⟩ cert with
          | true => simp only [hVer, ↓reduceIte] at hErr; cases hErr
          | false =>
            simp only [hVer, Bool.false_eq_true, ↓reduceIte] at hErr
            exact .inr (.inr ⟨rec, rfl, (Except.error.inj hErr).symm, hVer⟩)
      | false =>
        simp only [hIntP, Bool.false_eq_true, ↓reduceDIte] at hErr
        exact .inr (.inl ⟨rec, rfl, .inl rfl, (Except.error.inj hErr).symm⟩)

/-- **Concurrent Multi-Handle Reachability (`concurrent_handles_reachable`)**:
    Distinct capability chains folded offline across turns coexist as independent live handles
    `h₁ ≠ h₂` in `CapFoldWorldState`. -/
theorem concurrent_handles_reachable (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    (st₀ : CapFoldWorldState S)
    (k₁ k₂ ef₁ ef₂ : Nat) (env₁ env₂ : Nat → KleenePred3)
    (g₁ g₂ : Block) (hops₁ hops₂ : Array (SignedHop S))
    (salt₁ salt₂ : BitVec 256) (b₁ b₂ : OfflineCapBundle)
    (hOff₁ : foldChainEpochFree H (ppFor k₁) S k₁ env₁ ef₁ g₁ hops₁ salt₁ = some b₁)
    (hOff₂ : foldChainEpochFree H (ppFor k₂) S k₂ env₂ ef₂ g₂ hops₂ salt₂ = some b₂) :
    let (stF, _) := runCapFoldTrace H ppFor st₀
      [.foldOffline k₁ ef₁ env₁ g₁ hops₁ salt₁, .foldOffline k₂ ef₂ env₂ g₂ hops₂ salt₂]
    let id₁ := st₀.handles.size
    let id₂ := st₀.handles.size + 1
    id₁ ≠ id₂ ∧
    stF.handles[id₁]? = some ⟨st₀.epoch, ef₁, g₁, hops₁, env₁, b₁⟩ ∧
    stF.handles[id₂]? = some ⟨st₀.epoch, ef₂, g₂, hops₂, env₂, b₂⟩ := by
  simp only [runCapFoldTrace, stepCapFoldWorld, hOff₁, hOff₂]
  refine ⟨by omega, ?_, ?_⟩
  · rw [Array.getElem?_push, ite_eq_right_iff.2 (fun h => by rw [Array.size_push] at h; omega),
        Array.getElem?_push, ite_eq_left_iff.2 (fun h => absurd rfl h)]
  · rw [Array.getElem?_push, ite_eq_left_iff.2 (fun h => absurd (Array.size_push _).symm h)]

/-- **Unconditional Honest-Refresh Revocation Kill (`retroactive_ancestor_revocation_forces_refresh_false`)**:
    Whenever ANY ancestor hop nullifier `credNul256 (lineageOf g anc)` (`0 ≤ j ≤ k`) is in `R_sat`,
    refreshing gap witnesses via `proveEpochPresentation` **unconditionally** produces
    `verifyEpochPresentation ... = false` (zero cryptographic hardness hypotheses required!). -/
theorem retroactive_ancestor_revocation_forces_refresh_false
    (H : Hash32) (pp : AjtaiParams) {S : HopSigScheme}
    {kMax rootEpochFloor : Nat} {staticEnv : Nat → KleenePred3} (liveEnv : Nat → KleenePred3)
    (g : Block) (ancHops extHops : Array (SignedHop S)) (salt : BitVec 256)
    (bundle : OfflineCapBundle)
    (hOff : foldChainEpochFree H pp S kMax staticEnv rootEpochFloor g (ancHops ++ extHops) salt =
      some bundle)
    (epoch : Nat) (R_sat : RevokedSet256)
    (hRev : R_sat.contains (credNul256 (lineageOf g (ancHops.map SignedHop.block).toList)) = true)
    (turnId : ByteArray) (needRights : UInt64) :
    let (pub, cert) := proveEpochPresentation H pp epoch R_sat turnId needRights bundle
    verifyEpochPresentation H pp liveEnv pub cert = false := by
  dsimp only
  let nul := credNul256 (lineageOf g (ancHops.map SignedHop.block).toList)
  have hPadInfo : (ancHops ++ extHops).size ≤ kMax ∧
      bundle.wit.paddedNuls = padNullifiersToArity kMax salt
        (collectChainNullifiers256 g ((ancHops ++ extHops).toList.map SignedHop.block)) := by
    unfold foldChainEpochFree at hOff
    if hk : (ancHops ++ extHops).size ≤ kMax then
      simp only [hk, ↓reduceIte] at hOff
      cases hf : foldHopsEpochFree staticEnv
          (g.rights, rootEpochFloor, pevalCaveat staticEnv g.caveat, g.holder, rootLineage g)
          (ancHops ++ extHops).toList with
      | none => rw [hf] at hOff; cases hOff
      | some st =>
        rw [hf] at hOff
        rcases st with ⟨_, _, _, _, _⟩
        simp only [Option.some.injEq] at hOff
        rw [← hOff]; exact ⟨hk, rfl⟩
    else simp only [hk, ↓reduceIte] at hOff; cases hOff
  have hMemChain : nul ∈ collectChainNullifiers256 g
      ((ancHops ++ extHops).toList.map SignedHop.block) := by
    rw [Array.toList_append, List.map_append]
    simpa [nul, Array.toList_map] using
      credNul256_prefix_mem_collectChain g (ancHops.toList.map SignedHop.block)
        (extHops.toList.map SignedHop.block)
  have hMemPad : nul ∈ bundle.wit.paddedNuls.toList := by
    rw [hPadInfo.2]
    exact mem_realNuls_mem_padded kMax salt g _ (by simpa using hPadInfo.1) hMemChain
  obtain ⟨idx, hIdxL, hElem⟩ := List.mem_iff_getElem.1 hMemPad
  have hIdx : idx < bundle.wit.paddedNuls.size := by simpa using hIdxL
  let pc := proveEpochPresentation H pp epoch R_sat turnId needRights bundle
  cases hV : verifyEpochPresentation H pp liveEnv pc.1 pc.2 with
  | false => rfl
  | true =>
    exfalso
    have hAllGaps : verifyAllGapSlots H (R_sat.gapRoot H epoch) bundle.wit.paddedNuls
        (bundle.wit.paddedNuls.map (openGapForNullifier H epoch R_sat)) = true := by
      dsimp only [pc, proveEpochPresentation] at hV
      simp only [verifyEpochPresentation, Bool.and_eq_true] at hV
      exact hV.2
    simp only [verifyAllGapSlots, Bool.and_eq_true, List.all_eq_true, List.mem_finRange] at hAllGaps
    have hSlot := hAllGaps.2 ⟨idx, hIdx⟩ trivial
    have hIdxMap : idx < (bundle.wit.paddedNuls.map (openGapForNullifier H epoch R_sat)).size := by
      simp [hIdx]
    rw [Array.getElem?_eq_getElem hIdxMap, Array.getElem_map] at hSlot
    have hNulEq : bundle.wit.paddedNuls[idx]'hIdx = nul := by simpa using hElem
    change verifyGapSlotOpening H (R_sat.gapRoot H epoch) (bundle.wit.paddedNuls[idx]'hIdx)
      (openGapForNullifier H epoch R_sat (bundle.wit.paddedNuls[idx]'hIdx)) = true at hSlot
    rw [hNulEq] at hSlot
    simp only [verifyGapSlotOpening, RevokedSet256.gapRoot, openGapForNullifier,
      gapEntryAt, Bool.and_eq_true] at hSlot
    have hFalse := (strictGap_not_contains R_sat nul (of_decide_eq_true hSlot.1.1.1) hSlot.1.2).1
    rw [hRev] at hFalse; cases hFalse

/-- **Headline Multi-Turn Trace Theorem (`retroactive_ancestor_revocation_kills_pre_folded_cone`)**:
    Suppose along ANY multi-turn `PolisTrace`, a capability chain `g` with hops `ancHops ++ extHops`
    was pre-folded offline at epoch `e_fold` into `handleId` (before any revocation!), then at
    a later turn its ancestor prefix `anc = ancHops.map SignedHop.block` (`0 ≤ j ≤ k`) is revoked
    via `.revokeAncestorChain g anc`, followed by an arbitrary sequence `laterEvents` of offline
    folds, unrelated revocations (`R_e ⊆ R_{e+1}`), and presentations reaching `stFinal` at
    `e_final > e_fold`.
    Then under `ModuleSISHard`, **NO** `EpochPresentationCert` without a discrepant-path
    `PinnedCollision` can verify or be admitted at `stFinal` (`#tooth` guarded!)! -/
theorem retroactive_ancestor_revocation_kills_pre_folded_cone
    (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    (stPre : CapFoldWorldState S)
    (hInvPre : CapFoldWorldInv H ppFor stPre)
    (handleId : Nat) (rec : FoldedHandleRecord S)
    (ancHops extHops : Array (SignedHop S))
    (hRec : stPre.handles[handleId]? = some rec)
    (hCone : rec.hops = ancHops ++ extHops)
    (hAncInt : IsInteriorNullifier256
      (credNul256 (lineageOf rec.rootGrant (ancHops.map SignedHop.block).toList)))
    (laterEvents : List (CapFoldTurnEvent S))
    (liveEnv : Nat → KleenePred3)
    (hRef : ∀ v, KleenePred3.Refines (rec.staticEnv v) (liveEnv v))
    (hCols : (ppFor rec.bundle.stmt.kMax).cols = 4 * (2 ^ nulTableVars rec.bundle.stmt.kMax))
    (hNonPig : NonPigeonholeSISParams (ppFor rec.bundle.stmt.kMax))
    (hSIS : ModuleSISHard (ppFor rec.bundle.stmt.kMax) 131070) :
    let anc := ancHops.map SignedHop.block
    let (stFinal, _) := runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)
    rec.foldEpoch < stFinal.epoch ∧
    ∀ (turnId : ByteArray) (needRights : UInt64) (cert : EpochPresentationCert),
      ¬ Nonempty (PinnedCollision H.eval
        (allGapSlotFrames H stFinal.epoch stFinal.revoked cert.gapOpenings)) →
      verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
        ⟨stFinal.epoch, turnId, needRights, rec.bundle.stmt, stFinal.revokedGapRoot, cert.presNul⟩
        cert = false ∧
      ∃ refusal, stepCapFoldWorld H ppFor stFinal
        (.presentHandle handleId turnId needRights liveEnv cert) = .error refusal := by
  let _ := hNonPig
  let anc := ancHops.map SignedHop.block
  have hAncIntB : checkInteriorNullifier256 (credNul256 (lineageOf rec.rootGrant anc.toList)) = true :=
    (checkInteriorNullifier256_iff _).2 hAncInt
  have hStepRev : stepCapFoldWorld H ppFor stPre (.revokeAncestorChain rec.rootGrant anc) =
      .ok { stPre with
            epoch := stPre.epoch + 1
            revoked := stPre.revoked.insert (credNul256 (lineageOf rec.rootGrant anc.toList)) hAncInt
            revokedGapRoot :=
              (stPre.revoked.insert (credNul256 (lineageOf rec.rootGrant anc.toList)) hAncInt).gapRoot
                H (stPre.epoch + 1) } := by
    simp only [stepCapFoldWorld, hAncIntB, ↓reduceDIte]
  obtain ⟨hInvRev, _, _, hHdlRev⟩ := stepCapFoldWorld_preserves_inv H ppFor hInvPre hStepRev
  let stRev := { stPre with
    epoch := stPre.epoch + 1
    revoked := stPre.revoked.insert (credNul256 (lineageOf rec.rootGrant anc.toList)) hAncInt
    revokedGapRoot :=
      (stPre.revoked.insert (credNul256 (lineageOf rec.rootGrant anc.toList)) hAncInt).gapRoot
        H (stPre.epoch + 1) }
  obtain ⟨hInvF, hEpF, hMonoF, hHdlF⟩ :=
    runCapFoldTrace_preserves_inv_and_monotone H ppFor laterEvents stRev hInvRev
  have hRunEq : (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1 =
      (runCapFoldTrace H ppFor stRev laterEvents).1 := by
    conv => lhs; unfold runCapFoldTrace
    rw [hStepRev]
  let stFinal := (runCapFoldTrace H ppFor stRev laterEvents).1
  have hRecMem : rec ∈ stPre.handles.toList := by
    cases Nat.lt_or_ge handleId stPre.handles.size with
    | inl hlt =>
      rw [Array.getElem?_eq_getElem hlt, Option.some.injEq] at hRec
      exact hRec ▸ Array.getElem_mem_toList hlt
    | inr hge =>
      rw [Array.getElem?_eq_none hge] at hRec; cases hRec
  obtain ⟨hFoldLe, salt, hOffline⟩ := hInvPre.2 rec hRecMem
  have hEpStrict : rec.foldEpoch < stFinal.epoch :=
    Nat.lt_of_le_of_lt hFoldLe (Nat.lt_of_lt_of_le (Nat.lt_succ_self stPre.epoch) hEpF)
  have hRevContains : stFinal.revoked.contains (credNul256 (lineageOf rec.rootGrant anc.toList)) = true :=
    hMonoF _ (RevokedSet256.contains_insert_self stPre.revoked _ hAncInt)
  have hFinalHandle : stFinal.handles[handleId]? = some rec :=
    hHdlF handleId rec (hHdlRev handleId rec hRec)
  change rec.foldEpoch < (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1.epoch ∧
    ∀ (turnId : ByteArray) (needRights : UInt64) (cert : EpochPresentationCert),
      ¬ Nonempty (PinnedCollision H.eval
        (allGapSlotFrames H (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1.epoch
          (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1.revoked cert.gapOpenings)) →
      verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
        ⟨(runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1.epoch,
         turnId, needRights, rec.bundle.stmt,
         (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1.revokedGapRoot,
         cert.presNul⟩ cert = false ∧
      ∃ refusal, stepCapFoldWorld H ppFor
        (runCapFoldTrace H ppFor stPre (.revokeAncestorChain rec.rootGrant anc :: laterEvents)).1
        (.presentHandle handleId turnId needRights liveEnv cert) = .error refusal
  rw [hRunEq]
  change rec.foldEpoch < stFinal.epoch ∧ _
  refine ⟨hEpStrict, fun turnId needRights cert hNoGapCol => ?_⟩
  have hVerFalse : verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
      ⟨stFinal.epoch, turnId, needRights, rec.bundle.stmt, stFinal.revokedGapRoot, cert.presNul⟩
      cert = false := by
    cases hV : verifyEpochPresentation H (ppFor rec.bundle.stmt.kMax) liveEnv
        ⟨stFinal.epoch, turnId, needRights, rec.bundle.stmt, stFinal.revokedGapRoot, cert.presNul⟩
        cert with
    | false => rfl
    | true =>
      exfalso
      match extractEpochPresentationOrFoldChain H (ppFor rec.bundle.stmt.kMax)
          hRef hCols hOffline stFinal.revoked rfl hInvF.1 hV with
      | .inr (.dualCommitBreak _ sisWit) =>
        exact hSIS ⟨sisWit⟩
      | .inr (.gapTreePinnedCollision gCol) =>
        exact hNoGapCol ⟨gCol⟩
      | .inl ⟨acc, hFoldChain, _, _, _, _, _, _, _, _⟩ =>
        rw [hCone, Array.map_append] at hFoldChain
        have hLive := (foldChain_prefix_live stFinal.revoked.toRevokedSet liveEnv
          rec.rootGrant anc (extHops.map SignedHop.block) acc hFoldChain).1
        have hCont : stFinal.revoked.toRevokedSet.contains
            (credNul (lineageOf rec.rootGrant anc.toList)) = true := by
          rw [← credNul256_toNat, stFinal.revoked.toRevokedSet_contains_eq]
          exact hRevContains
        rw [lineageLive, hCont] at hLive
        cases hLive
  refine ⟨hVerFalse, ?_⟩
  dsimp only [stepCapFoldWorld]
  rw [hFinalHandle]
  dsimp only
  split
  · split
    · exact ⟨_, rfl⟩
    · rw [hVerFalse]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **Retroactive Channel Revocation (`retroactive_channel_revocation_kills_pre_folded_chain`)**:
    Revoking any hop's `channel` at `epoch` kills every pre-folded capability chain containing a
    hop over `channel` (`#tooth` guarded!). -/
theorem retroactive_channel_revocation_kills_pre_folded_chain
    (H : Hash32) (ppFor : Nat → AjtaiParams) {S : HopSigScheme}
    {kMax rootEpochFloor epoch : Nat} {staticEnv liveEnv : Nat → KleenePred3}
    (hRef : ∀ v, KleenePred3.Refines (staticEnv v) (liveEnv v))
    (hCols : (ppFor kMax).cols = 4 * (2 ^ nulTableVars kMax))
    (hNonPig : NonPigeonholeSISParams (ppFor kMax))
    (hSIS : ModuleSISHard (ppFor kMax) 131070)
    (g : Block) (hops : Array (SignedHop S)) (salt : BitVec 256) (bundle : OfflineCapBundle)
    (hOff : foldChainEpochFree H (ppFor kMax) S kMax staticEnv rootEpochFloor g hops salt = some bundle)
    (b : Block) (hb : b ∈ (hops.map SignedHop.block).toList)
    (R_sat : RevokedSet256)
    (hChanRev : R_sat.contains (chanNul256 b.channel) = true)
    (turnId : ByteArray) (needRights : UInt64) (cert : EpochPresentationCert)
    (hNoGapCol : ¬ Nonempty (PinnedCollision H.eval (allGapSlotFrames H epoch R_sat cert.gapOpenings))) :
    verifyEpochPresentation H (ppFor kMax) liveEnv
      ⟨epoch, turnId, needRights, bundle.stmt, R_sat.gapRoot H epoch, cert.presNul⟩ cert = false := by
  let _ := hNonPig
  cases hV : verifyEpochPresentation H (ppFor kMax) liveEnv
      ⟨epoch, turnId, needRights, bundle.stmt, R_sat.gapRoot H epoch, cert.presNul⟩ cert with
  | false => rfl
  | true =>
    exfalso
    match extractEpochPresentationOrFoldChain H (ppFor kMax) hRef hCols hOff R_sat rfl rfl hV with
    | .inr (.dualCommitBreak _ sisWit) =>
      exact hSIS ⟨sisWit⟩
    | .inr (.gapTreePinnedCollision gCol) =>
      exact hNoGapCol ⟨gCol⟩
    | .inl ⟨_, hFoldChain, _, _, _, _, _, _, _, _⟩ =>
      obtain ⟨_, _, hl⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 hFoldChain
      have hChanLive := (foldBlocks_facts R_sat.toRevokedSet liveEnv _ _ _ hl).2.2.2.2 b hb
      have hCont : R_sat.toRevokedSet.contains (chanNul b.channel) = true := by
        rw [← chanNul256_toNat, R_sat.toRevokedSet_contains_eq]
        exact hChanRev
      rw [channelLive, hCont] at hChanLive
      cases hChanLive

/-! ## 7. First-Class `Obend.Judge` Instance (`zkCapFoldJudge`) -/

/-- Query object judged by `zkCapFoldJudge`. -/
structure ZkCapFoldQuery where
  pub : CapPresentationPublicInputs
  liveEnv : Nat → KleenePred3

inductive ZkCapFoldClause where
  | epochBoundViolated
  | insufficientRightsOrCaveat
  | malformedSlotArity
  | cryptographicVerificationFailed
  deriving DecidableEq, Repr

/-- Declarative semantic contract of `zkCapFoldJudge` (zero self-reference to `checkZkCapFold`). -/
def ZkCapFoldMeaning (q : ZkCapFoldQuery) (cert : EpochPresentationCert) : Prop :=
  let kMax := q.pub.offlineStmt.kMax
  let pp := capFoldAjtaiParams kMax
  let v := nulTableVars kMax
  let tbl := buildSaltedNulTable kMax cert.commitSalt cert.paddedNuls
  let limbs := gadgetDecomposeTable tbl
  checkLiveEpochBound q.pub.offlineStmt.epochFloor q.pub.epoch q.pub.revokedGapRoot.epoch = true ∧
  subMask q.pub.needRights q.pub.offlineStmt.tailRights = true ∧
  (q.pub.offlineStmt.residualCaveat.eval q.liveEnv).accepts = true ∧
  cert.paddedNuls.size = 2 * kMax + 2 ∧
  cert.gapOpenings.size = 2 * kMax + 2 ∧
  cert.presNul = q.pub.presNul ∧
  q.pub.presNul = computePresNul256 q.pub.epoch cert.commitSalt q.pub.turnId cert.tailLineage ∧
  q.pub.offlineStmt.holderLinkCommit =
    computeHolderLinkCommit deployedCanopyHash32 cert.commitSalt cert.tailHolder cert.tailLineage ∧
  q.pub.offlineStmt.nulVecCommit =
    commitSaltedNulTable deployedCanopyHash32 pp kMax cert.commitSalt cert.paddedNuls ∧
  verifyDualSumcheckPIOP (canopyMerklePCS deployedCanopyHash32) (ajtaiLatticePCS pp) ((), ())
    1 v q.pub.offlineStmt.nulVecCommit (hypercubeSum v tbl)
    cert.sumcheckRounds cert.dualOpening (capPresentationTranscript q.pub) = true ∧
  verifyMaskedAjtaiOpening pp.modulus pp.cols 65535 pp.matrix
    (GameSoundness.ajtaiSyndrome pp.modulus pp.matrix limbs)
    cert.ajtaiMaskSyndrome 1 cert.ajtaiMaskedResp = true ∧
  verifyAllGapSlots deployedCanopyHash32 q.pub.revokedGapRoot cert.paddedNuls cert.gapOpenings = true

def checkZkCapFold (_grade : Nat) (q : ZkCapFoldQuery) (cert : EpochPresentationCert) :
    Obend.Judge.Verdict ZkCapFoldClause :=
  if !checkLiveEpochBound q.pub.offlineStmt.epochFloor q.pub.epoch q.pub.revokedGapRoot.epoch then
    .refused .epochBoundViolated []
  else if !(subMask q.pub.needRights q.pub.offlineStmt.tailRights &&
            (q.pub.offlineStmt.residualCaveat.eval q.liveEnv).accepts) then
    .refused .insufficientRightsOrCaveat []
  else if !(cert.paddedNuls.size == 2 * q.pub.offlineStmt.kMax + 2 &&
            cert.gapOpenings.size == 2 * q.pub.offlineStmt.kMax + 2) then
    .refused .malformedSlotArity []
  else if verifyEpochPresentation deployedCanopyHash32 (capFoldAjtaiParams q.pub.offlineStmt.kMax)
      q.liveEnv q.pub cert then
    .ok
  else
    .refused .cryptographicVerificationFailed []

theorem checkZkCapFold_ok_iff (grade : Nat) (q : ZkCapFoldQuery) (cert : EpochPresentationCert) :
    checkZkCapFold grade q cert = .ok ↔ ZkCapFoldMeaning q cert := by
  unfold checkZkCapFold ZkCapFoldMeaning
  cases hEp : checkLiveEpochBound q.pub.offlineStmt.epochFloor q.pub.epoch q.pub.revokedGapRoot.epoch with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨h1, _⟩; cases h1
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hAuth : (subMask q.pub.needRights q.pub.offlineStmt.tailRights &&
        (q.pub.offlineStmt.residualCaveat.eval q.liveEnv).accepts) with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨_, h1, h2, _⟩
      have ht : (subMask q.pub.needRights q.pub.offlineStmt.tailRights &&
          (q.pub.offlineStmt.residualCaveat.eval q.liveEnv).accepts) = true := by simp [h1, h2]
      rw [hAuth] at ht; cases ht
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true] at hAuth
      cases hArity : (cert.paddedNuls.size == 2 * q.pub.offlineStmt.kMax + 2 &&
          cert.gapOpenings.size == 2 * q.pub.offlineStmt.kMax + 2) with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨_, _, _, ha1, ha2, _⟩
        have ht : (cert.paddedNuls.size == 2 * q.pub.offlineStmt.kMax + 2 &&
            cert.gapOpenings.size == 2 * q.pub.offlineStmt.kMax + 2) = true := by simp [ha1, ha2]
        rw [hArity] at ht; cases ht
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hArity
        constructor
        · intro hOk
          split at hOk
          · rename_i hV
            simp only [verifyEpochPresentation, Bool.and_eq_true, beq_iff_eq] at hV
            rcases hV with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
            exact ⟨trivial, hAuth.1, hAuth.2, hArity.1, hArity.2, h1, h2, h3, h4, h5, h6, h7⟩
          · cases hOk
        · rintro ⟨_, _, _, _, _, h1, h2, h3, h4, h5, h6, h7⟩
          have hV : verifyEpochPresentation deployedCanopyHash32
              (capFoldAjtaiParams q.pub.offlineStmt.kMax) q.liveEnv q.pub cert = true := by
            simp only [verifyEpochPresentation, Bool.and_eq_true, beq_iff_eq]
            exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hArity.1, hArity.2⟩, hEp⟩, hAuth.1⟩, hAuth.2⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
          simp [hV]

instance zkCapFoldJudge : Obend.Judge ZkCapFoldQuery EpochPresentationCert where
  Clause := ZkCapFoldClause
  Meaning := ZkCapFoldMeaning
  check := checkZkCapFold
  sound := by intro r o c h; exact (checkZkCapFold_ok_iff r o c).1 h
  refutes
    | .epochBoundViolated => true
    | .insufficientRightsOrCaveat => true
    | _ => false
  refuted := by
    intro r o c k p hc hk c' hm
    unfold checkZkCapFold at hc
    split at hc
    · rename_i hBadEp
      rw [hm.1] at hBadEp; simp at hBadEp
    · split at hc
      · rename_i hBadAuth
        have hGood : (subMask o.pub.needRights o.pub.offlineStmt.tailRights &&
            (o.pub.offlineStmt.residualCaveat.eval o.liveEnv).accepts) = true := by
          simp [hm.2.1, hm.2.2.1]
        rw [hGood] at hBadAuth; simp at hBadAuth
      · split at hc
        · cases hc; cases hk
        · split at hc <;> cases hc; cases hk
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hm⟩
    exact ⟨c, 0, (checkZkCapFold_ok_iff 0 o c).2 hm⟩
  mono := by intro _ _ _ _ _ _; rfl

example : (∃ k, zkCapFoldJudge.refutes k = true) ∧ (∃ k, zkCapFoldJudge.refutes k = false) := by
  exact ⟨⟨.insufficientRightsOrCaveat, rfl⟩, ⟨.cryptographicVerificationFailed, rfl⟩⟩

end Obend.Polis.ZkCapFold
end
