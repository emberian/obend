module
/-
# Obend.Vault.Projection — stranger-checkable blinded cSHAKE256 Merkle multiproofs & Fog-of-War noninterference

Absorbs `breadstuffs/Dregg2/Deos/FogOfWar.lean`, `Rerender.lean`, and `Rehydration.lean` on top of
`Obend.Receipt.Merkle` and `Obend.Core.Digest`.

Addresses Requirement R3 and Milestone 3 Feature 26 (`Receipt.blind`) and Feature 27 (`FogOfWar.noninterference`):
1. **Fog-of-War Visibility**: State is partitioned into per-cell authority gates (`VaultCell`). A viewer sees
   a cell if and only if its capability set authorizes it (`canSee`, via `fireGate`). A hidden cell is
   STRUCTURALLY ABSENT from the viewer's visible projection (`visibleTo`), not a redacted placeholder.
2. **Machine-Checked Non-Interference**: If two vaults agree on every cell a viewer holding rights `v` is
   authorized to see (`agreeOn`), their projections are bit-identical (`fog_of_war_noninterference`).
   Consequently, changing or inserting any hidden cell leaves the low projection unchanged
   (`hidden_change_invisible`, `cons_hidden_invisible`).
3. **Cryptographic Blinding & Root Invariance**: Every cell is bound with a cryptographic blinding salt
   (`cellBlind H c = digestWith H c.salt c.content`). In the projected view (`projectCell`), visible cells
   reveal `(id, required, salt, content)`, while hidden cells reveal only the blinded commitment
   (`blinded id (cellBlind H c)`). The Merkle root of the projected vault equals the unredacted vault root
   bit-for-bit (`projectVault_mapRoot_eq`).
4. **Stranger-Checkable Merkle Multiproofs**: a blinded projection is a multiproof of the unredacted
   vault root, verified as one `Obend.Receipt.Merkle.MerkleBatchProof` (`verifyBlindedMultiProof`:
   pairwise-distinct positions, every leaf climbing to the root). The honest multiproof of any set of
   positions verifies (`verify_blinded_multiproof_complete`), a verifying multiproof is a set of
   verifying openings at distinct positions (`verifyBlindedMultiProof_sound`), and every opening it
   carries commits to the vault's cell at that position, or the hash collides
   (`verifyBlindedMultiProof_binds`, `verifyBlindedMultiProof_revealed_binds`). Single openings
   (`verifyBlindedOpening`, `verify_blinded_opening_complete`, `stranger_verification_sound`) are the
   same Merkle openings one at a time. Until 2026-11-04 the multiproof was a list of openings each
   checked alone, with no distinctness rule: one opening could be presented as several cells.

What blinding rests on. A blinded cell shows `cellBlind H c`, which commits to the salt and the
content together, so the content is hidden exactly as far as the salt is unpredictable to the
stranger: with a salt the stranger can derive, the commitment is a dictionary over the content.
`Obend.Core.Digest.Hiding` is ASSUMED, not proved, and nothing here constrains where a salt comes
from; the 2026-11-03 review (S12) found the node deriving its salts from public data. The
requirement on an issuer is a fresh, secret salt per cell; this module proves binding, not hiding.
-/
public import Obend.Receipt.Merkle
public import Obend.Core.Digest
public import Obend.Digest.HashBytes

@[expose] public section

namespace Obend.Vault.Projection

open Obend.Core.Digest (digestWith Admissible admissible_of_lt binds_or_collides)
open Obend.Digest.HashBytes (Hash Collision)
open Obend.Receipt.Merkle (Small Bounded root path climb leaf leaves mapRoot Opening opens climb_path mapOpening opens_complete opens_binds
  leaves_length leaves_small leaves_getD MerkleBatchEntry MerkleBatchProof verifyMerkleBatchProof verifySingleMerkleLeaf
  verifyMerkleBatchProof_sound verifyMerkleBatchProof_honest verifyMerkleBatchProof_binds honestBatchEntry honestBatchProof leaf_binds)

set_option autoImplicit false

/-! ## 1. IPC Authority Kinds & Confinement Gates -/

/-- Authority kinds representing seL4/Dregg2 IPC authorities. -/
inductive Auth where
  | read
  | write
  | grant
  | call
  | reply
  | reset
  | control
  | notify
  deriving DecidableEq, Repr

/-- `fireGate required held`: true iff every required authority is held. -/
def fireGate (required held : List Auth) : Bool :=
  required.all fun r => held.contains r

theorem fireGate_iff_subset (required held : List Auth) :
    fireGate required held = true ↔ ∀ a ∈ required, a ∈ held := by
  simp [fireGate, List.all_eq_true]

theorem fireGate_refl (held : List Auth) : fireGate held held = true := by
  rw [fireGate_iff_subset]; intro a ha; exact ha

theorem fireGate_trans {r h₁ h₂ : List Auth} (hsub : h₁ ⊆ h₂) (hgate : fireGate r h₁ = true) :
    fireGate r h₂ = true := by
  rw [fireGate_iff_subset] at hgate ⊢
  intro a ha
  exact hsub (hgate a ha)

/-! ## 2. Vault Cells & Fog-of-War Projection -/

/-- A cell of the shared vault: stable `id`, access authority `required`, cryptographic blinding `salt`,
    and digest-sized `content`. -/
structure VaultCell where
  id       : Nat
  required : List Auth
  salt     : Nat
  content  : Nat
  deriving DecidableEq, Repr, Inhabited

/-- May a viewer holding rights `v` see cell `c`? -/
def canSee (v : List Auth) (c : VaultCell) : Bool :=
  fireGate c.required v

/-- The per-viewer projection of a vault: the sublist of cells `v` may see.
    Hidden cells are STRUCTURALLY ABSENT (filtered out, not redacted placeholders). -/
def visibleTo (v : List Auth) (s : List VaultCell) : List VaultCell :=
  s.filter (canSee v)

/-- Two vaults are indistinguishable to `v` iff their visible projections are identical. -/
def agreeOn (v : List Auth) (s₁ s₂ : List VaultCell) : Prop :=
  visibleTo v s₁ = visibleTo v s₂

theorem view_deterministic (v : List Auth) (s : List VaultCell) :
    visibleTo v s = visibleTo v s := rfl

theorem visible_means_canSee (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ visibleTo v s) : canSee v c = true :=
  (List.mem_filter.mp hmem).2

theorem canSee_means_visible (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ s) (hsee : canSee v c = true) : c ∈ visibleTo v s :=
  List.mem_filter.mpr ⟨hmem, hsee⟩

/-- Total fog: a hidden cell does not appear in the projection at all (no leak via presence). -/
theorem hiddenCell_absent (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hhide : canSee v c = false) : c ∉ visibleTo v s := by
  intro hmem
  have hc := visible_means_canSee v s c hmem
  rw [hhide] at hc
  cases hc

/-- **Headline Non-Interference**: A low viewer's render is a function of the authorized state alone.
    If two vaults agree on everything `v` may see, their projections are bit-identical. -/
theorem fog_of_war_noninterference (v : List Auth) (s₁ s₂ : List VaultCell)
    (hagree : agreeOn v s₁ s₂) : visibleTo v s₁ = visibleTo v s₂ := hagree

/-- Inserting a hidden cell leaves the visible view unchanged. -/
theorem cons_hidden_invisible (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hhide : canSee v c = false) : visibleTo v (c :: s) = visibleTo v s := by
  unfold visibleTo
  rw [List.filter_cons, hhide]
  rfl

/-- Changing a hidden cell outside a viewer's authority leaves the projection bit-identical. -/
theorem hidden_change_invisible (v : List Auth) (pre post : List VaultCell) (c c' : VaultCell)
    (hc : canSee v c = false) (hc' : canSee v c' = false) :
    visibleTo v (pre ++ c :: post) = visibleTo v (pre ++ c' :: post) := by
  unfold visibleTo
  simp only [List.filter_append, List.filter_cons, hc, hc', Bool.false_eq_true, ↓reduceIte]

/-- Divergence: two viewers see different scenes bounded strictly by their caps. -/
theorem divergence (v₁ v₂ : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ s) (hsee₁ : canSee v₁ c = true) (hhide₂ : canSee v₂ c = false) :
    c ∈ visibleTo v₁ s ∧ c ∉ visibleTo v₂ s :=
  ⟨canSee_means_visible v₁ s c hmem hsee₁, hiddenCell_absent v₂ s c hhide₂⟩

theorem canSee_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) {c : VaultCell}
    (hsee : canSee v₁ c = true) : canSee v₂ c = true :=
  fireGate_trans h12 hsee

/-- Monotonicity: granting more capability yields a superset view. -/
theorem vision_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) (s : List VaultCell) :
    visibleTo v₁ s ⊆ visibleTo v₂ s := by
  intro c hc
  have hmem : c ∈ s := (List.mem_filter.mp hc).1
  have hsee₁ : canSee v₁ c = true := visible_means_canSee v₁ s c hc
  exact canSee_means_visible v₂ s c hmem (canSee_monotone h12 hsee₁)

/-- Projection idempotence (stability law). -/
theorem rerender_idempotent (v : List Auth) (s : List VaultCell) :
    visibleTo v (visibleTo v s) = visibleTo v s := by
  unfold visibleTo
  rw [List.filter_filter]
  have h_eq : (fun c => canSee v c && canSee v c) = canSee v := by
    funext c; cases canSee v c <;> rfl
  rw [h_eq]

/-! ## 3. Metadata-Bound Cryptographic Blinding & Root Invariance -/

/-- Extract the read capability bit (`0` or `1`) from an authority list. -/
def readCapOf (req : List Auth) : Nat :=
  if req.contains .read then 1 else 0

/-- Extract the write capability bit (`0` or `1`) from an authority list. -/
def writeCapOf (req : List Auth) : Nat :=
  if req.contains .write then 1 else 0

/-- Extract the full 8-capability bitmask (`0..255`) over all `Auth` variants in `req`. -/
def capMaskOf (req : List Auth) : Nat :=
  (if req.contains .read then 1 else 0) +
  (if req.contains .write then 2 else 0) +
  (if req.contains .grant then 4 else 0) +
  (if req.contains .call then 8 else 0) +
  (if req.contains .reply then 16 else 0) +
  (if req.contains .reset then 32 else 0) +
  (if req.contains .control then 64 else 0) +
  (if req.contains .notify then 128 else 0)

/-- Read capability metadata of a `VaultCell`. -/
def VaultCell.readCap (c : VaultCell) : Nat :=
  readCapOf c.required

/-- Write capability metadata of a `VaultCell`. -/
def VaultCell.writeCap (c : VaultCell) : Nat :=
  writeCapOf c.required

/-- Full 8-capability bitmask metadata of a `VaultCell`. -/
def VaultCell.capMask (c : VaultCell) : Nat :=
  capMaskOf c.required

theorem readCapOf_lt (req : List Auth) : readCapOf req < 2 ^ 256 := by
  unfold readCapOf
  split <;> decide

theorem writeCapOf_lt (req : List Auth) : writeCapOf req < 2 ^ 256 := by
  unfold writeCapOf
  split <;> decide

theorem capMaskOf_lt (req : List Auth) : capMaskOf req < 2 ^ 256 := by
  unfold capMaskOf
  have h0 : (if req.contains .read then 1 else 0) ≤ 1 := by split <;> decide
  have h1 : (if req.contains .write then 2 else 0) ≤ 2 := by split <;> decide
  have h2 : (if req.contains .grant then 4 else 0) ≤ 4 := by split <;> decide
  have h3 : (if req.contains .call then 8 else 0) ≤ 8 := by split <;> decide
  have h4 : (if req.contains .reply then 16 else 0) ≤ 16 := by split <;> decide
  have h5 : (if req.contains .reset then 32 else 0) ≤ 32 := by split <;> decide
  have h6 : (if req.contains .control then 64 else 0) ≤ 64 := by split <;> decide
  have h7 : (if req.contains .notify then 128 else 0) ≤ 128 := by split <;> decide
  omega

/-- Metadata-bound commitment over `(id, readCap, writeCap, capMask, salt, content)`. -/
def cellBlindMetadataBoundValues (H : Hash) (id readCap writeCap capMask salt content : Nat) : Nat :=
  digestWith H
    (digestWith H id (digestWith H readCap (digestWith H writeCap capMask)))
    (digestWith H salt content)

/-- The metadata-bound blinded commitment of a cell:
    commits to `(c.id, c.readCap, c.writeCap, c.capMask, c.salt, c.content)`. -/
def cellBlind (H : Hash) (c : VaultCell) : Nat :=
  cellBlindMetadataBoundValues H c.id c.readCap c.writeCap c.capMask c.salt c.content

abbrev cellBlindMetadataBound (H : Hash) (c : VaultCell) : Nat :=
  cellBlind H c

/-- Projected cell: revealed to authorized viewers, blinded to strangers/unauthorized viewers. -/
inductive ProjectedCell where
  | revealed (id : Nat) (required : List Auth) (salt : Nat) (content : Nat)
  | blinded  (id : Nat) (blindedCommit : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Project an individual cell for viewer `v`. -/
def projectCell (H : Hash) (v : List Auth) (c : VaultCell) : ProjectedCell :=
  if canSee v c then
    .revealed c.id c.required c.salt c.content
  else
    .blinded c.id (cellBlind H c)

/-- The commitment value verified by the Merkle tree:
    for revealed cells, recomputed from `(id, readCapOf required, writeCapOf required, capMaskOf required, salt, content)`;
    for blinded cells, the carried blinded commitment. -/
def projectedCommit (H : Hash) : ProjectedCell → Nat
  | .revealed id required salt content =>
    cellBlindMetadataBoundValues H id (readCapOf required) (writeCapOf required) (capMaskOf required) salt content
  | .blinded _ blindedCommit  => blindedCommit

/-- **Core Commitment Invariant**: Regardless of whether a cell is revealed or blinded,
    its commitment in the Merkle tree is bit-identical to the unredacted vault cell commitment. -/
@[simp] theorem projectCell_commit_eq (H : Hash) (v : List Auth) (c : VaultCell) :
    projectedCommit H (projectCell H v c) = cellBlind H c := by
  dsimp [projectCell, cellBlind, VaultCell.readCap, VaultCell.writeCap, VaultCell.capMask]
  split <;> rfl

theorem projectedCommit_eq_cellBlind (H : Hash) (v : List Auth) (c : VaultCell) :
    projectedCommit H (projectCell H v c) = cellBlind H c :=
  projectCell_commit_eq H v c

/-- Project all cells in a vault for viewer `v`. -/
def projectVault (H : Hash) (v : List Auth) (cells : List VaultCell) : List ProjectedCell :=
  cells.map (projectCell H v)

/-- The list of unredacted cell commitments in a vault. -/
def vaultCommits (H : Hash) (cells : List VaultCell) : List Nat :=
  cells.map (cellBlind H)

abbrev vaultCommitsMetadataBound (H : Hash) (cells : List VaultCell) : List Nat :=
  vaultCommits H cells

/-- The list of commitment values extracted from a projected vault. -/
def projectedCommits (H : Hash) (v : List Auth) (cells : List VaultCell) : List Nat :=
  (projectVault H v cells).map (projectedCommit H)

/-- The commitments extracted from a projected vault equal the unredacted vault commitments. -/
theorem projectedCommits_eq (H : Hash) (v : List Auth) (cells : List VaultCell) :
    projectedCommits H v cells = vaultCommits H cells := by
  unfold projectedCommits vaultCommits projectVault
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    simp [projectCell_commit_eq, ih]

/-- **Root Invariance Theorem**: The Merkle root of a projected vault is bit-identical
    to the root of the unredacted vault. -/
theorem projectVault_mapRoot_eq (H : Hash) (v : List Auth) (cells : List VaultCell) :
    mapRoot H (projectedCommits H v cells) = mapRoot H (vaultCommits H cells) := by
  rw [projectedCommits_eq]

/-- Binary Merkle tree root over `projectedCommits`. -/
def projectedMerkleRoot (H : Hash) (v : List Auth) (cells : List VaultCell) : Nat :=
  mapRoot H (projectedCommits H v cells)

theorem projectedMerkleRoot_eq_vaultRoot (H : Hash) (v : List Auth) (cells : List VaultCell) :
    projectedMerkleRoot H v cells = mapRoot H (vaultCommits H cells) := by
  unfold projectedMerkleRoot
  rw [projectedCommits_eq]

/-! ## 4. Stranger-Checkable Merkle Multiproofs & Metadata Binding -/

/-- A blinded opening: tree size, position index, projected cell, and sibling path. -/
structure BlindedOpening where
  size  : Nat
  index : Nat
  cell  : ProjectedCell
  path  : List Nat
  deriving DecidableEq, Repr

/-- Stranger verification of an individual opening against the unredacted vault root. -/
def verifyBlindedOpening (H : Hash) (bo : BlindedOpening) (vaultRoot : Nat) : Bool :=
  Small bo.index &&
  climb H bo.size bo.index (leaf H bo.index (projectedCommit H bo.cell)) bo.path == some vaultRoot

/-- The batch entry of a blinded opening: the Merkle leaf of the projected commitment at its
position, and its siblings. -/
def BlindedOpening.toBatchEntry (H : Hash) (bo : BlindedOpening) : MerkleBatchEntry :=
  ⟨bo.index, leaf H bo.index (projectedCommit H bo.cell), bo.path⟩

/-- A blinded projection as a multiproof of the unredacted vault root: the root, the tree size, and
the openings, verified as one `MerkleBatchProof`. -/
structure BlindedMultiProof where
  vaultRoot : Nat
  size      : Nat
  openings  : List BlindedOpening
  deriving DecidableEq, Repr

def BlindedMultiProof.toBatch (H : Hash) (bmp : BlindedMultiProof) : MerkleBatchProof :=
  ⟨bmp.size, bmp.openings.map (BlindedOpening.toBatchEntry H)⟩

/-- Verify a blinded multiproof: pairwise-distinct positions, every leaf climbing to the root
(`Obend.Receipt.Merkle.verifyMerkleBatchProof`). -/
def verifyBlindedMultiProof (H : Hash) (bmp : BlindedMultiProof) : Bool :=
  verifyMerkleBatchProof H (bmp.toBatch H) bmp.vaultRoot

/-- Construct an honest blinded opening for cell `j`. -/
def mkBlindedOpening (H : Hash) (v : List Auth) (cells : List VaultCell) (j : Nat) : BlindedOpening :=
  let o := mapOpening H (vaultCommits H cells) j
  ⟨o.size, o.index, projectCell H v (cells.getD j default), o.path⟩

theorem verifyBlindedOpening_eq_opens (H : Hash) (bo : BlindedOpening) (vaultRoot : Nat) :
    verifyBlindedOpening H bo vaultRoot =
    opens H ⟨bo.size, bo.index, projectedCommit H bo.cell, bo.path⟩ vaultRoot := rfl

theorem getD_map_helper {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (j : Nat), j < l.length → (l.map f).getD j d' = f (l.getD j d)
  | [], _, hj => by cases hj
  | _ :: _, 0, _ => rfl
  | _ :: xs, n + 1, hj => by
    have hj' : n < xs.length := by simpa using hj
    exact getD_map_helper f d d' xs n hj'

/-- **Completeness Theorem**: Every honestly issued blinded opening verifies against the unredacted vault root. -/
theorem verify_blinded_opening_complete {H : Hash} (hb : Bounded H)
    (v : List Auth) (cells : List VaultCell) (j : Nat)
    (hj : j < cells.length) (hjs : j < 2 ^ 256) :
    verifyBlindedOpening H (mkBlindedOpening H v cells j) (mapRoot H (vaultCommits H cells)) = true := by
  have hlen : j < (vaultCommits H cells).length := by
    simp [vaultCommits, hj]
  have hc := opens_complete hb (vaultCommits H cells) j hlen hjs
  rw [verifyBlindedOpening_eq_opens]
  unfold mkBlindedOpening mapOpening
  dsimp only
  have hcomm : projectedCommit H (projectCell H v (cells.getD j default)) = (vaultCommits H cells).getD j 0 := by
    rw [projectCell_commit_eq]
    exact (getD_map_helper (cellBlind H) default 0 cells j hj).symm
  rw [hcomm]
  exact hc

/-- **Stranger Verification Soundness**: Passing stranger verification entails standard Merkle opening validity. -/
theorem stranger_verification_sound {H : Hash}
    (bo : BlindedOpening) (vaultRoot : Nat) (hver : verifyBlindedOpening H bo vaultRoot = true) :
    opens H ⟨bo.size, bo.index, projectedCommit H bo.cell, bo.path⟩ vaultRoot = true :=
  hver

/-- The honest multiproof of positions `idxs` of a vault, projected for viewer `v`. -/
def mkBlindedMultiProof (H : Hash) (v : List Auth) (cells : List VaultCell) (idxs : List Nat) :
    BlindedMultiProof :=
  ⟨mapRoot H (vaultCommits H cells), cells.length, idxs.map (mkBlindedOpening H v cells)⟩

theorem vaultCommits_length (H : Hash) (cells : List VaultCell) :
    (vaultCommits H cells).length = cells.length := by
  simp [vaultCommits]

/-- An honest blinded opening's batch entry is the honest batch entry of the vault's leaves. -/
theorem toBatchEntry_mkBlindedOpening (H : Hash) (v : List Auth) (cells : List VaultCell) {i : Nat}
    (hi : i < cells.length) :
    BlindedOpening.toBatchEntry H (mkBlindedOpening H v cells i) =
      honestBatchEntry H (leaves H (vaultCommits H cells)) i := by
  have hlen : i < (vaultCommits H cells).length := by rw [vaultCommits_length]; exact hi
  have hget : (vaultCommits H cells).getD i 0 = cellBlind H (cells.getD i default) :=
    getD_map_helper (cellBlind H) default 0 cells i hi
  simp only [BlindedOpening.toBatchEntry, mkBlindedOpening, mapOpening, honestBatchEntry,
    leaves_getD H (vaultCommits H cells) hlen, projectCell_commit_eq, hget]

/-- **Multiproof completeness**: the honest multiproof of any pairwise-distinct, in-range set of
positions verifies against the unredacted vault root. -/
theorem verify_blinded_multiproof_complete {H : Hash} (hb : Bounded H)
    (v : List Auth) (cells : List VaultCell) (hs : cells.length < 2 ^ 256)
    (idxs : List Nat) (hnodup : idxs.Nodup) (hbounds : ∀ i ∈ idxs, i < cells.length) :
    verifyBlindedMultiProof H (mkBlindedMultiProof H v cells idxs) = true := by
  have hl : (leaves H (vaultCommits H cells)).length = cells.length := by
    rw [leaves_length, vaultCommits_length]
  have hmap : (idxs.map (mkBlindedOpening H v cells)).map (BlindedOpening.toBatchEntry H) =
      idxs.map (honestBatchEntry H (leaves H (vaultCommits H cells))) := by
    rw [List.map_map]
    exact List.map_congr_left fun i hi => toBatchEntry_mkBlindedOpening H v cells (hbounds i hi)
  have hhonest := verifyMerkleBatchProof_honest hb (leaves H (vaultCommits H cells))
    (leaves_small hb _) (by rw [hl]; exact hs) idxs hnodup (fun i hi => by rw [hl]; exact hbounds i hi)
  simp only [verifyBlindedMultiProof, mkBlindedMultiProof, BlindedMultiProof.toBatch, hmap, mapRoot]
  simp only [honestBatchProof, hl] at hhonest
  exact hhonest

/-- **Multiproof soundness**: a verifying multiproof has pairwise-distinct positions and every
opening in it is a verifying Merkle opening of the multiproof's size against its root. -/
theorem verifyBlindedMultiProof_sound {H : Hash} {bmp : BlindedMultiProof}
    (h : verifyBlindedMultiProof H bmp = true) :
    (bmp.openings.map BlindedOpening.index).Nodup ∧
    ∀ bo ∈ bmp.openings,
      opens H ⟨bmp.size, bo.index, projectedCommit H bo.cell, bo.path⟩ bmp.vaultRoot = true := by
  obtain ⟨hnodup, hentries⟩ := verifyMerkleBatchProof_sound H (bmp.toBatch H) bmp.vaultRoot h
  refine ⟨?_, fun bo hbo => ?_⟩
  · have hcomp : (MerkleBatchEntry.leafIndex ∘ BlindedOpening.toBatchEntry H) = BlindedOpening.index :=
      funext fun _ => rfl
    simp only [BlindedMultiProof.toBatch, List.map_map, hcomp] at hnodup
    exact hnodup
  · obtain ⟨hsingle, _⟩ := hentries (BlindedOpening.toBatchEntry H bo)
      (List.mem_map_of_mem (f := BlindedOpening.toBatchEntry H) hbo)
    simp only [verifySingleMerkleLeaf, BlindedOpening.toBatchEntry, Bool.and_eq_true] at hsingle
    simp only [opens, Bool.and_eq_true]
    exact ⟨hsingle.1.1, hsingle.2⟩

/-- **Multiproof binding**: against the unredacted root of `cells` with the right size, every
opening a verifying multiproof carries commits to the vault's cell at its position, or `H`
collides. -/
theorem verifyBlindedMultiProof_binds {H : Hash} (hb : Bounded H) (cells : List VaultCell)
    (hs : cells.length < 2 ^ 256) {bmp : BlindedMultiProof}
    (h : verifyBlindedMultiProof H bmp = true)
    (hroot : bmp.vaultRoot = mapRoot H (vaultCommits H cells)) (hsize : bmp.size = cells.length)
    {bo : BlindedOpening} (hbo : bo ∈ bmp.openings) (hi : bo.index < cells.length) :
    projectedCommit H bo.cell = cellBlind H cells[bo.index] ∨ Collision H := by
  have hl : (leaves H (vaultCommits H cells)).length = cells.length := by
    rw [leaves_length, vaultCommits_length]
  have hi' : bo.index < (leaves H (vaultCommits H cells)).length := by rw [hl]; exact hi
  have hbatch : verifyMerkleBatchProof H (bmp.toBatch H) (root H (leaves H (vaultCommits H cells))) = true := by
    rw [← mapRoot, ← hroot]; exact h
  have hsz : (bmp.toBatch H).treeSize = (leaves H (vaultCommits H cells)).length := by
    simp [BlindedMultiProof.toBatch, hsize, hl]
  have hbind := verifyMerkleBatchProof_binds hb (leaves H (vaultCommits H cells)) (leaves_small hb _)
    hbatch hsz (List.mem_map_of_mem (f := BlindedOpening.toBatchEntry H) hbo) hi'
  have hleaf : (leaves H (vaultCommits H cells))[bo.index] = leaf H bo.index (cellBlind H cells[bo.index]) := by
    simp [leaves, vaultCommits]
  simp only [BlindedOpening.toBatchEntry] at hbind
  rw [hleaf] at hbind
  rcases hbind with heq | hcoll
  · exact leaf_binds (Nat.lt_trans hi hs) heq
  · exact .inr hcoll

/-- **Zero Unblinded Data Exposure**: A hidden cell's projected representation cannot evaluate to its raw content. -/
theorem projectCell_blinded_reveals_no_content (H : Hash) (v : List Auth) (c : VaultCell)
    (hhide : canSee v c = false) :
    ∀ val, (match projectCell H v c with
      | .revealed _ _ _ content => some content
      | .blinded _ _ => none) = some val → False := by
  intro val h
  unfold projectCell at h
  rw [hhide] at h
  contradiction

/-- **Binding Theorem for `cellBlind` (`cellBlind_binds`)**:
    Equal commitments imply equal `(id, readCap, writeCap, capMask, salt, content)` or a hash collision. -/
theorem cellBlind_binds {H : Hash} (hb : Bounded H) {c₁ c₂ : VaultCell}
    (hid₁ : c₁.id < 2 ^ 256) (hsalt₁ : c₁.salt < 2 ^ 256)
    (hid₂ : c₂.id < 2 ^ 256) (hsalt₂ : c₂.salt < 2 ^ 256)
    (heq : cellBlind H c₁ = cellBlind H c₂) :
    (c₁.id = c₂.id ∧ c₁.readCap = c₂.readCap ∧ c₁.writeCap = c₂.writeCap ∧
     c₁.capMask = c₂.capMask ∧ c₁.salt = c₂.salt ∧ c₁.content = c₂.content) ∨ Collision H := by
  unfold cellBlind cellBlindMetadataBoundValues at heq
  have hadm_top₁ : Admissible (digestWith H c₁.id (digestWith H c₁.readCap (digestWith H c₁.writeCap c₁.capMask))) :=
    admissible_of_lt (hb _ _)
  have hadm_top₂ : Admissible (digestWith H c₂.id (digestWith H c₂.readCap (digestWith H c₂.writeCap c₂.capMask))) :=
    admissible_of_lt (hb _ _)
  rcases binds_or_collides H hadm_top₁ hadm_top₂ heq with ⟨h_meta, h_body⟩ | hcoll
  · have hadm_meta₁ : Admissible c₁.id := admissible_of_lt hid₁
    have hadm_meta₂ : Admissible c₂.id := admissible_of_lt hid₂
    rcases binds_or_collides H hadm_meta₁ hadm_meta₂ h_meta with ⟨hid_eq, h_caps⟩ | hcoll
    · have hadm_caps₁ : Admissible c₁.readCap := admissible_of_lt (readCapOf_lt c₁.required)
      have hadm_caps₂ : Admissible c₂.readCap := admissible_of_lt (readCapOf_lt c₂.required)
      rcases binds_or_collides H hadm_caps₁ hadm_caps₂ h_caps with ⟨hread_eq, h_wcaps⟩ | hcoll
      · have hadm_wcaps₁ : Admissible c₁.writeCap := admissible_of_lt (writeCapOf_lt c₁.required)
        have hadm_wcaps₂ : Admissible c₂.writeCap := admissible_of_lt (writeCapOf_lt c₂.required)
        rcases binds_or_collides H hadm_wcaps₁ hadm_wcaps₂ h_wcaps with ⟨hwrite_eq, hmask_eq⟩ | hcoll
        · have hadm_body₁ : Admissible c₁.salt := admissible_of_lt hsalt₁
          have hadm_body₂ : Admissible c₂.salt := admissible_of_lt hsalt₂
          rcases binds_or_collides H hadm_body₁ hadm_body₂ h_body with ⟨hsalt_eq, hcont_eq⟩ | hcoll
          · left
            exact ⟨hid_eq, hread_eq, hwrite_eq, hmask_eq, hsalt_eq, hcont_eq⟩
          · right; exact hcoll.global
        · right; exact hcoll.global
      · right; exact hcoll.global
    · right; exact hcoll.global
  · right; exact hcoll.global

/-- **Metadata Tampering Refusal Theorem (`tampered_metadata_opening_refused`)**:
    Under a bounded hash `H`, tampering with `cell.id` or `cell.readCap` (or `cell.writeCap` /
    `cell.capMask`) in an opening at index `j < cells.length` invalidates `verifyBlindedOpening`
    against `projectedMerkleRoot H v cells`, or exhibits a collision of `H`. (Stated up to
    `Collision H`, the spine's form: `¬ Collision H` is false for every fixed-width hash by
    pigeonhole, so a theorem assuming it says nothing at `deployed`.) -/
theorem tampered_metadata_opening_refused {H : Hash} (hb : Bounded H)
    (v : List Auth) (cells : List VaultCell) (j : Nat) (c_tampered : VaultCell)
    (hj : j < cells.length) (hjs : j < 2 ^ 256)
    (hid_orig : (cells.getD j default).id < 2 ^ 256)
    (hsalt_orig : (cells.getD j default).salt < 2 ^ 256)
    (hid_tamp : c_tampered.id < 2 ^ 256)
    (hsalt_tamp : c_tampered.salt < 2 ^ 256)
    (h_tampered : c_tampered.id ≠ (cells.getD j default).id ∨
                  c_tampered.readCap ≠ (cells.getD j default).readCap) :
    verifyBlindedOpening H
      { mkBlindedOpening H v cells j with cell := projectCell H v c_tampered }
      (projectedMerkleRoot H v cells) = false ∨ Collision H := by
  cases hver : verifyBlindedOpening H
      { mkBlindedOpening H v cells j with cell := projectCell H v c_tampered }
      (projectedMerkleRoot H v cells) with
  | false => exact Or.inl rfl
  | true =>
    right
    rw [projectedMerkleRoot_eq_vaultRoot, verifyBlindedOpening_eq_opens] at hver
    unfold mkBlindedOpening at hver
    dsimp only at hver
    have hlen : j < (vaultCommits H cells).length := by
      simp [vaultCommits, hj]
    have h_honest := opens_complete hb (vaultCommits H cells) j hlen hjs
    rcases opens_binds hb hver h_honest rfl rfl with hval_eq | hcoll
    · dsimp only [mapOpening] at hval_eq
      rw [projectCell_commit_eq] at hval_eq
      have hget : (vaultCommits H cells).getD j 0 = cellBlind H (cells.getD j default) :=
        getD_map_helper (cellBlind H) default 0 cells j hj
      rw [hget] at hval_eq
      rcases cellBlind_binds hb hid_tamp hsalt_tamp hid_orig hsalt_orig hval_eq with
        ⟨hid_eq, hread_eq, _, _, _, _⟩ | hcoll
      · rcases h_tampered with hne_id | hne_read
        · exact absurd hid_eq hne_id
        · exact absurd hread_eq hne_read
      · exact hcoll
    · exact hcoll

/-- **Full 8-Capability Mask Tampering Refusal (`tampered_capMask_opening_refused`)**:
    Under a bounded hash `H`, tampering with any of the 8 `Auth` capabilities
    (`c_tampered.capMask ≠ (cells.getD j default).capMask`) invalidates `verifyBlindedOpening`
    against `projectedMerkleRoot H v cells`, or exhibits a collision of `H`. -/
theorem tampered_capMask_opening_refused {H : Hash} (hb : Bounded H)
    (v : List Auth) (cells : List VaultCell) (j : Nat) (c_tampered : VaultCell)
    (hj : j < cells.length) (hjs : j < 2 ^ 256)
    (hid_orig : (cells.getD j default).id < 2 ^ 256)
    (hsalt_orig : (cells.getD j default).salt < 2 ^ 256)
    (hid_tamp : c_tampered.id < 2 ^ 256)
    (hsalt_tamp : c_tampered.salt < 2 ^ 256)
    (h_tampered : c_tampered.capMask ≠ (cells.getD j default).capMask) :
    verifyBlindedOpening H
      { mkBlindedOpening H v cells j with cell := projectCell H v c_tampered }
      (projectedMerkleRoot H v cells) = false ∨ Collision H := by
  cases hver : verifyBlindedOpening H
      { mkBlindedOpening H v cells j with cell := projectCell H v c_tampered }
      (projectedMerkleRoot H v cells) with
  | false => exact Or.inl rfl
  | true =>
    right
    rw [projectedMerkleRoot_eq_vaultRoot, verifyBlindedOpening_eq_opens] at hver
    unfold mkBlindedOpening at hver
    dsimp only at hver
    have hlen : j < (vaultCommits H cells).length := by
      simp [vaultCommits, hj]
    have h_honest := opens_complete hb (vaultCommits H cells) j hlen hjs
    rcases opens_binds hb hver h_honest rfl rfl with hval_eq | hcoll
    · dsimp only [mapOpening] at hval_eq
      rw [projectCell_commit_eq] at hval_eq
      have hget : (vaultCommits H cells).getD j 0 = cellBlind H (cells.getD j default) :=
        getD_map_helper (cellBlind H) default 0 cells j hj
      rw [hget] at hval_eq
      rcases cellBlind_binds hb hid_tamp hsalt_tamp hid_orig hsalt_orig hval_eq with
        ⟨_, _, _, hmask_eq, _, _⟩ | hcoll
      · exact absurd hmask_eq h_tampered
      · exact hcoll
    · exact hcoll

/-- **A revealed cell in a verifying multiproof is the vault's cell** at that position, field by
field, or `H` collides: id, both capability words, the capability mask, the salt and the content. -/
theorem verifyBlindedMultiProof_revealed_binds {H : Hash} (hb : Bounded H) (cells : List VaultCell)
    (hs : cells.length < 2 ^ 256) {bmp : BlindedMultiProof}
    (h : verifyBlindedMultiProof H bmp = true)
    (hroot : bmp.vaultRoot = mapRoot H (vaultCommits H cells)) (hsize : bmp.size = cells.length)
    {bo : BlindedOpening} (hbo : bo ∈ bmp.openings) (hi : bo.index < cells.length)
    {id : Nat} {req : List Auth} {salt content : Nat}
    (hcell : bo.cell = .revealed id req salt content)
    (hid : id < 2 ^ 256) (hsalt : salt < 2 ^ 256)
    (hid' : cells[bo.index].id < 2 ^ 256) (hsalt' : cells[bo.index].salt < 2 ^ 256) :
    (id = cells[bo.index].id ∧ readCapOf req = cells[bo.index].readCap ∧
      writeCapOf req = cells[bo.index].writeCap ∧ capMaskOf req = cells[bo.index].capMask ∧
      salt = cells[bo.index].salt ∧ content = cells[bo.index].content) ∨ Collision H := by
  rcases verifyBlindedMultiProof_binds hb cells hs h hroot hsize hbo hi with heq | hcoll
  · rw [hcell] at heq
    have heq' : cellBlind H ⟨id, req, salt, content⟩ = cellBlind H cells[bo.index] := heq
    rcases cellBlind_binds hb hid hsalt hid' hsalt' heq' with hf | hcoll
    · exact .inl hf
    · exact .inr hcoll
  · exact .inr hcoll

end Obend.Vault.Projection

