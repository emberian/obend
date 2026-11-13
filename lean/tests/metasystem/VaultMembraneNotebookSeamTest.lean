module
/-
# The vault, membrane and notebook seams, on small fixtures

Each section runs one seam's universal theorems on a fixture and mutates the checks they rest on.

1. **Snapshot chunk index** (`section SnapshotsAndContinuation`). Chunk `c + 2^60` shares chunk
   `c`'s 64-bit key; `verifyDualChunkOpening` accepts every real chunk and refuses the wrapped one,
   and the snapshot root commits to the chunk count.
2. **Portable continuation** (same section). `cU64` refuses `n + 2^64`; a membrane entry carries
   and roundtrips its 256-bit bearer secret; an archive rehydrates the replay world through the
   sharded checkpoint and passes the WAL snapshot check; a custody receipt is accepted in the vault
   and under the mandate it names and refused in any other.
3. **Membranes and the notebook** (`section MembraneNotebook`). A transclusion opens a field under
   its 256-bit salt: the salted opening is admitted, the unsalted and the wrong-salt ones are
   refused. A notebook cell has one address in a membrane world. A viewer's frustum of a notebook,
   with its redacted upstream cell behind a sealed boundary, computes the visible receipts of the
   whole run; a tampered boundary opening is refused; and `Frustum.snip` makes the same cut.

Kernel proofs here evaluate no hash: they instantiate the library's theorems. Runs that compute
cSHAKE256 are `#guard`s.
-/
public import Obend.Vault.TransclusionAndMirror
public import Obend.Vault.Escrow
public import Obend.Tactic.Tooth
meta import Obend.Vault.TransclusionAndMirror
meta import Obend.Doc.ReactiveNotebook
meta import Obend.Vault.Escrow
import all Obend.Vault.WorldTree
import all Obend.Vault.Escrow
import all Obend.Vault.SurviveFirePor
import all Obend.Vault.Replay
import all Obend.Tactic.Tooth
import all Obend.Vault.FrustumMembrane
import all Obend.Doc.ReactiveNotebook
import all Obend.Vault.TransclusionAndMirror

public section

namespace Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest

set_option autoImplicit false

section SnapshotsAndContinuation

open Obend.Vault Obend.Vault.VerkleSnapshotBridge Obend.Vault.SurviveFirePor
open Obend.Vault.PortableContinuation Obend.Vault.ChunkedWorld
open Obend.Judge.Computational (HashCollisionWitness)

/-! ## 1. `[HIGH-04]` Snapshot chunk index: `c + 2^60` is refused, not aliased to `c` -/

/-- The aliasing the audit found is real at the address level: chunk `c + 2^60` has chunk `c`'s
64-bit `VerkleUmem` key, so only the verifier's index bound separates them. -/
theorem slotAddr_wraps (c j : Nat) : slotAddr (c + 2 ^ 60) j = slotAddr c j := by
  apply UInt64.toNat_inj.1
  simp only [slotAddr, chunkSlots, UInt64.toNat_ofNat']
  omega

/-- Positive: every chunk `c < 256` of every well-formed snapshot opens against its snapshot root. -/
theorem valid_chunk_accepted {pp : Obend.Crypto.AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) {c j : Nat}
    (hc : c < numChunks) (hj : j < chunkSlots) :
    verifyDualChunkOpening pp hCols s.snapshotRoot (s.ajtaiChunkRoots.getD c []) c j
      (s.readSlot c j) (openDualSnapshotSlot s c j) = true :=
  openDualSnapshotSlot_valid hwf hc hj

/-- Refusal: chunk `c`'s honest opening never authenticates index `c + 2^60`, for any claimed value
and any Ajtai root, although both indices share one `slotAddr`. -/
theorem wrapped_chunk_refused {pp : Obend.Crypto.AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) (c j : Nat) (a : List Int)
    (v : UInt64) :
    verifyDualChunkOpening pp hCols s.snapshotRoot a (c + 2 ^ 60) j v
      (openDualSnapshotSlot s c j) = false := by
  cases h : verifyDualChunkOpening pp hCols s.snapshotRoot a (c + 2 ^ 60) j v
      (openDualSnapshotSlot s c j) with
  | false => rfl
  | true =>
    have hb := (verifyDualChunkOpening_header h).1
    have hn : (openDualSnapshotSlot s c j).chunkCount = numChunks := hwf.1
    rw [hn] at hb; unfold numChunks at hb; omega

/-- Refusal against every opening, not only the honest one: an accepted opening at an index outside
the snapshot yields a named `treeHash` collision between two snapshot-root headers. -/
def out_of_range_opening_collides {pp : Obend.Crypto.AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) {c j : Nat} (hc : numChunks ≤ c)
    {a : List Int} {v : UInt64} {w : DualChunkSlotOpening}
    (h : verifyDualChunkOpening pp hCols s.snapshotRoot a c j v w = true) :
    PathCollision [snapshotRootPreimage w.chunkCount w.verkleRoot]
      [snapshotRootPreimage s.chunks.size s.verkleRoot] :=
  match extractSnapshotIndexBreak hwf h with
  | .inl hin => absurd hin.1 (Nat.not_lt.2 hc)
  | .inr col => col

-- Dropping the `c < chunkCount` bound from the verifier lets the wrapped index through.
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.wrapped_chunk_refused by mutation
  Obend.Vault.VerkleSnapshotBridge.verifyDualChunkOpening := fun pp hCols snapshotRoot ajtaiRoot c j val w =>
    if hlen : w.chunkSlotsList.length = 16 then
      if hj : j < 16 then
        ((w.chunkSlotsList[j]'(by omega) == val) &&
         checkWellSizedVerklePath w.verklePath &&
         Obend.Polis.verifyOpening w.verkleRoot (slotAddr c j) val w.verklePath &&
         decide (Obend.Crypto.ajtaiCommit pp (wordsToLimbs w.chunkSlotsList)
           (by rw [wordsToLimbs_length, hlen, hCols]) = ajtaiRoot)) &&
        (decide (chunkSlots * w.chunkCount ≤ 2 ^ 64) && w.verkleRoot.size == 32 &&
         decide (snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot))
      else false
    else false

-- Leaving the chunk count out of the snapshot-root preimage breaks root binding.
#tooth Obend.Vault.VerkleSnapshotBridge.snapshotRootPreimage_injective by mutation
  Obend.Vault.VerkleSnapshotBridge.snapshotRootPreimage := fun _n verkleRoot =>
    2 :: Obend.Polis.encodeFields [verkleRoot.data.toList]

/-! Concrete witnesses on the genesis world (compiled evaluation of the real hashes). -/

/-- One evaluation: build a snapshot, open chunk 42, and present that opening at the real index,
at the wrapped index, and at the wrapped index under an inflated chunk count. -/
def wrappedIndexSuite : Bool :=
  let snap := updateChunkVerkleRoot defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
    (buildAuthenticatedSnapshot defaultChunkAjtaiParams defaultChunkAjtaiParams_cols Replay.genesis) 42 (by decide)
    (zeroChunk.setSlot 0 0xFEDCBA9876543210)
  let root := snap.snapshotRoot
  let dual := openDualSnapshotSlot snap 42 0
  let ajtai := snap.ajtaiChunkRoots.getD 42 []
  let verify := fun (c : Nat) (w : DualChunkSlotOpening) =>
    verifyDualChunkOpening defaultChunkAjtaiParams defaultChunkAjtaiParams_cols root ajtai c 0 0xFEDCBA9876543210 w
  verify 42 dual && slotAddr (42 + 2 ^ 60) 0 == slotAddr 42 0 &&
    !verify (42 + 2 ^ 60) dual && !verify (42 + 2 ^ 60) { dual with chunkCount := 2 ^ 60 + 43 } &&
    !verify (42 + 2 ^ 60) { dual with chunkCount := 2 ^ 60 }

#guard wrappedIndexSuite

/-! ## 2. Portable continuation: canonical `cU64`, 256-bit bearer secrets, replay bridge, receipts -/

/-- Refusal: `n + 2^64` is not a second encoding of `n`; the decoder returns `none`. -/
theorem cU64_overflow_refused (n : Nat) (rest : Log.Bytes) :
    cU64.dec (cNat.enc (n + 2 ^ 64) ++ rest) = none :=
  cU64_dec_refuses_overflow _ (by omega) rest

/-- Positive: every `UInt64` roundtrips before any suffix. -/
theorem cU64_roundtrips (v : UInt64) (rest : Log.Bytes) :
    cU64.dec (cU64.enc v ++ rest) = some (v, rest) := cU64.roundtrip v rest

-- The pre-repair decoder (reduce modulo `2^64`) accepts the overflowing natural.
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.cU64_overflow_refused by mutation
  Obend.Vault.PortableContinuation.cU64 :=
    cMap UInt64.toNat (fun n => some (UInt64.ofNat n)) (by intro n; simp) cNat

/-- Positive: a membrane entry with its full 256-bit bearer secret roundtrips through the codec. -/
theorem sturdyEntry_roundtrips (e : SturdyMembraneEntry) :
    cSturdyMembraneEntry.decodeExact (cSturdyMembraneEntry.enc e) = some e :=
  FastCodec.decodeExact_enc _ e

/-- All 32 secret bytes are on the wire: entries with equal encodings are equal. -/
theorem sturdyEntry_wire_injective (a b : SturdyMembraneEntry)
    (h : cSturdyMembraneEntry.enc a = cSturdyMembraneEntry.enc b) : a = b :=
  Option.some.inj ((FastCodec.decodeExact_enc _ a).symm.trans (h ▸ FastCodec.decodeExact_enc _ b))

-- Authenticating a bearer by the 64-bit locator alone breaks `lookupMembrane_sound`.
#tooth Obend.Vault.PortableContinuation.lookupMembrane_sound by mutation
  Obend.Vault.PortableContinuation.SovereignHome.lookupMembrane := fun h secret =>
    h.membranes.find? fun e => decide (swissLocator e.swissNum = swissLocator secret)

/-- Positive: archive → sharded checkpoint → replay world is lossless. -/
theorem archive_world_roundtrips (a : HomeArchive) (h : HomeArchiveFits a) :
    (archiveToSharded (encodeHomeArchiveCbor a)).bind rehydrateWorld = some a.home.world :=
  archive_sharded_rehydrate a h

#tooth Obend.Vault.PortableContinuation.archive_sharded_rehydrate by mutation
  Obend.Vault.PortableContinuation.rehydrateWorld := fun _ => some Replay.genesis

/-- The WAL check is sound as a proposition: a passing home has the replayed world's root, or two
snapshot-root headers collide. -/
theorem wal_check_sound (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) (h : checkHomeAgainstWal pp hCols home wal = true) :
    fullVerkleCommitWorld home.world = fullVerkleCommitWorld (Log.replay Replay.deployed
        Replay.genesis (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1) ∨
      Nonempty (HashCollisionWitness Obend.Polis.treeHash verkleMaxPreimageBytes) :=
  match checkHomeAgainstWal_sound pp hCols home wal h with
  | .inl e => .inl e
  | .inr c => .inr ⟨c⟩

def homeSeam : SovereignHome :=
  ⟨Replay.genesis, [], [], [], ⟨⟨(List.replicate 32 (0x37 : UInt8)).toArray⟩, by decide⟩, [],
    ⟨⟨(List.replicate 32 (0x37 : UInt8)).toArray⟩, by decide⟩⟩
/-- Inhabited premises: the genesis session is reachable, the empty history is valid, and a registry
whose live slot holds the genesis home has that home's origin; so the live home passes the WAL
check against the empty log (or a collision exists). -/
theorem genesis_home_passes_wal_check (key : Digest256) :
    checkHomeAgainstWal defaultChunkAjtaiParams defaultChunkAjtaiParams_cols homeSeam [] = true := by
  have h := migratedHome_passes_wal_check_or_collision defaultChunkAjtaiParams defaultChunkAjtaiParams_cols homeSeam key
    ⟨7, 0, some ⟨1, homeSeam.receiptGenesis, 0, homeSeam⟩, none, [], []⟩ _ [] (.nil _)
    ⟨fun _ hl => by cases hl; rfl, fun _ hp => by cases hp⟩
    ⟨Replay.genesis, []⟩ Log.Reachable.genesis rfl ⟨1, homeSeam.receiptGenesis, 0, homeSeam⟩ rfl
    (tornTail := []) (.inl rfl)
  rcases h with h | ⟨a, b, ha, _⟩
  · exact h
  · simp [migrationPreimages] at ha

-- A home whose world minted one unit does not match the empty WAL.
#guard !checkHomeAgainstWal defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
  { homeSeam with world := { Replay.genesis with minted := 1 } } []

/-- Positive: an executed transfer's receipt is accepted in the vault and mandate it names. -/
theorem receipt_accepted_in_its_vault (s : CustodyState) (amount : Nat)
    (hs : amount ≤ s.balances.source) (ha : amount ≤ s.balances.allowance) :
    checkKernelTransitionReceipt s (makeTransitionReceipt s amount) = true :=
  checkKernelTransitionReceipt_complete s amount hs ha

/-- Refusal: the same receipt is refused by any other vault. -/
theorem receipt_refused_in_other_vault (s : CustodyState) (amount : Nat) (other : Digest256)
    (h : other ≠ s.vaultId) :
    checkKernelTransitionReceipt { s with vaultId := other } (makeTransitionReceipt s amount) = false :=
  checkKernelTransitionReceipt_refuses_foreign _ _ (.inl fun (e : s.vaultId = other) => h e.symm)

/-- Refusal: the same receipt is refused under any other mandate. -/
theorem receipt_refused_under_other_mandate (s : CustodyState) (amount : Nat) (other : Digest256)
    (h : other ≠ s.mandateId) :
    checkKernelTransitionReceipt { s with mandateId := other } (makeTransitionReceipt s amount) = false :=
  checkKernelTransitionReceipt_refuses_foreign _ _ (.inr fun (e : s.mandateId = other) => h e.symm)

/-- One commitment accepted in two custody states names one vault and one mandate, or collides. -/
theorem receipt_commitment_binds_vault_and_mandate (sa sb : CustodyState)
    (a b : VaultTransitionReceipt) (ha : checkKernelTransitionReceipt sa a = true)
    (hb : checkKernelTransitionReceipt sb b = true) (h : a.commitment = b.commitment) :
    (sa.vaultId = sb.vaultId ∧ sa.mandateId = sb.mandateId ∧ a = b) ∨
      Obend.Digest.HashBytes.CollisionAmong
        (Obend.Digest.Cshake256.cshake256Bytes transitionTag.toUTF8.data.toList)
        (fun x => x = (cTransitionPayload.encodeArray a.payload).data.toList ∨
          x = (cTransitionPayload.encodeArray b.payload).data.toList) :=
  match acceptedReceipt_binding sa sb a b ha hb h with
  | .inl e => .inl ⟨e.2.1, e.2.2.1, e.1⟩
  | .inr c => .inr c.toCollisionAmong

-- The pre-repair check (no vault or mandate comparison) admits the foreign receipt.
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.receipt_refused_in_other_vault by mutation
  Obend.Vault.SurviveFirePor.checkKernelTransitionReceipt := fun state r =>
    decide (r.amount ≤ state.balances.source) && decide (r.amount ≤ state.balances.allowance) &&
      decide (r.after = ⟨state.balances.source - r.amount,
        state.balances.destination + r.amount, state.balances.allowance - r.amount⟩) &&
      decide (r.previous = state.receiptHead) && decide (r.epoch = state.epoch + 1) &&
      decide (r.commitment = transitionCommitment r)

-- The pre-repair preimage (no vault or mandate identifier) cannot bind a receipt to its vault.
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.receipt_commitment_binds_vault_and_mandate by mutation
  Obend.Vault.SurviveFirePor.VaultTransitionReceipt.payload := fun r =>
    (r.previous, r.previous, r.previous, r.epoch, r.amount, r.after)

end SnapshotsAndContinuation

/-! ## 3. Membranes and the notebook -/

section MembraneNotebook

open Obend.Vault.FrustumMembrane (SealedSlot sealPreimage sealCustomization)
open Obend.Vault.TransclusionAndMirror
open Obend.Doc.Reactive
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.HashBytes (CollisionAmong)

/-- A 256-bit salt. -/
def salt (b : UInt8) : List UInt8 := List.replicate 32 b

/-! ### A transclusion opens its field under the field's salt -/

def titleReceipt : Receipt := ⟨genesisDigest, 0, [("title", ⟨[7], salt 1⟩)]⟩
def titleSource : SourceCell := ⟨[titleReceipt], []⟩

/-- The title quoted with its salt; with no salt; and under another 256-bit salt. -/
def salted : Transclusion := ⟨receiptDigest titleReceipt.header, 0, "title", ⟨[7], salt 1⟩⟩
def unsalted : Transclusion := { salted with opening := ⟨[7], []⟩ }
def wrongSalt : Transclusion := { salted with opening := ⟨[7], salt 2⟩ }

/-- The salted opening is admitted. -/
theorem salted_opening_admitted :
    admitTransclusion titleSource.observed salted = .ok ⟨[7], 0, 0⟩ :=
  admit_of_find (hd := titleReceipt.header)
    (by simp [titleSource, SourceCell.observed, salted]) rfl
    (by simp [titleReceipt, Receipt.header, salted]) (by decide)

/-- The unsalted opening is refused, against this chain and any other. -/
example (chain : List ReceiptHeader) (d : DatedQuote) : admitTransclusion chain unsalted ≠ .ok d :=
  transclusion_unsalted_refused chain unsalted (by decide) d

/-- The right bytes under the wrong salt are refused, or the two sealed slots collide. -/
example : admitTransclusion titleSource.observed wrongSalt = .error .digestMismatch ∨
    CollisionAmong (cshake256Bytes sealCustomization) (fun x =>
      x = sealPreimage (fieldSlot "title" ⟨[7], salt 2⟩) ∨
      x = sealPreimage (fieldSlot "title" ⟨[7], salt 1⟩)) :=
  transclusion_wrong_salt_refused_or_collides salted_opening_admitted rfl rfl rfl
    (by decide) (by decide)

def refusal (r : Except TransclusionRefusal DatedQuote) : Option TransclusionRefusal :=
  match r with
  | .ok _ => none
  | .error e => some e

#guard refusal (admitTransclusion titleSource.observed salted) == none
#guard refusal (admitTransclusion titleSource.observed unsalted) == some (.saltWidth 0)
#guard refusal (admitTransclusion titleSource.observed wrongSalt) == some .digestMismatch
#guard fieldCommit "title" ⟨[7], salt 1⟩ != fieldCommit "title" ⟨[7], salt 2⟩

/-! ### One address for a cell -/

example (a : Obend.Doc.AtomId) : atomOfAddress (cellAddress a) = some a :=
  atomOfAddress_cellAddress a

#guard cellAddress 42 == "42"
#guard atomOfAddress "42" == some 42
-- Only the canonical numeral is an address.
#guard atomOfAddress "042" == none
#guard atomOfAddress "alice" == none

/-! ### A frustum of a notebook -/

def lit (n : Int) : Instruction := ⟨.literal, n⟩
def input (n : Nat) : Instruction := ⟨.input, n⟩
def add : Instruction := ⟨.add, 0⟩
def mul : Instruction := ⟨.mul, 0⟩

/-- Cell 1 holds a rate its owner does not show. Cells 2 and 3 are downstream of it. -/
def ledger : List ReactiveCell := [
  ⟨1, .obendCode, [], ["rate"], [[lit 41]], "the rate"⟩,
  ⟨2, .casSymbolic, ["rate"], ["quote"], [[input 0, lit 1, add]], "rate plus one"⟩,
  ⟨3, .lawContract, ["quote"], ["double"], [[input 0, lit 2, mul]], "twice the quote"⟩]

/-- The viewer may see cells 2 and 3. -/
def viewer : List CellId := [2, 3]

def symbolSalt (s : String) : List UInt8 := List.replicate 32 (UInt8.ofNat s.length)

theorem symbolSalt_width (s : String) : (symbolSalt s).length = 32 := by simp [symbolSalt]

example : checkNotebookDag ledger = true := by decide
example : frustumClosed viewer ledger = true := by decide

/-- The viewer's run is the visible part of the whole run, receipts included, under any kernel. -/
theorem ledger_snip (k : CellKernel) :
    evalSnip k (snipNotebook k symbolSalt viewer ledger) =
      .ok (snipCache viewer (evalFromScratch k ledger).cells) :=
  (snip_preserves_receipts k symbolSalt viewer ledger (by decide) symbolSalt_width).1

/-- Each visible cell's receipt is the whole run's receipt for that cell. -/
example (k : CellKernel) (i : CellId) (hi : i ∈ viewer) :
    (cacheLookup (snipCache viewer (evalFromScratch k ledger).cells) i).map (·.result.receipt) =
      (cacheLookup (evalFromScratch k ledger).cells i).map (·.result.receipt) := by
  rw [(snip_preserves_receipts k symbolSalt viewer ledger (by decide) symbolSalt_width).2 i hi]

/-- What the viewer holds: the two visible cells with their values, and one opening. -/
example (hash : List UInt8 → BitVec 256) :
    (snipCache viewer (evalFromScratch ⟨arithmeticRun, hash⟩ ledger).cells).map
      (fun x => (x.cell.id, x.result.values)) = [(2, [42]), (3, [84])] := by rfl

example (hash : List UInt8 → BitVec 256) :
    (snipNotebook ⟨arithmeticRun, hash⟩ symbolSalt viewer ledger).openings =
      [⟨"rate", 41, symbolSalt "rate"⟩] := by rfl

/-- The same snip with its one opening claiming 99 for the rate. -/
def tampered (k : CellKernel) : NotebookSnip :=
  { snipNotebook k symbolSalt viewer ledger with openings := [⟨"rate", 99, symbolSalt "rate"⟩] }

/-- If `evalSnip` admits the tampered opening, two sealed slots collide. -/
theorem tampered_boundary_refused_or_collides (hash : List UInt8 → BitVec 256)
    (out : List CachedCell)
    (h : evalSnip ⟨arithmeticRun, hash⟩ (tampered ⟨arithmeticRun, hash⟩) = .ok out) :
    CollisionAmong (cshake256Bytes sealCustomization)
      (boundaryPreimages symbolSalt
        (redactCache viewer (evalFromScratch ⟨arithmeticRun, hash⟩ ledger).cells)
        (tampered ⟨arithmeticRun, hash⟩).openings) := by
  rcases snip_tampered_refused_or_collides ⟨arithmeticRun, hash⟩ symbolSalt viewer ledger
    (by decide) _ rfl rfl h with ⟨hown, _⟩ | hcol
  · have hslot := (hown ⟨"rate", 99, symbolSalt "rate"⟩ (List.mem_singleton.mpr rfl)).2
    have hval : frameInt 99 = frameInt 41 := congrArg SealedSlot.secret hslot
    exact absurd (frameInt_injective hval) (by decide)
  · exact hcol

def snipRefusal (r : Except SnipRefusal (List CachedCell)) : Option SnipRefusal :=
  match r with
  | .ok _ => none
  | .error e => some e

def ownerSnip : NotebookSnip := snipNotebook scientificKernel symbolSalt viewer ledger

#guard snipRefusal (evalSnip scientificKernel ownerSnip) == none
#guard snipRefusal (evalSnip scientificKernel (tampered scientificKernel)) ==
  some (.opening "rate" .digestMismatch)
-- The right value with no salt, the right value under another salt, and no opening at all.
#guard snipRefusal (evalSnip scientificKernel
    { ownerSnip with openings := [⟨"rate", 41, []⟩] }) == some (.opening "rate" (.saltWidth 0))
#guard snipRefusal (evalSnip scientificKernel
    { ownerSnip with openings := [⟨"rate", 41, salt 9⟩] }) == some (.opening "rate" .digestMismatch)
#guard snipRefusal (evalSnip scientificKernel { ownerSnip with openings := [] }) ==
  some (.unopened "rate")
-- With the cSHAKE256 receipts computed: the viewer's results are the whole run's.
#guard (match evalSnip scientificKernel ownerSnip with
  | .ok out => out.map (·.result) ==
      (snipCache viewer (evalFromScratch scientificKernel ledger).cells).map (·.result)
  | .error _ => false)

/-- An edit to visible cell 2. -/
def quoteEdit : NotebookAction := ⟨2, [[input 0, lit 10, add]]⟩

/-- The edit dirties the same cells on both sides, against the same boundary, and the viewer's
recompute is the visible part of the whole notebook's. -/
example (k : CellKernel) :
    (dirtyCone (snipCells viewer ledger) quoteEdit.target = dirtyCone ledger quoteEdit.target ∧
      ∀ i ∈ dirtyCone ledger quoteEdit.target, i ∈ viewer) ∧
    (snipNotebook k symbolSalt viewer (applyEdit quoteEdit ledger)).boundary =
      (snipNotebook k symbolSalt viewer ledger).boundary ∧
    recompute k quoteEdit (snipCache viewer (evalFromScratch k ledger).cells)
        (snipEnv (snipNotebook k symbolSalt viewer ledger).openings) [] =
      snipCache viewer (editCellAndRecompute k (evalFromScratch k ledger) quoteEdit).cells :=
  snip_edit_preserves_cone_and_receipts k symbolSalt viewer ledger quoteEdit
    (by decide) (by decide) (by decide)

example : dirtyCone ledger 2 = [2, 3] := by decide

-- Closure is needed: a viewer of cells 1 and 3 has redacted cell 2 between them, and its cone of
-- an edit to cell 1 misses cell 3.
example : frustumClosed [1, 3] ledger = false := by decide
example : dirtyCone (snipCells [1, 3] ledger) 1 = [1] ∧ dirtyCone ledger 1 = [1, 2, 3] := by decide

/-! Adversarial four-node diamond: A -> {B,C} -> D. -/
def diamond : List ReactiveCell := [
  ⟨1, .obendCode, [], ["A"], [[lit 2]], "A"⟩,
  ⟨2, .obendCode, ["A"], ["B"], [[input 0, lit 1, add]], "B"⟩,
  ⟨3, .obendCode, ["A"], ["C"], [[input 0, lit 2, mul]], "C"⟩,
  ⟨4, .obendCode, ["B", "C"], ["D"], [[input 0, input 1, add]], "D"⟩]
def diamondEdit : NotebookAction := ⟨1, [[lit 10]]⟩
theorem diamond_dag : checkNotebookDag diamond = true := by decide
theorem diamond_order (k : CellKernel) :
    RecomputeExecution k diamondEdit (evalFromScratch k diamond).cells (fun _ => 0) []
      (editCellAndRecompute k (evalFromScratch k diamond) diamondEdit).cells [1, 2, 3, 4] :=
  recompute_execution k diamondEdit _ _ []
theorem diamond_fresh_values (hash : List UInt8 → BitVec 256) :
    (editCellAndRecompute ⟨arithmeticRun, hash⟩ (evalFromScratch ⟨arithmeticRun, hash⟩ diamond)
      diamondEdit).cells.map (fun c => c.result.values) = [[10], [11], [20], [31]] := by rfl

theorem diamond_mediated_cut : frustumClosed [1, 4] diamond = false ∧
    dirtyCone (snipCells [1, 4] diamond) 1 = [1] ∧ dirtyCone diamond 1 = [1, 2, 3, 4] := by decide

/-- A snapshot snip is faithful, but editing across a hidden intermediary keeps D stale.
This concrete counterexample is why downstream closure is required for boundary reuse. -/
theorem diamond_stale_boundary (hash : List UInt8 → BitVec 256) :
    (recompute ⟨arithmeticRun, hash⟩ diamondEdit
      (snipCache [1, 4] (evalFromScratch ⟨arithmeticRun, hash⟩ diamond).cells)
      (snipEnv (snipNotebook ⟨arithmeticRun, hash⟩ symbolSalt [1, 4] diamond).openings) []).map
        (fun c => c.result.values) = [[10], [7]] := by rfl

theorem diamond_closed_cut (k : CellKernel) :
    recompute k ⟨2, [[input 0, lit 10, add]]⟩ (snipCache [2, 4] (evalFromScratch k diamond).cells)
      (snipEnv (snipNotebook k symbolSalt [2, 4] diamond).openings) [] =
    snipCache [2, 4] (editCellAndRecompute k (evalFromScratch k diamond)
      ⟨2, [[input 0, lit 10, add]]⟩).cells :=
  (snip_edit_preserves_cone_and_receipts k symbolSalt [2, 4] diamond _ diamond_dag
    (by decide) (by decide)).2.2

def cyclicSnip : NotebookSnip := ⟨[
  ⟨1, .obendCode, ["B"], ["A"], [[input 0]], ""⟩,
  ⟨2, .obendCode, ["A"], ["B"], [[input 0]], ""⟩], [], []⟩
theorem cyclic_snip_refused (k : CellKernel) : evalSnip k cyclicSnip = .error .invalidDag :=
  evalSnip_refuses_invalidDag k cyclicSnip (by decide)
theorem self_loop_snip_refused (k : CellKernel) :
    evalSnip k ⟨[⟨1, .obendCode, ["A"], ["A"], [[input 0]], ""⟩], [], []⟩ = .error .invalidDag :=
  evalSnip_refuses_invalidDag k _ (by decide)

#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.diamond_fresh_values by mutation
  Obend.Doc.Reactive.reuseOrEval := fun _ _ old _ _ => old
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.diamond_mediated_cut by mutation
  Obend.Doc.Reactive.frustumClosed := fun _ _ => true
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.cyclic_snip_refused by mutation
  Obend.Doc.Reactive.checkNotebookDag := fun _ => true
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.self_loop_snip_refused by mutation
  Obend.Doc.Reactive.checkNotebookDag := fun _ => true

#guard (editCellAndRecompute scientificKernel (evalFromScratch scientificKernel diamond) diamondEdit) ==
  evalFromScratch scientificKernel (applyEdit diamondEdit diamond)
#guard (match evalSnip scientificKernel (snipNotebook scientificKernel symbolSalt [1, 4] diamond) with
  | .ok out => out == snipCache [1, 4] (evalFromScratch scientificKernel diamond).cells
  | .error _ => false)
#guard (match evalSnip scientificKernel cyclicSnip with | .error .invalidDag => true | _ => false)

/-- A self-verified badge cannot invent skipped gates. -/
theorem mirror_invented_skip_refused : verifyMirrorBadge (fun _ => .passed) "page" genesisDigest
    ⟨.selfVerifiedLocal, [.proofSignature], ⟨"page", genesisDigest⟩⟩ = false := by decide
example : verifyMirrorBadge (fun _ => .passed) "page" genesisDigest
    ⟨.selfVerifiedLocal, [], ⟨"page", genesisDigest⟩⟩ = true := classify_verifies (by rfl)
#tooth Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest.mirror_invented_skip_refused by mutation
  Obend.Vault.TransclusionAndMirror.verifyMirrorBadge := fun _ _ _ _ => true

/-! ### The same cut, in the membrane -/

/-- Every pin `Frustum.snip` makes for the viewer, in the membrane face of the ledger's run, is a
visible cell reading a redacted one, each at its `cellAddress`. -/
example (k : CellKernel) (pin : Obend.Vault.FrustumMembrane.BoundaryPin)
    (hpin : pin ∈ ((notebookFrustum "viewer" symbolSalt (evalFromScratch k ledger).cells).snip
      (viewer.map cellAddress) (fun _ _ => .sever []) []).pins) :
    ∃ c ∈ snipCache viewer (evalFromScratch k ledger).cells,
    ∃ q ∈ redactCache viewer (evalFromScratch k ledger).cells,
      dependency q.cell c.cell ∧ pin.holder = cellAddress c.cell.id ∧
      pin.target = cellAddress q.cell.id := by
  obtain ⟨c, hc, q, hq, hd, hh, ht, _⟩ :=
    (notebook_cut_is_boundary "viewer" symbolSalt k ledger viewer _ [] (by decide)).1 pin hpin
  exact ⟨c, hc, q, hq, hd, hh, ht⟩

-- There is one such pin: cell 2 reads cell 1. The commitment the frustum shows there is the boundary.
#guard ((notebookFrustum "viewer" symbolSalt (evalFromScratch scientificKernel ledger).cells).snip
    (viewer.map cellAddress) (fun _ _ => .sever []) []).pins.map (fun p => (p.holder, p.target)) ==
  [("2", "1")]
#guard ((notebookFrustum "viewer" symbolSalt (evalFromScratch scientificKernel ledger).cells).reflect
    "1").map (·.sealed) == some ownerSnip.boundary

/-! ### Teeth -/

-- The opening check admits a salt of any width.
#tooth Obend.Vault.TransclusionAndMirror.transclusion_unsalted_refused by mutation
  Obend.Vault.TransclusionAndMirror.openingRefusal := fun commits field o =>
    match commits.lookup field with
    | none => some .fieldAbsent
    | some c => if fieldCommit field o = c then none else some .digestMismatch

-- The field slot leaves the salt out of what it seals.
#tooth Obend.Vault.TransclusionAndMirror.transclusion_wrong_salt_refused_or_collides by mutation
  Obend.Vault.TransclusionAndMirror.fieldSlot := fun name o => ⟨fieldPreimage name o.secret, []⟩

-- The field slot leaves the name out of what it seals.
#tooth Obend.Vault.TransclusionAndMirror.fieldCommit_binds by mutation
  Obend.Vault.TransclusionAndMirror.fieldSlot := fun _ o => o

-- `evalSnip` evaluates without checking an opening.
#tooth Obend.Vault.TransclusionAndMirror.snip_tampered_refused_or_collides by mutation
  Obend.Vault.TransclusionAndMirror.evalSnip := fun k n =>
    .ok (evalSchedule k n.cells (snipEnv n.openings))

-- The viewer's environment ignores what was opened.
#tooth Obend.Vault.TransclusionAndMirror.snip_preserves_receipts by mutation
  Obend.Vault.TransclusionAndMirror.snipEnv := fun _ _ => 0

-- Every visible set counts as closed downstream.
#tooth Obend.Vault.TransclusionAndMirror.snip_edit_preserves_cone_and_receipts by mutation
  Obend.Doc.Reactive.frustumClosed := fun _ _ => true

-- A cell's face in the membrane holds no capability to what it reads.
#tooth Obend.Vault.TransclusionAndMirror.notebook_cut_is_boundary by mutation
  Obend.Vault.TransclusionAndMirror.cellFace := fun salt _ x =>
    { state := .record [],
      sealed := x.cell.defs.map fun s => (s, fieldCommit s ⟨frameInt (published x s), salt s⟩),
      caps := [], lit := [], epoch := 0 }

-- The receipt preimage leaves out the inputs.
#tooth Obend.Doc.Reactive.receipt_binds by mutation
  Obend.Doc.Reactive.cellReceiptPreimage := fun c _ values =>
    Obend.Crypto.leb128 c.id ++ (frameStr c.kind.toLabel ++ (frameList frameStr c.reads ++
      (frameList frameStr c.defs ++ (frameList (frameList frameInstr) c.body ++
        (frameStr c.note ++ frameList frameInt values)))))

-- Every atom has the same membrane address.
#tooth Obend.Doc.Reactive.cellAddress_injective by mutation
  Obend.Doc.Reactive.cellAddress := fun _ => "0"

end MembraneNotebook

end Obend.Tests.Metasystem.VaultMembraneNotebookSeamTest

end
