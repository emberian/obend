module
/-
# Obend.SemanticKG.Databank — Content-Addressed `WorldTree` + `DetCbor` Databank & Redaction Confinement

Stage 1 of the 4-stage Verifiable Semantic Knowledge Graph (`Obend.SemanticKG`):
1. **256-Bit Content-Addressed Databank (`SemanticDatabank`, `DatabankRoot256`)**:
   - Anchors document chunks (`DocChunkEntry`) to `Obend.Vault.ChunkedWorld` (`World`, `logHashArray`)
     serialized deterministically via RFC 8949 §4.2 `Obend.Codec.DetCbor` (`encodeDetCbor_injective`,
     `decodeDetCbor_encodeDetCbor`) and committed under domain-separated 256-bit cSHAKE256
     (`Obend.Core.Digest.Digest256`).
   - Proves `databankCommit256With_binding` and `databankCommit256_binding` (up to `CollisionAmong H` /
     `Collision H`) plus constructive `0 Classical.choice` collision extractor `databankCommit256_extract`,
     alongside Merkle chunk inclusion proofs (`verifyDatabankChunkInclusion_binding`,
     `verifyDatabankChunkInclusion_complete`).
2. **Stateful JSON + Delimiter Redaction Confinement (`RedactionSlicePolicy`, `redaction_cannot_splice_tokens`)**:
   - Enforces strictly separated disclosed byte intervals (`e < s'`) whose complement `elidedGaps`
     satisfies both stateful RFC 8259 JSON value-string confinement (`VpaJson.checkJsonRedaction`) and
     token-delimiter boundary isolation (`gapDelimiterBounded`).
   - Proves multi-gap JSON grammar and key-set invariance (`redactionPolicy_preserves_json_grammar_and_keys`)
     and **`redaction_cannot_splice_tokens`**: every maximal token extracted from `applyRedactionPolicy doc pol`
     lies strictly inside a single disclosed interval `(ds, de) ∈ pol.disclosedSpans` (cannot bridge across
     any elided gap), enters at the identical `VpaJson.JState`, and is an exact un-truncated maximal token
     of the unredacted `doc` (`tok ∈ extractTokenSpans doc`).
-/
public import Obend.Vault.WorldTree
public import Obend.Codec.DetCbor
public import Obend.Core.Digest
public import Obend.Judge.VpaComplementAndJson
public import Obend.Judge.TranscriptPolicy
import all Obend.Codec.DetCbor
import all Obend.Core.Digest
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.SymbolicRegexBisim

public section
namespace Obend.SemanticKG

open Obend.Codec.DetCbor
open Obend.Digest.HashBytes
open Obend.Core.Digest
open Obend.Judge
open Obend.Judge.Commit (cshakeHasher spliceByteArray spliceByteArray_toList)

set_option autoImplicit false

/-! ## §1. 256-Bit Content-Addressed `DocChunkEntry` & `SemanticDatabank` -/

/-- Full-width 256-bit databank commitment (`BitVec 256`, zero scalar truncation). -/
abbrev DatabankRoot256 := Digest256

/-- Domain tag `"Obend.SemanticKG.Chunk/v1\x00"` as explicit ASCII bytes (kernel-reducible). -/
def chunkDomainTag : List UInt8 :=
  [0x4f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x53, 0x65, 0x6d, 0x61, 0x6e, 0x74, 0x69, 0x63,
   0x4b, 0x47, 0x2e, 0x43, 0x68, 0x75, 0x6e, 0x6b, 0x2f, 0x76, 0x31, 0x00]

/-- Domain tag `"Obend.SemanticKG.Root/v1\x00"` as explicit ASCII bytes (kernel-reducible). -/
def databankDomainTag : List UInt8 :=
  [0x4f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x53, 0x65, 0x6d, 0x61, 0x6e, 0x74, 0x69, 0x63,
   0x4b, 0x47, 0x2e, 0x52, 0x6f, 0x6f, 0x74, 0x2f, 0x76, 0x31, 0x00]

/-- Domain tag `"Obend.SemanticKG.World/v1\x00"` binding `ChunkedWorld` manifest digests. -/
def worldLinkDomainTag : List UInt8 :=
  [0x4f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x53, 0x65, 0x6d, 0x61, 0x6e, 0x74, 0x69, 0x63,
   0x4b, 0x47, 0x2e, 0x57, 0x6f, 0x72, 0x6c, 0x64, 0x2f, 0x76, 0x31, 0x00]

/-- Customization string for Merkle inclusion of `DocChunkEntry` leaves. -/
def databankChunkSpanTag : String := "obend.semantickg.chunk.merkle.v1"

/-- Content-addressed document chunk entry in a `SemanticDatabank`. -/
structure DocChunkEntry where
  docId          : Nat
  byteOffset     : Nat
  rawBytes       : ByteArray
  chunkDigest256 : DatabankRoot256
  deriving DecidableEq

/-- Canonical CBOR tuple for `(docId, byteOffset, rawBytes)` prior to hashing `chunkDigest256`. -/
def chunkPayloadCbor (docId byteOffset : Nat) (rawBytes : ByteArray) : CborVal :=
  .array [.uint (UInt64.ofNat docId), .uint (UInt64.ofNat byteOffset), .bytes rawBytes]

/-- Domain-separated preimage for `chunkDigest256`. -/
def chunkPreimage (docId byteOffset : Nat) (rawBytes : ByteArray) : List UInt8 :=
  chunkDomainTag ++ (encodeDetCbor (chunkPayloadCbor docId byteOffset rawBytes)).data.toList

/-- Generic hash-parameterized 256-bit chunk digest. -/
def computeChunkDigest256With (H : Hash) (docId byteOffset : Nat) (rawBytes : ByteArray) : DatabankRoot256 :=
  hashOfHashBytes256 H (chunkPreimage docId byteOffset rawBytes)

/-- Deployed cSHAKE256 256-bit chunk digest. -/
def computeChunkDigest256 (docId byteOffset : Nat) (rawBytes : ByteArray) : DatabankRoot256 :=
  computeChunkDigest256With deployed docId byteOffset rawBytes

/-- Construct an authenticated `DocChunkEntry` from `(docId, byteOffset, rawBytes)`. -/
@[expose] def mkDocChunk (docId byteOffset : Nat) (rawBytes : ByteArray) : DocChunkEntry where
  docId := docId
  byteOffset := byteOffset
  rawBytes := rawBytes
  chunkDigest256 := computeChunkDigest256 docId byteOffset rawBytes

/-- 64-bit CBOR width bounds on a `DocChunkEntry` ensuring injective `UInt64` & `ByteArray` encoding. -/
def WfDocChunkBounds (c : DocChunkEntry) : Bool :=
  decide (c.docId < 18446744073709551616) &&
  decide (c.byteOffset < 18446744073709551616) &&
  decide (c.rawBytes.size < 18446744073709551616)

/-- Full chunk well-formedness: width bounds hold and `chunkDigest256` matches `rawBytes`. -/
def WfDocChunk (c : DocChunkEntry) : Bool :=
  WfDocChunkBounds c &&
  decide (c.chunkDigest256 = computeChunkDigest256 c.docId c.byteOffset c.rawBytes)

/-- Complete `CborVal` representation of a `DocChunkEntry` (framing all 4 fields). -/
def docChunkToCbor (c : DocChunkEntry) : CborVal :=
  .array [
    .uint (UInt64.ofNat c.docId),
    .uint (UInt64.ofNat c.byteOffset),
    .bytes c.rawBytes,
    .bytes ⟨(bytes32OfDigest256 c.chunkDigest256).toArray⟩
  ]

/-- Content-addressed semantic databank anchored to an `Obend.Vault.ChunkedWorld` checkpoint digest. -/
structure SemanticDatabank where
  worldLogRoot256 : DatabankRoot256
  chunks          : Array DocChunkEntry
  deriving DecidableEq

/-- Compute the 256-bit anchor from a `ChunkedWorld.World` and serialized manifest bytes via `logHashArray`. -/
def worldAnchorDigest256 (w : Obend.Vault.ChunkedWorld.World) (manifest : ByteArray) : DatabankRoot256 :=
  let logDigest := Obend.Vault.ChunkedWorld.logHashArray manifest
  hashOfHashBytes256 deployed (worldLinkDomainTag ++ be 8 w.minted ++ be 8 logDigest.length ++ logDigest)

/-- A zero-based version and half-open byte range in a committed vault page. -/
structure PageChunkRange where
  pageId : Obend.Doc.PageId
  version : Nat
  start : Nat
  length : Nat
  deriving DecidableEq

private def openPageRange (lookup : Obend.Doc.PageId → Option Obend.Vault.Page)
    (r : PageChunkRange) : Option DocChunkEntry := do
  let p ← lookup r.pageId
  let graph ← p.history[r.version]?
  let bytes := (Obend.Vault.render graph p.name p.who).toUTF8
  guard (r.start + r.length ≤ bytes.size)
  let chunk := mkDocChunk r.pageId r.start (bytes.extract r.start (r.start + r.length))
  guard (WfDocChunkBounds chunk)
  return chunk

/-- Open every requested range against the same checkpoint. A missing version or truncated range
rejects the entire batch. The manifest and chunk payloads are derived from the supplied world. -/
def databankFromWorld (w : Obend.Vault.ChunkedWorld.World) (ranges : Array PageChunkRange) :
    Option SemanticDatabank :=
  let pages := Obend.Vault.Index.ofList Obend.Vault.Page.id w.store.pages
  let opened := ranges.map (openPageRange (Obend.Vault.Index.first pages))
  if opened.all Option.isSome && decide (ranges.size < 2^64) then
    some ⟨worldAnchorDigest256 w (Obend.Vault.ChunkedWorld.encodeWorldIncremental w none).1,
      opened.filterMap id⟩
  else none

theorem databankFromWorld_openings {w : Obend.Vault.ChunkedWorld.World}
    {ranges : Array PageChunkRange} {db : SemanticDatabank}
    (h : databankFromWorld w ranges = some db) :
    db.worldLogRoot256 =
        worldAnchorDigest256 w (Obend.Vault.ChunkedWorld.encodeWorldIncremental w none).1 ∧
    ∀ c ∈ db.chunks, ∃ r ∈ ranges, ∃ p g,
      w.store.pages.find? (fun p => p.id == r.pageId) = some p ∧
      p.history[r.version]? = some g ∧
      let bytes := (Obend.Vault.render g p.name p.who).toUTF8
      r.start + r.length ≤ bytes.size ∧
      c = mkDocChunk r.pageId r.start (bytes.extract r.start (r.start + r.length)) := by
  unfold databankFromWorld at h
  dsimp only at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst db
  refine ⟨rfl, fun c hc => ?_⟩
  obtain ⟨oc, hmem, heq⟩ := Array.mem_filterMap.mp hc
  obtain ⟨r, hr, ho⟩ := Array.mem_map.mp hmem
  change oc = some c at heq
  rw [heq] at ho
  unfold openPageRange at ho
  simp only [Obend.Vault.Index.first_ofList, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at ho
  obtain ⟨p, hp, g, hg, _, hb, _, _, hchunk⟩ := ho
  exact ⟨r, hr, p, g, hp, hg, by simpa [guard] using hb, (Option.some.inj hchunk).symm⟩

/-- `worldAnchorDigest256` refines `ChunkedWorld.logHash` via `ChunkedWorld.logHashArray_eq`. -/
theorem worldAnchorDigest256_eq_logHash (w : Obend.Vault.ChunkedWorld.World) (manifest : ByteArray) :
    worldAnchorDigest256 w manifest =
      hashOfHashBytes256 deployed
        (worldLinkDomainTag ++ be 8 w.minted ++
          be 8 (Obend.Vault.ChunkedWorld.logHash manifest.data.toList).length ++
          Obend.Vault.ChunkedWorld.logHash manifest.data.toList) := by
  simp only [worldAnchorDigest256, Obend.Vault.ChunkedWorld.logHashArray_eq]

/-- 64-bit CBOR width guard across an entire `SemanticDatabank`. -/
def WfDatabankBounds (db : SemanticDatabank) : Bool :=
  decide (db.chunks.size < 18446744073709551616) && db.chunks.all WfDocChunkBounds

/-- Full databank well-formedness: width bounds and per-chunk digest integrity. -/
def WfDatabank (db : SemanticDatabank) : Bool :=
  decide (db.chunks.size < 18446744073709551616) && db.chunks.all WfDocChunk

/-- Deterministic CBOR representation of a `SemanticDatabank` (framing `worldLogRoot256` and all chunks). -/
def databankToCbor (db : SemanticDatabank) : CborVal :=
  .array [
    .bytes ⟨(bytes32OfDigest256 db.worldLogRoot256).toArray⟩,
    .array (db.chunks.toList.map docChunkToCbor)
  ]

/-- Domain-separated preimage for `databankCommit256With`. -/
def databankPreimage (db : SemanticDatabank) : List UInt8 :=
  databankDomainTag ++ (encodeDetCbor (databankToCbor db)).data.toList

/-- Generic hash-parameterized 256-bit databank commitment. -/
def databankCommit256With (H : Hash) (db : SemanticDatabank) : DatabankRoot256 :=
  hashOfHashBytes256 H (databankPreimage db)

/-- Deployed cSHAKE256 256-bit databank root commitment. -/
def databankCommit256 (db : SemanticDatabank) : DatabankRoot256 :=
  databankCommit256With deployed db

/-! ### §1.1 `DetCbor` Canonicality, Round-Trip & Preimage Injectivity Proofs -/

private theorem uint64_ofNat_inj {a b : Nat}
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (h : UInt64.ofNat a = UInt64.ofNat b) : a = b := by
  have hnat := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat'] at hnat
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h64] at hnat
  omega

theorem wfDocChunk_mkDocChunk {docId byteOffset : Nat} {rawBytes : ByteArray}
    (hd : docId < 18446744073709551616) (ho : byteOffset < 18446744073709551616)
    (hr : rawBytes.size < 18446744073709551616) :
    WfDocChunk (mkDocChunk docId byteOffset rawBytes) = true := by
  simp [WfDocChunk, WfDocChunkBounds, mkDocChunk, hd, ho, hr]

theorem docChunkToCbor_canonical {c : DocChunkEntry} (hWf : WfDocChunkBounds c = true) :
    CanonicalCbor (docChunkToCbor c) = true := by
  simp only [WfDocChunkBounds, Bool.and_eq_true, decide_eq_true_eq] at hWf
  have h32 : (⟨(bytes32OfDigest256 c.chunkDigest256).toArray⟩ : ByteArray).size < 18446744073709551616 := by
    simp [ByteArray.size]
  simp only [CanonicalCbor, docChunkToCbor, wfVal, wfList, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by simp, trivial, trivial, hWf.2, h32, trivial⟩

theorem docChunkToCbor_injective {c₁ c₂ : DocChunkEntry}
    (h₁ : WfDocChunkBounds c₁ = true) (h₂ : WfDocChunkBounds c₂ = true)
    (hEq : docChunkToCbor c₁ = docChunkToCbor c₂) : c₁ = c₂ := by
  simp only [WfDocChunkBounds, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  simp only [docChunkToCbor, CborVal.array.injEq, List.cons.injEq, CborVal.uint.injEq,
    CborVal.bytes.injEq, and_true] at hEq
  obtain ⟨hd, ho, hr, hdig⟩ := hEq
  have hId : c₁.docId = c₂.docId := uint64_ofNat_inj h₁.1.1 h₂.1.1 hd
  have hOff : c₁.byteOffset = c₂.byteOffset := uint64_ofNat_inj h₁.1.2 h₂.1.2 ho
  have hBytes32 : bytes32OfDigest256 c₁.chunkDigest256 = bytes32OfDigest256 c₂.chunkDigest256 := by
    have hl := congrArg (fun b : ByteArray => b.data.toList) hdig
    simpa using hl
  have hDigest := bytes32OfDigest256_injective hBytes32
  cases c₁; cases c₂
  simp only at hId hOff hr hDigest
  subst hId; subst hOff; subst hr; subst hDigest; rfl

private theorem wfList_docChunkToCbor : ∀ (cs : List DocChunkEntry),
    (∀ c ∈ cs, WfDocChunkBounds c = true) → wfList isValidUtf8 true (cs.map docChunkToCbor) = true
  | [], _ => rfl
  | c :: rest, h => by
    simp only [List.map_cons, wfList, Bool.and_eq_true]
    exact ⟨docChunkToCbor_canonical (h c List.mem_cons_self),
      wfList_docChunkToCbor rest (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem databankToCbor_canonical {db : SemanticDatabank} (hWf : WfDatabankBounds db = true) :
    CanonicalCbor (databankToCbor db) = true := by
  simp only [WfDatabankBounds, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at hWf
  have h32 : (⟨(bytes32OfDigest256 db.worldLogRoot256).toArray⟩ : ByteArray).size < 18446744073709551616 := by
    simp [ByteArray.size]
  have hLen : (db.chunks.toList.map docChunkToCbor).length < 18446744073709551616 := by
    rw [List.length_map, Array.length_toList]; exact hWf.1
  have hChunks : ∀ c ∈ db.chunks.toList, WfDocChunkBounds c = true :=
    fun c hc => hWf.2 c (Array.mem_toList_iff.mp hc)
  simp only [CanonicalCbor, databankToCbor, wfVal, wfList, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by simp, h32, ⟨hLen, wfList_docChunkToCbor db.chunks.toList hChunks⟩, trivial⟩

/-- Deterministic CBOR round-trip on every width-valid `SemanticDatabank`. -/
theorem decodeDetCbor_databankToCbor {db : SemanticDatabank} (hWf : WfDatabankBounds db = true) :
    decodeDetCbor (encodeDetCbor (databankToCbor db)) = some (databankToCbor db) :=
  decodeDetCbor_encodeDetCbor (databankToCbor db) (databankToCbor_canonical hWf)

private theorem map_docChunkToCbor_injective : ∀ (xs ys : List DocChunkEntry),
    (∀ x ∈ xs, WfDocChunkBounds x = true) →
    (∀ y ∈ ys, WfDocChunkBounds y = true) →
    xs.map docChunkToCbor = ys.map docChunkToCbor → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [docChunkToCbor_injective (hx x List.mem_cons_self) (hy y List.mem_cons_self) h.1,
        map_docChunkToCbor_injective xs ys
          (fun a ha => hx a (List.mem_cons_of_mem _ ha))
          (fun b hb => hy b (List.mem_cons_of_mem _ hb)) h.2]

theorem databankToCbor_injective {db₁ db₂ : SemanticDatabank}
    (h₁ : WfDatabankBounds db₁ = true) (h₂ : WfDatabankBounds db₂ = true)
    (hEq : databankToCbor db₁ = databankToCbor db₂) : db₁ = db₂ := by
  simp only [WfDatabankBounds, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at h₁ h₂
  simp only [databankToCbor, CborVal.array.injEq, List.cons.injEq, CborVal.bytes.injEq, and_true] at hEq
  obtain ⟨hw, hc⟩ := hEq
  have hWorldBytes : bytes32OfDigest256 db₁.worldLogRoot256 = bytes32OfDigest256 db₂.worldLogRoot256 := by
    have hl := congrArg (fun b : ByteArray => b.data.toList) hw
    simpa using hl
  have hWorld := bytes32OfDigest256_injective hWorldBytes
  have hList := map_docChunkToCbor_injective db₁.chunks.toList db₂.chunks.toList
    (fun x hx => h₁.2 x (Array.mem_toList_iff.mp hx))
    (fun y hy => h₂.2 y (Array.mem_toList_iff.mp hy)) hc
  have hArr : db₁.chunks = db₂.chunks := Array.toList_inj.mp hList
  cases db₁; cases db₂
  simp only at hWorld hArr
  subst hWorld; subst hArr; rfl

theorem databankPreimage_injective {db₁ db₂ : SemanticDatabank}
    (h₁ : WfDatabankBounds db₁ = true) (h₂ : WfDatabankBounds db₂ = true)
    (hPre : databankPreimage db₁ = databankPreimage db₂) : db₁ = db₂ := by
  have hEncList : (encodeDetCbor (databankToCbor db₁)).data.toList =
      (encodeDetCbor (databankToCbor db₂)).data.toList := by
    simpa only [databankPreimage, List.append_cancel_left_eq] using hPre
  have hEnc : encodeDetCbor (databankToCbor db₁) = encodeDetCbor (databankToCbor db₂) :=
    byteArray_eq_of_toList hEncList
  have hCbor : databankToCbor db₁ = databankToCbor db₂ :=
    encodeDetCbor_injective_canonical _ _
      (databankToCbor_canonical h₁) (databankToCbor_canonical h₂) hEnc
  exact databankToCbor_injective h₁ h₂ hCbor

private theorem hashOfHashBytes256_eq_ofBE_32 {H : Hash} {m₁ m₂ : List UInt8}
    (hlen₁ : (H m₁).length = 32) (hlen₂ : (H m₂).length = 32)
    (h : hashOfHashBytes256 H m₁ = hashOfHashBytes256 H m₂) : ofBE (H m₁) = ofBE (H m₂) := by
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have ha : ofBE (H m₁) < 2 ^ 256 := by have := ofBE_lt (H m₁); rwa [hlen₁, hpow] at this
  have hb : ofBE (H m₂) < 2 ^ 256 := by have := ofBE_lt (H m₂); rwa [hlen₂, hpow] at this
  have hh := congrArg BitVec.toNat h
  simpa only [hashOfHashBytes256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh

/-- **Generic Hash Databank Binding (`databankCommit256With_binding`)**:
    Equal 256-bit databank roots imply identical databanks (`worldLogRoot256` and every `DocChunkEntry`),
    or an explicit `CollisionAmong H` on their two `DetCbor` preimages (`0 Classical`). -/
theorem databankCommit256With_binding (H : Hash) {db₁ db₂ : SemanticDatabank}
    (h₁ : WfDatabankBounds db₁ = true) (h₂ : WfDatabankBounds db₂ = true)
    (hlen : (H (databankPreimage db₁)).length = 32 ∧ (H (databankPreimage db₂)).length = 32)
    (hEq : databankCommit256With H db₁ = databankCommit256With H db₂) :
    db₁ = db₂ ∨ CollisionAmong H (fun m => m = databankPreimage db₁ ∨ m = databankPreimage db₂) := by
  if hp : databankPreimage db₁ = databankPreimage db₂ then
    exact .inl (databankPreimage_injective h₁ h₂ hp)
  else
    exact .inr ⟨databankPreimage db₁, databankPreimage db₂, .inl rfl, .inr rfl, hp,
      hashOfHashBytes256_eq_ofBE_32 hlen.1 hlen.2 hEq⟩

/-- **Deployed cSHAKE256 Databank Binding (`databankCommit256_binding`)**:
    Equal `databankCommit256` commitments imply `db₁ = db₂` or an explicit 2-preimage
    `CollisionAmong deployed` on `(databankPreimage db₁, databankPreimage db₂)`. -/
theorem databankCommit256_binding {db₁ db₂ : SemanticDatabank}
    (h₁ : WfDatabankBounds db₁ = true) (h₂ : WfDatabankBounds db₂ = true)
    (hEq : databankCommit256 db₁ = databankCommit256 db₂) :
    db₁ = db₂ ∨
      CollisionAmong deployed (fun m => m = databankPreimage db₁ ∨ m = databankPreimage db₂) :=
  databankCommit256With_binding deployed h₁ h₂ (by simp [deployed]) hEq

/-- **Constructive `Type`-Valued Collision Extractor (`0 Classical.choice`)**:
    Decides either `db₁ = db₂` or exhibits an `ExactCollisionPair` of `deployed`. -/
def databankCommit256_extract {db₁ db₂ : SemanticDatabank}
    (h₁ : WfDatabankBounds db₁ = true) (h₂ : WfDatabankBounds db₂ = true)
    (hEq : databankCommit256 db₁ = databankCommit256 db₂) :
    PSum (db₁ = db₂) (ExactCollisionPair deployed (databankPreimage db₁) (databankPreimage db₂)) :=
  if hp : databankPreimage db₁ = databankPreimage db₂ then
    .inl (databankPreimage_injective h₁ h₂ hp)
  else
    .inr ⟨hp, hashOfHashBytes256_eq_ofBE_32 (by simp [deployed]) (by simp [deployed]) hEq⟩

/-! ### §1.2 Authenticated Chunk Merkle Inclusion (`VpaJson.SpanRoot` / `SpanProof`) -/

/-- Merkle leaf encoding of a `DocChunkEntry` via deterministic CBOR. -/
def encodeDocChunkBytes (c : DocChunkEntry) : ByteArray :=
  encodeDetCbor (docChunkToCbor c)

/-- Merkle span-tree root over a databank's `DocChunkEntry` leaves. -/
def databankChunkMerkleRoot (db : SemanticDatabank) : VpaJson.SpanRoot :=
  VpaJson.spanMerkleRoot cshakeHasher databankChunkSpanTag (db.chunks.toList.map encodeDocChunkBytes)

/-- Construct the Merkle inclusion proof for chunk index `idx` in `db`. -/
def databankChunkMerkleProof (db : SemanticDatabank) (idx : Nat) : VpaJson.SpanProof :=
  VpaJson.spanMerkleProof cshakeHasher databankChunkSpanTag (db.chunks.toList.map encodeDocChunkBytes) idx

/-- Verify a `DocChunkEntry` Merkle inclusion proof against `root`. -/
def verifyDatabankChunkInclusion (root : VpaJson.SpanRoot) (c : DocChunkEntry) (prf : VpaJson.SpanProof) : Bool :=
  WfDocChunk c &&
  VpaJson.verifySpanMerkleInclusion cshakeHasher databankChunkSpanTag root (encodeDocChunkBytes c) prf

/-- **Chunk Inclusion Completeness**: every well-formed chunk in `db` verifies at its index. -/
theorem verifyDatabankChunkInclusion_complete (db : SemanticDatabank) (idx : Nat)
    (hIdx : idx < db.chunks.size) (hWf : WfDocChunk db.chunks[idx] = true) :
    verifyDatabankChunkInclusion (databankChunkMerkleRoot db) db.chunks[idx]
      (databankChunkMerkleProof db idx) = true := by
  unfold verifyDatabankChunkInclusion databankChunkMerkleRoot databankChunkMerkleProof
  rw [hWf, Bool.true_and]
  have hLen : idx < (db.chunks.toList.map encodeDocChunkBytes).length := by
    rw [List.length_map, Array.length_toList]; exact hIdx
  have hGet : (db.chunks.toList.map encodeDocChunkBytes)[idx]'hLen = encodeDocChunkBytes db.chunks[idx] := by
    simp [List.getElem_map, Array.getElem_toList]
  rw [← hGet]
  exact VpaJson.verifySpanMerkleInclusion_complete cshakeHasher databankChunkSpanTag _ idx hLen

/-- **Chunk Inclusion Top-Binding**: an accepted chunk inclusion proof against `databankChunkMerkleRoot db`
    returns the exact `DocChunkEntry` at `db.chunks[prf.index]?`, or exhibits a `cshakeHasher` collision. -/
theorem verifyDatabankChunkInclusion_binding {db : SemanticDatabank}
    {c : DocChunkEntry} {prf : VpaJson.SpanProof}
    (hWfDb : WfDatabankBounds db = true)
    (hVer : verifyDatabankChunkInclusion (databankChunkMerkleRoot db) c prf = true) :
    db.chunks[prf.index]? = some c ∨
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
        cshakeHasher.hash databankChunkSpanTag m₁ = cshakeHasher.hash databankChunkSpanTag m₂ := by
  simp only [verifyDatabankChunkInclusion, Bool.and_eq_true] at hVer
  have hWfC : WfDocChunkBounds c = true := by
    simp only [WfDocChunk, Bool.and_eq_true] at hVer; exact hVer.1.1
  rcases VpaJson.verifySpanMerkleInclusion_top_binding cshakeHasher databankChunkSpanTag rfl hVer.2 with
    hLeaf | hCol
  · rw [List.getElem?_map] at hLeaf
    cases hGet : db.chunks.toList[prf.index]? with
    | none => simp [hGet] at hLeaf
    | some cDb =>
      rw [hGet, Option.map_some, Option.some.injEq] at hLeaf
      have hMem : cDb ∈ db.chunks := Array.mem_toList_iff.mp (List.mem_of_getElem? hGet)
      have hWfCDb : WfDocChunkBounds cDb = true := by
        simp only [WfDatabankBounds, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hWfDb
        exact hWfDb.2 cDb hMem
      have hEqCbor := encodeDetCbor_injective_canonical _ _
        (docChunkToCbor_canonical hWfCDb) (docChunkToCbor_canonical hWfC) hLeaf
      have hEqChunk := docChunkToCbor_injective hWfCDb hWfC hEqCbor
      rw [Array.getElem?_toList] at hGet
      exact Or.inl (hGet.trans (congrArg some hEqChunk))
  · exact Or.inr hCol

/-! ## §2. `RedactionSlicePolicy` & Stateful Delimiter Confinement (`redaction_cannot_splice_tokens`) -/

/-- Sorted, strictly separated disclosed byte intervals `[start, stop)` within `[0, docByteLen)`. -/
structure RedactionSlicePolicy where
  docByteLen     : Nat
  disclosedSpans : Array (Nat × Nat)
  deriving DecidableEq, Repr

/-- Identifier/claim payload bytes (`0-9`, `A-Z`, `a-z`, `_`, `-`, `.`, `/`).
    Excludes JSON delimiters (`"`, `\`, `,`, `:`, `{`, `}`, `[`, `]`, whitespace) AND the redaction
    placeholder `'*'` (`0x2a`), so redaction masks never participate in or bridge claim tokens. -/
def isTokenPayloadByte (b : UInt8) : Bool :=
  (decide (0x30 ≤ b.toNat) && decide (b.toNat ≤ 0x39)) ||
  (decide (0x41 ≤ b.toNat) && decide (b.toNat ≤ 0x5a)) ||
  (decide (0x61 ≤ b.toNat) && decide (b.toNat ≤ 0x7a)) ||
  b == 0x5f || b == 0x2d || b == 0x2e || b == 0x2f

theorem isTokenPayloadByte_placeholder_false (u : Unit) :
    let _ := u
    isTokenPayloadByte 0x2a = false := by decide

/-- Half-open interval membership `sp.1 ≤ pos < sp.2`. -/
def inByteSpan (pos : Nat) (sp : Nat × Nat) : Bool :=
  decide (sp.1 ≤ pos) && decide (pos < sp.2)

/-- Specification-tier disclosed-byte predicate over a list of intervals. -/
def isDisclosedAtSpec (spans : List (Nat × Nat)) (pos : Nat) : Bool :=
  spans.any (inByteSpan pos)

/-- Whether byte offset `pos` is disclosed under `pol`. -/
def isDisclosedAt (pol : RedactionSlicePolicy) (pos : Nat) : Bool :=
  isDisclosedAtSpec pol.disclosedSpans.toList pos

/-- Enforces `minStart ≤ s < e ≤ docLen` and strict separation `e + 1 ≤ s'` (`e < s'`) between
    consecutive disclosed spans so every pair of disclosed intervals has a non-empty elided gap. -/
def checkSortedDisjointSpansFrom (minStart docLen : Nat) : List (Nat × Nat) → Bool
  | [] => decide (minStart ≤ docLen + 1)
  | (s, e) :: rest =>
    decide (minStart ≤ s) && decide (s < e) && decide (e ≤ docLen) &&
      checkSortedDisjointSpansFrom (e + 1) docLen rest

/-- Complement elided intervals `[l, r)` covering `[cursor, docLen) \ ⋃ spans`. -/
def elidedGapsFrom (cursor docLen : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if cursor < docLen then [(cursor, docLen)] else []
  | (s, e) :: rest =>
    if cursor < s then (cursor, s) :: elidedGapsFrom e docLen rest
    else elidedGapsFrom e docLen rest

/-- All elided byte gaps `[l, r)` induced by `pol`. -/
def elidedGaps (pol : RedactionSlicePolicy) : List (Nat × Nat) :=
  elidedGapsFrom 0 pol.docByteLen pol.disclosedSpans.toList

/-- Safe ASCII placeholder mask (`'*' = 0x2a` repeated `n` times). -/
def placeholderBytes (n : Nat) : ByteArray :=
  ⟨(List.replicate n 0x2a).toArray⟩

/-- Apply placeholder masks sequentially across elided gaps `[l, r)`. -/
def applyGapsMask (doc : ByteArray) : List (Nat × Nat) → ByteArray
  | [] => doc
  | (l, r) :: rest =>
    applyGapsMask (spliceByteArray doc l r (placeholderBytes (r - l))) rest

/-- Materialize the redacted document view by masking every elided gap with `'*'` (`0x2a`). -/
def applyRedactionPolicy (doc : ByteArray) (pol : RedactionSlicePolicy) : ByteArray :=
  applyGapsMask doc (elidedGaps pol)

/-- Delimiter-boundary guard: neither endpoint `l - 1` nor `r` of an elided gap `[l, r)` may split
    an adjacent disclosed token payload (`isTokenPayloadByte = false` on disclosed neighbors). -/
def gapDelimiterBounded (doc : ByteArray) (l r : Nat) : Bool :=
  (decide (l = 0) || !isTokenPayloadByte (byteAt doc (l - 1))) &&
  (decide (r = doc.size) || !isTokenPayloadByte (byteAt doc r))

/-- **Stateful JSON + Token-Delimiter Redaction Confinement Checker**:
    1. `doc.size = pol.docByteLen` and `pol.disclosedSpans` are strictly sorted & gap-separated (`e < s'`),
    2. Every elided gap `(l, r) ∈ elidedGaps pol` satisfies stateful RFC 8259 JSON value-string
       confinement (`VpaJson.checkJsonRedaction doc l r (placeholderBytes (r - l))`) AND
       delimiter-boundary isolation (`gapDelimiterBounded doc l r`). -/
def checkRedactionDelimiterConfined (doc : ByteArray) (pol : RedactionSlicePolicy) : Bool :=
  decide (doc.size = pol.docByteLen) &&
  checkSortedDisjointSpansFrom 0 pol.docByteLen pol.disclosedSpans.toList &&
  (elidedGaps pol).all fun (l, r) =>
    VpaJson.checkJsonRedaction doc l r (placeholderBytes (r - l)) &&
    gapDelimiterBounded doc l r

/-- A maximal contiguous token span `[start, stop)` extracted from a byte buffer. -/
structure TokenSpan where
  start : Nat
  stop  : Nat
  bytes : ByteArray
  deriving DecidableEq, Repr

/-- Declarative specification of a maximal contiguous `isTokenPayloadByte` span `[start, stop)` in `buf`. -/
def IsMaximalTokenSpan (buf : ByteArray) (tok : TokenSpan) : Bool :=
  decide (tok.start < tok.stop) &&
  decide (tok.stop ≤ buf.size) &&
  decide (tok.bytes.data.toList = (buf.extract tok.start tok.stop).data.toList) &&
  (List.range (tok.stop - tok.start)).all (fun k => isTokenPayloadByte (byteAt buf (tok.start + k))) &&
  (decide (tok.start = 0) || !isTokenPayloadByte (byteAt buf (tok.start - 1))) &&
  (decide (tok.stop = buf.size) || !isTokenPayloadByte (byteAt buf tok.stop))

/-- Single-pass $O(N)$ scanner collecting maximal `TokenSpan`s from `buf`. -/
def scanTokensGo (buf : ByteArray) (idx : Nat) (curStart : Option Nat) (acc : Array TokenSpan) :
    Array TokenSpan :=
  if h : idx < buf.size then
    let b := buf[idx]'h
    if isTokenPayloadByte b then
      match curStart with
      | some s => scanTokensGo buf (idx + 1) (some s) acc
      | none => scanTokensGo buf (idx + 1) (some idx) acc
    else
      match curStart with
      | some s => scanTokensGo buf (idx + 1) none (acc.push ⟨s, idx, buf.extract s idx⟩)
      | none => scanTokensGo buf (idx + 1) none acc
  else
    match curStart with
    | some s => acc.push ⟨s, buf.size, buf.extract s buf.size⟩
    | none => acc
termination_by buf.size - idx

/-- Extract all maximal payload tokens from `buf` in $O(|buf|)$ time. -/
def extractTokenSpans (buf : ByteArray) : Array TokenSpan :=
  scanTokensGo buf 0 none #[]

/-! ### §2.1 Disclosed Interval Separation & Complement Gap Equivalence Lemmas -/

private theorem checkSortedDisjointSpansFrom_mono {m₁ m₂ docLen : Nat} (hle : m₁ ≤ m₂) :
    ∀ spans : List (Nat × Nat),
      checkSortedDisjointSpansFrom m₂ docLen spans = true →
      checkSortedDisjointSpansFrom m₁ docLen spans = true
  | [], h => by
    simp only [checkSortedDisjointSpansFrom, decide_eq_true_eq] at h ⊢; omega
  | (s, e) :: rest, h => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨by omega, h.1.1.2⟩, h.1.2⟩, h.2⟩

private theorem not_disclosed_below : ∀ (spans : List (Nat × Nat)) (minStart docLen pos : Nat),
    checkSortedDisjointSpansFrom minStart docLen spans = true →
    pos < minStart →
    isDisclosedAtSpec spans pos = false
  | [], _, _, _, _, _ => rfl
  | (s, e) :: rest, minStart, docLen, pos, hWf, hLt => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at hWf
    have hIn : inByteSpan pos (s, e) = false := by
      simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    simp only [isDisclosedAtSpec, List.any_cons, hIn, Bool.false_or]
    exact not_disclosed_below rest (e + 1) docLen pos hWf.2 (by omega)

/-- **Interval Non-Bridging Lemma**: if `spans` pass `checkSortedDisjointSpansFrom` and every byte
    in `[ts, te)` (`ts < te`) is disclosed, then `[ts, te)` lies inside a *single* interval `sp ∈ spans`. -/
theorem disclosedRange_sub_single_span : ∀ (spans : List (Nat × Nat)) (minStart docLen ts te : Nat),
    checkSortedDisjointSpansFrom minStart docLen spans = true →
    ts < te →
    (∀ i, ts ≤ i → i < te → isDisclosedAtSpec spans i = true) →
    ∃ sp ∈ spans, sp.1 ≤ ts ∧ te ≤ sp.2
  | [], _, _, ts, te, _, hLt, hAll => by
    have h0 := hAll ts (Nat.le_refl ts) hLt
    simp [isDisclosedAtSpec] at h0
  | (s, e) :: rest, minStart, docLen, ts, te, hWf, hLt, hAll => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at hWf
    have hTs := hAll ts (Nat.le_refl ts) hLt
    unfold isDisclosedAtSpec at hTs
    rw [List.any_cons] at hTs
    cases hInTs : inByteSpan ts (s, e) with
    | true =>
      simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq] at hInTs
      by_cases hTe : te ≤ e
      · exact ⟨(s, e), List.mem_cons_self, hInTs.1, hTe⟩
      · exfalso
        have hAtE := hAll e (by omega) (by omega)
        have hNotHead : inByteSpan e (s, e) = false := by simp [inByteSpan]
        have hNotRest := not_disclosed_below rest (e + 1) docLen e hWf.2 (by omega)
        unfold isDisclosedAtSpec at hAtE hNotRest
        rw [List.any_cons, hNotHead, hNotRest] at hAtE
        cases hAtE
    | false =>
      rw [hInTs, Bool.false_or] at hTs
      change isDisclosedAtSpec rest ts = true at hTs
      have hGe : e + 1 ≤ ts := by
        by_cases hge : e + 1 ≤ ts
        · exact hge
        · rw [not_disclosed_below rest (e + 1) docLen ts hWf.2 (by omega)] at hTs; cases hTs
      have hRestAll : ∀ i, ts ≤ i → i < te → isDisclosedAtSpec rest i = true := by
        intro i hlo hhi
        have hi := hAll i hlo hhi
        have hNotSE : inByteSpan i (s, e) = false := by
          simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
        unfold isDisclosedAtSpec at hi ⊢
        simpa [hNotSE] using hi
      obtain ⟨sp, hMem, h1, h2⟩ := disclosedRange_sub_single_span rest (e + 1) docLen ts te hWf.2 hLt hRestAll
      exact ⟨sp, List.mem_cons_of_mem _ hMem, h1, h2⟩

/-- Ordered disjointness predicate for elided gaps `[(l₁, r₁), (l₂, r₂), ...]`. -/
def GapsOrderedFrom (cursor docLen : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (l, r) :: rest => cursor ≤ l ∧ l < r ∧ r ≤ docLen ∧ GapsOrderedFrom r docLen rest

private theorem gapsOrdered_lower_bound : ∀ (gs : List (Nat × Nat)) (c docLen : Nat),
    GapsOrderedFrom c docLen gs → ∀ x ∈ gs, c ≤ x.1
  | [], _, _, _, _, hx => nomatch hx
  | (a, b) :: tl, c, docLen, ho, x, hx => by
    obtain ⟨hca, hab, _, htlOrd⟩ := ho
    rcases List.mem_cons.mp hx with rfl | htl
    · exact hca
    · exact Nat.le_trans (by omega : c ≤ b) (gapsOrdered_lower_bound tl b docLen htlOrd x htl)

private theorem elidedGapsFrom_ordered : ∀ (spans : List (Nat × Nat)) (cursor docLen : Nat),
    cursor ≤ docLen →
    checkSortedDisjointSpansFrom cursor docLen spans = true →
    GapsOrderedFrom cursor docLen (elidedGapsFrom cursor docLen spans)
  | [], cursor, docLen, _, _ => by
    unfold elidedGapsFrom
    split
    · rename_i hlt; exact ⟨Nat.le_refl _, hlt, Nat.le_refl _, trivial⟩
    · trivial
  | (s, e) :: rest, cursor, docLen, _, hWf => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at hWf
    have hRestWf := checkSortedDisjointSpansFrom_mono (Nat.le_succ e) rest hWf.2
    have ih := elidedGapsFrom_ordered rest e docLen hWf.1.2 hRestWf
    unfold elidedGapsFrom
    split
    · rename_i hcs
      refine ⟨Nat.le_refl _, hcs, by omega, ?_⟩
      cases hg : elidedGapsFrom e docLen rest with
      | nil => trivial
      | cons g gs =>
        rw [hg] at ih
        obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
        exact ⟨by omega, ih2, ih3, ih4⟩
    · cases hg : elidedGapsFrom e docLen rest with
      | nil => trivial
      | cons g gs =>
        rw [hg] at ih
        obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
        exact ⟨by omega, ih2, ih3, ih4⟩

private theorem not_inAnyGap_below : ∀ (gaps : List (Nat × Nat)) (cursor docLen pos : Nat),
    GapsOrderedFrom cursor docLen gaps →
    pos < cursor →
    gaps.any (inByteSpan pos) = false
  | [], _, _, _, _, _ => rfl
  | (l, r) :: rest, cursor, docLen, pos, hOrd, hLt => by
    obtain ⟨hcl, hlr, _, hRest⟩ := hOrd
    have hIn : inByteSpan pos (l, r) = false := by
      simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    simp only [List.any_cons, hIn, Bool.false_or]
    exact not_inAnyGap_below rest r docLen pos hRest (by omega)

private theorem isDisclosedAtSpec_eq_not_gap : ∀ (spans : List (Nat × Nat)) (cursor docLen pos : Nat),
    cursor ≤ pos → pos < docLen →
    checkSortedDisjointSpansFrom cursor docLen spans = true →
    isDisclosedAtSpec spans pos = !(elidedGapsFrom cursor docLen spans).any (inByteSpan pos)
  | [], cursor, docLen, pos, hlo, hhi, _ => by
    have hlt : cursor < docLen := by omega
    simp [isDisclosedAtSpec, elidedGapsFrom, hlt, inByteSpan, hlo, hhi]
  | (s, e) :: rest, cursor, docLen, pos, hlo, hhi, hWf => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at hWf
    have hRestWf := checkSortedDisjointSpansFrom_mono (Nat.le_succ e) rest hWf.2
    have hRestOrd := elidedGapsFrom_ordered rest e docLen hWf.1.2 hRestWf
    by_cases hps : pos < s
    · have hcs : cursor < s := by omega
      have hInSE : inByteSpan pos (s, e) = false := by
        simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
      have hRestDis := not_disclosed_below rest (e + 1) docLen pos hWf.2 (by omega)
      have hInGap : inByteSpan pos (cursor, s) = true := by simp [inByteSpan, hlo, hps]
      unfold isDisclosedAtSpec elidedGapsFrom
      simp only [List.any_cons, hInSE, Bool.false_or, hcs, ↓reduceIte, hInGap, Bool.true_or, Bool.not_true]
      exact hRestDis
    · by_cases hpe : pos < e
      · have hInSE : inByteSpan pos (s, e) = true := by
          simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq]; omega
        have hRestGap := not_inAnyGap_below _ e docLen pos hRestOrd hpe
        unfold isDisclosedAtSpec elidedGapsFrom
        simp only [List.any_cons, hInSE, Bool.true_or]
        split
        · have hInCS : inByteSpan pos (cursor, s) = false := by
            simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
          simp [hInCS, hRestGap]
        · simp [hRestGap]
      · have hInSE : inByteSpan pos (s, e) = false := by
          simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
        have ih := isDisclosedAtSpec_eq_not_gap rest e docLen pos (by omega) hhi hRestWf
        unfold isDisclosedAtSpec elidedGapsFrom
        simp only [List.any_cons, hInSE, Bool.false_or]
        change isDisclosedAtSpec rest pos = _
        split
        · have hInCS : inByteSpan pos (cursor, s) = false := by
            simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
          simpa [hInCS] using ih
        · exact ih

/-- If `pos` (`0 < pos < docLen`) is disclosed and `pos - 1` is NOT disclosed, then some elided gap
    `(l, r) ∈ elidedGaps pol` ends right at `r = pos`. -/
private theorem gap_ends_at_of_undisclosed_pred :
    ∀ (gaps : List (Nat × Nat)) (cursor docLen pos : Nat),
      GapsOrderedFrom cursor docLen gaps →
      0 < pos →
      gaps.any (inByteSpan (pos - 1)) = true →
      gaps.any (inByteSpan pos) = false →
      ∃ l, (l, pos) ∈ gaps
  | [], _, _, _, _, _, hPrev, _ => by simp at hPrev
  | (l, r) :: rest, cursor, docLen, pos, hOrd, hPos, hPrev, hCur => by
    obtain ⟨_, _, _, hRestOrd⟩ := hOrd
    simp only [List.any_cons, Bool.or_eq_true, Bool.or_eq_false_iff] at hPrev hCur
    rcases hPrev with hInHead | hInRest
    · simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq] at hInHead
      have hNotIn : ¬ (l ≤ pos ∧ pos < r) := fun hp => by
        have ht : inByteSpan pos (l, r) = true := by simp [inByteSpan, hp.1, hp.2]
        rw [ht] at hCur; cases hCur.1
      have hr : r = pos := by omega
      subst hr
      exact ⟨l, List.mem_cons_self⟩
    · obtain ⟨l', hm⟩ := gap_ends_at_of_undisclosed_pred rest r docLen pos hRestOrd hPos hInRest hCur.2
      exact ⟨l', List.mem_cons_of_mem _ hm⟩

/-- If `pos - 1` is disclosed (`0 < pos ≤ docLen`) and `pos` (`pos < docLen`) is NOT disclosed,
    then some elided gap `(pos, r) ∈ elidedGaps pol` starts right at `l = pos`. -/
private theorem gap_starts_at_of_undisclosed_curr :
    ∀ (gaps : List (Nat × Nat)) (cursor docLen pos : Nat),
      GapsOrderedFrom cursor docLen gaps →
      0 < pos →
      gaps.any (inByteSpan (pos - 1)) = false →
      gaps.any (inByteSpan pos) = true →
      ∃ r, (pos, r) ∈ gaps
  | [], _, _, _, _, _, _, hCur => by simp at hCur
  | (l, r) :: rest, cursor, docLen, pos, hOrd, hPos, hPrev, hCur => by
    obtain ⟨_, _, _, hRestOrd⟩ := hOrd
    simp only [List.any_cons, Bool.or_eq_true, Bool.or_eq_false_iff] at hPrev hCur
    rcases hCur with hInHead | hInRest
    · simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq] at hInHead
      have hNotPrev : ¬ (l ≤ pos - 1 ∧ pos - 1 < r) := fun hp => by
        have ht : inByteSpan (pos - 1) (l, r) = true := by simp [inByteSpan, hp.1, hp.2]
        rw [ht] at hPrev; cases hPrev.1
      have hl : l = pos := by omega
      subst hl
      exact ⟨r, List.mem_cons_self⟩
    · obtain ⟨r', hm⟩ := gap_starts_at_of_undisclosed_curr rest r docLen pos hRestOrd hPos hPrev.2 hInRest
      exact ⟨r', List.mem_cons_of_mem _ hm⟩

/-! ### §2.2 Multi-Gap `spliceByteArray` Bytewise Characterization & JSON Grammar Preservation -/

private theorem placeholderBytes_toList (n : Nat) :
    (placeholderBytes n).data.toList = List.replicate n 0x2a := rfl

private theorem placeholderBytes_size (n : Nat) : (placeholderBytes n).size = n := by
  simp [placeholderBytes, ByteArray.size]

private theorem placeholderBytes_all_safe (n : Nat) :
    (placeholderBytes n).data.toList.all VpaJson.isSafeMaskByte = true := by
  rw [placeholderBytes_toList]
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.all_cons, ih, Bool.and_true]
    decide

private theorem splice_placeholder_size {doc : ByteArray} {l r : Nat}
    (hlr : l ≤ r) (hr : r ≤ doc.size) :
    (spliceByteArray doc l r (placeholderBytes (r - l))).size = doc.size := by
  rw [← toList_length, spliceByteArray_toList, placeholderBytes_toList]
  simp only [List.length_append, List.length_take, List.length_replicate, List.length_drop, toList_length]
  omega

private theorem byteAt_eq_getElem?_toList (b : ByteArray) (i : Nat) :
    byteAt b i = (b.data.toList[i]?).getD 0 := by
  unfold byteAt
  by_cases h : i < b.size
  · have hl : i < b.data.toList.length := by rw [toList_length]; exact h
    rw [dite_eq_left h, List.getElem?_eq_getElem hl]; rfl
  · have hl : b.data.toList.length ≤ i := by rw [toList_length]; omega
    rw [dite_eq_right h, List.getElem?_eq_none hl]; rfl

private theorem byteAt_splice_placeholder {doc : ByteArray} {l r : Nat}
    (hlr : l ≤ r) (hr : r ≤ doc.size) (i : Nat) :
    byteAt (spliceByteArray doc l r (placeholderBytes (r - l))) i =
      if inByteSpan i (l, r) then 0x2a else byteAt doc i := by
  have hLenDoc : doc.data.toList.length = doc.size := toList_length doc
  rw [byteAt_eq_getElem?_toList, byteAt_eq_getElem?_toList, spliceByteArray_toList, placeholderBytes_toList]
  have hTakeLen : (doc.data.toList.take l).length = l := by simp [hLenDoc]; omega
  have hRepLen : (List.replicate (r - l) (0x2a : UInt8)).length = r - l := List.length_replicate
  by_cases hil : i < l
  · have hIn : inByteSpan i (l, r) = false := by
      simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    simp only [hIn, Bool.false_eq_true, ↓reduceIte]
    rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hil]
  · by_cases hir : i < r
    · have hIn : inByteSpan i (l, r) = true := by
        simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq]; omega
      simp only [hIn, ↓reduceIte]
      rw [List.append_assoc, List.getElem?_append_right (by omega),
          List.getElem?_append_left (by omega)]
      simp [hTakeLen, show i - l < r - l by omega]
    · have hIn : inByteSpan i (l, r) = false := by
        simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
      simp only [hIn, Bool.false_eq_true, ↓reduceIte]
      rw [List.getElem?_append_right (by simp [hTakeLen, hRepLen]; omega)]
      simp only [List.length_append, hTakeLen, hRepLen, List.getElem?_drop]
      rw [show r + (i - (l + (r - l))) = i by omega]

private theorem applyGapsMask_size_and_byteAt :
    ∀ (gaps : List (Nat × Nat)) (cursor : Nat) (doc : ByteArray),
      GapsOrderedFrom cursor doc.size gaps →
      (applyGapsMask doc gaps).size = doc.size ∧
        ∀ i, byteAt (applyGapsMask doc gaps) i =
          if gaps.any (inByteSpan i) then 0x2a else byteAt doc i
  | [], _, doc, _ => ⟨rfl, fun _ => by simp [applyGapsMask]⟩
  | (l, r) :: rest, cursor, doc, hOrd => by
    obtain ⟨_, hlr, hr, hRestOrd⟩ := hOrd
    let doc₁ := spliceByteArray doc l r (placeholderBytes (r - l))
    have hSz₁ : doc₁.size = doc.size := splice_placeholder_size (Nat.le_of_lt hlr) hr
    have hRestOrd' : GapsOrderedFrom r doc₁.size rest := hSz₁.symm ▸ hRestOrd
    obtain ⟨hSzRest, hByteRest⟩ := applyGapsMask_size_and_byteAt rest r doc₁ hRestOrd'
    refine ⟨hSzRest.trans hSz₁, fun i => ?_⟩
    unfold applyGapsMask
    rw [hByteRest i, byteAt_splice_placeholder (Nat.le_of_lt hlr) hr i]
    simp only [List.any_cons]
    by_cases h1 : rest.any (inByteSpan i) = true <;>
      by_cases h2 : inByteSpan i (l, r) = true <;>
      simp [h1, h2]

private theorem drop_splice_placeholder_of_ge {doc : ByteArray} {l r pos : Nat}
    (hlr : l ≤ r) (hr : r ≤ doc.size) (hge : r ≤ pos) :
    (spliceByteArray doc l r (placeholderBytes (r - l))).data.toList.drop pos =
      doc.data.toList.drop pos := by
  have hLenDoc : doc.data.toList.length = doc.size := toList_length doc
  rw [spliceByteArray_toList, placeholderBytes_toList]
  have hPreLen : (doc.data.toList.take l ++ List.replicate (r - l) (0x2a : UInt8)).length = r := by
    simp [hLenDoc]; omega
  rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hPreLen]; exact hge), List.nil_append,
      hPreLen, List.drop_drop, show r + (pos - r) = pos by omega]

private theorem jsonStateAt_splice_placeholder_of_ge {doc : ByteArray} {l r pos : Nat}
    (hRed : VpaJson.checkJsonRedaction doc l r (placeholderBytes (r - l)) = true)
    (hge : r ≤ pos) :
    VpaJson.jsonStateAt (spliceByteArray doc l r (placeholderBytes (r - l))) pos =
      VpaJson.jsonStateAt doc pos := by
  have hBounds : l ≤ r ∧ r ≤ doc.size := by
    simp only [VpaJson.checkJsonRedaction, Bool.and_eq_true, decide_eq_true_eq] at hRed
    exact ⟨hRed.1.1.1.1, hRed.1.1.1.2⟩
  have hLenDoc : doc.data.toList.length = doc.size := toList_length doc
  obtain ⟨_, _, hAfter⟩ := VpaJson.jsonRedaction_preserves_valid_parse_and_keys hRed
  have hSpec := hAfter (pos - r)
  rw [show r + (pos - r) = pos by omega] at hSpec
  rw [← hSpec, VpaJson.jsonStateAt_eq, spliceByteArray_toList]
  congr 1
  have hPreLen : (doc.data.toList.take l ++ (placeholderBytes (r - l)).data.toList).length = r := by
    rw [placeholderBytes_toList]; simp [hLenDoc]; omega
  rw [List.take_append, List.take_of_length_le (by rw [hPreLen]; exact hge), hPreLen]

private theorem jsonStateAt_splice_placeholder_of_le {doc : ByteArray} {l r pos : Nat}
    (hlr : l ≤ r) (hr : r ≤ doc.size) (hle : pos ≤ l) :
    VpaJson.jsonStateAt (spliceByteArray doc l r (placeholderBytes (r - l))) pos =
      VpaJson.jsonStateAt doc pos := by
  have hLenDoc : doc.data.toList.length = doc.size := toList_length doc
  rw [VpaJson.jsonStateAt_eq, VpaJson.jsonStateAt_eq, spliceByteArray_toList]
  congr 1
  have hTakeLen : (doc.data.toList.take l).length = l := by simp [hLenDoc]; omega
  rw [List.append_assoc, List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left hle]

private theorem applyGapsMask_json_invariant :
    ∀ (gaps : List (Nat × Nat)) (cursor : Nat) (doc : ByteArray),
      GapsOrderedFrom cursor doc.size gaps →
      (∀ g ∈ gaps, VpaJson.checkJsonRedaction doc g.1 g.2 (placeholderBytes (g.2 - g.1)) = true) →
      VpaJson.jsonRun (applyGapsMask doc gaps) = VpaJson.jsonRun doc ∧
        ∀ pos, gaps.any (inByteSpan pos) = false →
          VpaJson.jsonStateAt (applyGapsMask doc gaps) pos = VpaJson.jsonStateAt doc pos
  | [], _, doc, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | (l, r) :: rest, cursor, doc, hOrd, hAll => by
    obtain ⟨_, hlr, hr, hRestOrd⟩ := hOrd
    have hHead := hAll (l, r) List.mem_cons_self
    let doc₁ := spliceByteArray doc l r (placeholderBytes (r - l))
    have hSz₁ : doc₁.size = doc.size := splice_placeholder_size (Nat.le_of_lt hlr) hr
    have hRestOrd' : GapsOrderedFrom r doc₁.size rest := hSz₁.symm ▸ hRestOrd
    have hRestRed : ∀ g ∈ rest,
        VpaJson.checkJsonRedaction doc₁ g.1 g.2 (placeholderBytes (g.2 - g.1)) = true := by
      intro g hg
      have hgOrig := hAll g (List.mem_cons_of_mem _ hg)
      have hGeR : r ≤ g.1 := gapsOrdered_lower_bound rest r doc.size hRestOrd g hg
      have hStEq := jsonStateAt_splice_placeholder_of_ge hHead hGeR
      have hDropEq := drop_splice_placeholder_of_ge (Nat.le_of_lt hlr) hr hGeR
      unfold VpaJson.checkJsonRedaction at hgOrig ⊢
      rw [hSz₁, hStEq, hDropEq]
      exact hgOrig
    obtain ⟨hRunRest, hPosRest⟩ := applyGapsMask_json_invariant rest r doc₁ hRestOrd' hRestRed
    refine ⟨hRunRest.trans (VpaJson.jsonRedaction_run hHead), fun pos hNotGap => ?_⟩
    simp only [List.any_cons, Bool.or_eq_false_iff] at hNotGap
    unfold applyGapsMask
    rw [hPosRest pos hNotGap.2]
    by_cases hpl : pos ≤ l
    · exact jsonStateAt_splice_placeholder_of_le (Nat.le_of_lt hlr) hr hpl
    · have hgeR : r ≤ pos := by
        have hIn := hNotGap.1
        simp only [inByteSpan, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hIn
        rcases hIn with h1 | h2 <;> omega
      exact jsonStateAt_splice_placeholder_of_ge hHead hgeR

/-- **Multi-Span JSON Grammar & Key-Set Invariance**:
    If `checkRedactionDelimiterConfined doc pol = true`, then `applyRedactionPolicy doc pol` has the
    exact same RFC 8259 grammar verdict, closed object key sets, and byte length as `doc`. -/
theorem redactionPolicy_preserves_json_grammar_and_keys {doc : ByteArray} {pol : RedactionSlicePolicy}
    (hConf : checkRedactionDelimiterConfined doc pol = true) :
    (applyRedactionPolicy doc pol).size = doc.size ∧
    VpaJson.runFullJsonGrammar (applyRedactionPolicy doc pol) = VpaJson.runFullJsonGrammar doc ∧
    VpaJson.jsonObjectKeys (applyRedactionPolicy doc pol) = VpaJson.jsonObjectKeys doc := by
  simp only [checkRedactionDelimiterConfined, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hConf
  obtain ⟨⟨hSz, hDisj⟩, hGaps⟩ := hConf
  have hOrd : GapsOrderedFrom 0 doc.size (elidedGaps pol) := by
    rw [hSz]; exact elidedGapsFrom_ordered _ 0 pol.docByteLen (Nat.zero_le _) hDisj
  have hSzOut := (applyGapsMask_size_and_byteAt (elidedGaps pol) 0 doc hOrd).1
  have hRun := (applyGapsMask_json_invariant (elidedGaps pol) 0 doc hOrd
    (fun g hg => (hGaps g hg).1)).1
  exact ⟨hSzOut,
    by unfold VpaJson.runFullJsonGrammar applyRedactionPolicy; rw [hRun],
    by unfold VpaJson.jsonObjectKeys applyRedactionPolicy; rw [hRun]⟩

/-- **Bytewise & Stateful JSON Characterization of `applyRedactionPolicy`**:
    Under `checkRedactionDelimiterConfined doc pol = true`, `applyRedactionPolicy doc pol` preserves
    `doc.size`, equals `doc` on disclosed bytes and `0x2a` elsewhere, and agrees with `doc` on
    `VpaJson.jsonStateAt` at every disclosed byte offset. -/
theorem applyRedactionPolicy_characterization {doc : ByteArray} {pol : RedactionSlicePolicy}
    (hConf : checkRedactionDelimiterConfined doc pol = true) :
    (applyRedactionPolicy doc pol).size = doc.size ∧
    (∀ i, i < doc.size →
      byteAt (applyRedactionPolicy doc pol) i =
        if isDisclosedAt pol i then byteAt doc i else 0x2a) ∧
    (∀ i, i < doc.size → isDisclosedAt pol i = true →
      VpaJson.jsonStateAt (applyRedactionPolicy doc pol) i = VpaJson.jsonStateAt doc i) := by
  simp only [checkRedactionDelimiterConfined, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hConf
  obtain ⟨⟨hSz, hDisj⟩, hGaps⟩ := hConf
  have hOrd : GapsOrderedFrom 0 doc.size (elidedGaps pol) := by
    rw [hSz]; exact elidedGapsFrom_ordered _ 0 pol.docByteLen (Nat.zero_le _) hDisj
  obtain ⟨hRedSz, hBytes⟩ := applyGapsMask_size_and_byteAt (elidedGaps pol) 0 doc hOrd
  obtain ⟨_, hStPos⟩ := applyGapsMask_json_invariant (elidedGaps pol) 0 doc hOrd
    (fun g hg => (hGaps g hg).1)
  refine ⟨hRedSz, fun i hi => ?_, fun i hi hDis => ?_⟩
  · unfold applyRedactionPolicy isDisclosedAt
    rw [hBytes i]
    have hEq := isDisclosedAtSpec_eq_not_gap pol.disclosedSpans.toList 0 pol.docByteLen i
      (Nat.zero_le _) (by omega) hDisj
    rw [hEq]
    unfold elidedGaps
    cases (elidedGapsFrom 0 pol.docByteLen pol.disclosedSpans.toList).any (inByteSpan i) <;> rfl
  · have hEq := isDisclosedAtSpec_eq_not_gap pol.disclosedSpans.toList 0 pol.docByteLen i
      (Nat.zero_le _) (by omega) hDisj
    unfold isDisclosedAt at hDis
    rw [hDis] at hEq
    have hNoGap : (elidedGaps pol).any (inByteSpan i) = false := by
      unfold elidedGaps
      cases hg : (elidedGapsFrom 0 pol.docByteLen pol.disclosedSpans.toList).any (inByteSpan i)
      · rfl
      · rw [hg] at hEq; cases hEq
    exact hStPos i hNoGap

/-! ### §2.3 Scanner Soundness & `redaction_cannot_splice_tokens` -/

private theorem extract_eq_of_byteAt_eq {a b : ByteArray} {s e : Nat}
    (hsa : e ≤ a.size) (hsb : e ≤ b.size)
    (hBytes : ∀ k, k < e - s → byteAt a (s + k) = byteAt b (s + k)) :
    a.extract s e = b.extract s e := by
  apply byteArray_eq_of_toList
  rw [Commit.extract_toList, Commit.extract_toList]
  apply List.ext_getElem
  · simp; omega
  · intro k hk₁ hk₂
    have hlt : k < e - s := by simp at hk₁; omega
    have hb := hBytes k hlt
    rw [byteAt_eq_getElem?_toList, byteAt_eq_getElem?_toList] at hb
    have hka : s + k < a.data.toList.length := by rw [toList_length]; omega
    have hkb : s + k < b.data.toList.length := by rw [toList_length]; omega
    rw [List.getElem?_eq_getElem hka, List.getElem?_eq_getElem hkb] at hb
    simpa [List.getElem_take, List.getElem_drop] using hb

private theorem scanTokensGo_sound (buf : ByteArray) :
    ∀ (idx : Nat) (curStart : Option Nat) (acc : Array TokenSpan),
      idx ≤ buf.size →
      (∀ a ∈ acc, IsMaximalTokenSpan buf a = true) →
      (curStart = none → idx = 0 ∨ isTokenPayloadByte (byteAt buf (idx - 1)) = false) →
      (∀ s, curStart = some s →
        s < idx ∧
        (s = 0 ∨ isTokenPayloadByte (byteAt buf (s - 1)) = false) ∧
        (∀ k, k < idx - s → isTokenPayloadByte (byteAt buf (s + k)) = true)) →
      ∀ tok ∈ scanTokensGo buf idx curStart acc, IsMaximalTokenSpan buf tok = true := by
  intro idx curStart acc hIdx hAcc hNone hCur
  induction fuel : buf.size - idx using Nat.strongRecOn generalizing idx curStart acc with
  | ind fuel ih =>
    unfold scanTokensGo
    by_cases hLt : idx < buf.size
    · rw [dite_eq_left hLt]
      have hByteEq : buf[idx]'hLt = byteAt buf idx := by simp [byteAt, hLt]
      by_cases hPay : isTokenPayloadByte (buf[idx]'hLt) = true
      · simp only [hPay, ↓reduceIte]
        rw [hByteEq] at hPay
        cases curStart with
        | some s =>
          obtain ⟨hsLt, hsLeft, hsAll⟩ := hCur s rfl
          refine ih (buf.size - (idx + 1)) (by omega) (idx + 1) (some s) acc (by omega) hAcc
            (fun hn => nomatch hn) ?_ rfl
          intro s' hs'; cases hs'
          refine ⟨by omega, hsLeft, fun k hk => ?_⟩
          by_cases hkOld : k < idx - s
          · exact hsAll k hkOld
          · have hkEq : s + k = idx := by omega
            rwa [hkEq]
        | none =>
          have hLeft := hNone rfl
          refine ih (buf.size - (idx + 1)) (by omega) (idx + 1) (some idx) acc (by omega) hAcc
            (fun hn => nomatch hn) ?_ rfl
          intro s' hs'; cases hs'
          refine ⟨by omega, hLeft, fun k hk => ?_⟩
          have hk0 : k = 0 := by omega
          subst hk0; simpa using hPay
      · have hPayF : isTokenPayloadByte (byteAt buf idx) = false := by
          rw [← hByteEq]; exact Bool.eq_false_iff.mpr hPay
        simp only [hPay, Bool.false_eq_true, ↓reduceIte]
        have hNextNone : Option.none (α := Nat) = none →
            idx + 1 = 0 ∨ isTokenPayloadByte (byteAt buf (idx + 1 - 1)) = false :=
          fun _ => Or.inr (by simpa using hPayF)
        cases curStart with
        | some s =>
          refine ih (buf.size - (idx + 1)) (by omega) (idx + 1) none
            (acc.push ⟨s, idx, buf.extract s idx⟩) (by omega) ?_ hNextNone (fun _ hs => nomatch hs) rfl
          intro a ha
          rcases Array.mem_push.mp ha with ha | rfl
          · exact hAcc a ha
          · obtain ⟨hsLt, hsLeft, hsAll⟩ := hCur s rfl
            simp only [IsMaximalTokenSpan, Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true']
            exact ⟨⟨⟨⟨⟨hsLt, Nat.le_of_lt hLt⟩, trivial⟩, hsAll⟩, hsLeft⟩, Or.inr hPayF⟩
        | none =>
          exact ih (buf.size - (idx + 1)) (by omega) (idx + 1) none acc (by omega) hAcc
            hNextNone (fun _ hs => nomatch hs) rfl
    · rw [dite_eq_right hLt]
      have hEqSz : idx = buf.size := by omega
      subst hEqSz
      cases curStart with
      | none => exact hAcc
      | some s =>
        intro tok hMem
        rcases Array.mem_push.mp hMem with ha | rfl
        · exact hAcc tok ha
        · obtain ⟨hsLt, hsLeft, hsAll⟩ := hCur s rfl
          simp only [IsMaximalTokenSpan, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true']
          exact ⟨⟨⟨⟨⟨hsLt, Nat.le_refl _⟩, trivial⟩, hsAll⟩, hsLeft⟩, Or.inl trivial⟩

/-- Every token returned by `extractTokenSpans` is a valid maximal `TokenSpan` of `buf`. -/
theorem extractTokenSpans_sound (buf : ByteArray) :
    ∀ tok ∈ extractTokenSpans buf, IsMaximalTokenSpan buf tok = true :=
  scanTokensGo_sound buf 0 none #[] (Nat.zero_le _) (fun _ h => nomatch h)
    (fun _ => Or.inl rfl) (fun _ h => nomatch h)

/-- **Stage-1 Master Anti-Splice & Confinement Theorem (`redaction_cannot_splice_tokens`)**:
    Whenever `checkRedactionDelimiterConfined doc pol = true`:
    1. `applyRedactionPolicy doc pol` preserves `runFullJsonGrammar` and `jsonObjectKeys`, AND
    2. Every maximal token `tok` in `applyRedactionPolicy doc pol` (including every
       `tok ∈ extractTokenSpans (applyRedactionPolicy doc pol)`):
       - Lies strictly inside a **single** disclosed interval `sp ∈ pol.disclosedSpans`
         (`sp.1 ≤ tok.start ∧ tok.stop ≤ sp.2`, never bridging across an elided `[l, r)` gap!),
       - Reaches the identical stateful JSON machine configuration `VpaJson.jsonStateAt` at `tok.start`,
       - Is an **exact, un-truncated maximal token of the unredacted `doc`**
         (`IsMaximalTokenSpan doc tok = true`), so redaction cannot truncate `"admin_revoked"` into `"admin"`
         or splice adjacent fragments into a synthetic claim. -/
theorem redaction_cannot_splice_tokens {doc : ByteArray} {pol : RedactionSlicePolicy}
    (hConf : checkRedactionDelimiterConfined doc pol = true) :
    VpaJson.runFullJsonGrammar (applyRedactionPolicy doc pol) = VpaJson.runFullJsonGrammar doc ∧
    VpaJson.jsonObjectKeys (applyRedactionPolicy doc pol) = VpaJson.jsonObjectKeys doc ∧
    ∀ tok : TokenSpan, IsMaximalTokenSpan (applyRedactionPolicy doc pol) tok = true →
      (∃ sp ∈ pol.disclosedSpans.toList, sp.1 ≤ tok.start ∧ tok.stop ≤ sp.2) ∧
      VpaJson.jsonStateAt (applyRedactionPolicy doc pol) tok.start = VpaJson.jsonStateAt doc tok.start ∧
      IsMaximalTokenSpan doc tok = true := by
  obtain ⟨_, hGram, hKeys⟩ := redactionPolicy_preserves_json_grammar_and_keys hConf
  obtain ⟨hRedSz, hRedByte, hRedState⟩ := applyRedactionPolicy_characterization hConf
  simp only [checkRedactionDelimiterConfined, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hConf
  obtain ⟨⟨hDocSz, hDisj⟩, hGapProps⟩ := hConf
  have hOrd : GapsOrderedFrom 0 pol.docByteLen (elidedGaps pol) :=
    elidedGapsFrom_ordered _ 0 pol.docByteLen (Nat.zero_le _) hDisj
  refine ⟨hGram, hKeys, fun tok hMax => ?_⟩
  simp only [IsMaximalTokenSpan, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true', hRedSz] at hMax
  obtain ⟨⟨⟨⟨⟨hStLt, hStopLe⟩, hBytesEq⟩, hAllPay⟩, hLeftMax⟩, hRightMax⟩ := hMax
  have hEachDisAndEq : ∀ i, tok.start ≤ i → i < tok.stop →
      isDisclosedAt pol i = true ∧ byteAt doc i = byteAt (applyRedactionPolicy doc pol) i := by
    intro i hlo hhi
    have hk : i - tok.start < tok.stop - tok.start := by omega
    have hPay := hAllPay (i - tok.start) hk
    rw [show tok.start + (i - tok.start) = i by omega] at hPay
    have hB := hRedByte i (by omega)
    cases hDis : isDisclosedAt pol i with
    | false =>
      simp only [hDis, Bool.false_eq_true, ↓reduceIte] at hB
      rw [hB] at hPay
      have hFalse := isTokenPayloadByte_placeholder_false ()
      rw [hFalse] at hPay; cases hPay
    | true =>
      simp only [hDis, ↓reduceIte] at hB
      exact ⟨rfl, hB.symm⟩
  have hSingleSpan := disclosedRange_sub_single_span pol.disclosedSpans.toList 0 pol.docByteLen
    tok.start tok.stop hDisj hStLt (fun i hlo hhi => (hEachDisAndEq i hlo hhi).1)
  have hStartDis : isDisclosedAt pol tok.start = true := (hEachDisAndEq tok.start (Nat.le_refl _) hStLt).1
  have hStEq := hRedState tok.start (by omega) hStartDis
  have hSliceEq : tok.bytes.data.toList = (doc.extract tok.start tok.stop).data.toList := by
    rw [hBytesEq]
    exact congrArg (fun b : ByteArray => b.data.toList)
      (extract_eq_of_byteAt_eq (by rw [hRedSz]; exact hStopLe) hStopLe
        (fun k hk => (hEachDisAndEq (tok.start + k) (by omega) (by omega)).2.symm))
  have hGapIff : ∀ p, p < doc.size →
      ((elidedGaps pol).any (inByteSpan p) = false ↔ isDisclosedAt pol p = true) := by
    intro p hp
    have hEq := isDisclosedAtSpec_eq_not_gap pol.disclosedSpans.toList 0 pol.docByteLen p
      (Nat.zero_le _) (by omega) hDisj
    unfold isDisclosedAt elidedGaps
    rw [hEq]
    cases (elidedGapsFrom 0 pol.docByteLen pol.disclosedSpans.toList).any (inByteSpan p) <;> simp
  have hLeftDoc : tok.start = 0 ∨ isTokenPayloadByte (byteAt doc (tok.start - 1)) = false := by
    rcases hLeftMax with h0 | hNotPayRed
    · exact Or.inl h0
    · by_cases h0 : tok.start = 0
      · exact Or.inl h0
      · right
        have hStartNoGap : (elidedGaps pol).any (inByteSpan tok.start) = false :=
          (hGapIff tok.start (by omega)).mpr hStartDis
        cases hPrevGap : (elidedGaps pol).any (inByteSpan (tok.start - 1)) with
        | false =>
          have hPrevDis : isDisclosedAt pol (tok.start - 1) = true :=
            (hGapIff (tok.start - 1) (by omega)).mp hPrevGap
          have hPrevB := hRedByte (tok.start - 1) (by omega)
          simp only [hPrevDis, ↓reduceIte] at hPrevB
          rwa [← hPrevB]
        | true =>
          exfalso
          obtain ⟨l, hMemGap⟩ := gap_ends_at_of_undisclosed_pred (elidedGaps pol) 0 pol.docByteLen
            tok.start hOrd (by omega) hPrevGap hStartNoGap
          have hDelim := (hGapProps (l, tok.start) hMemGap).2
          simp only [gapDelimiterBounded, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, Bool.not_eq_true'] at hDelim
          rcases hDelim.2 with hEqEnd | hDocStartFalse
          · omega
          · have hStartPay := hAllPay 0 (by omega)
            rw [Nat.add_zero, ← (hEachDisAndEq tok.start (Nat.le_refl _) hStLt).2] at hStartPay
            rw [hStartPay] at hDocStartFalse; cases hDocStartFalse
  have hRightDoc : tok.stop = doc.size ∨ isTokenPayloadByte (byteAt doc tok.stop) = false := by
    rcases hRightMax with hEnd | hNotPayRed
    · exact Or.inl hEnd
    · by_cases hEnd : tok.stop = doc.size
      · exact Or.inl hEnd
      · right
        have hLastDis : isDisclosedAt pol (tok.stop - 1) = true :=
          (hEachDisAndEq (tok.stop - 1) (by omega) (by omega)).1
        have hLastNoGap : (elidedGaps pol).any (inByteSpan (tok.stop - 1)) = false :=
          (hGapIff (tok.stop - 1) (by omega)).mpr hLastDis
        cases hStopGap : (elidedGaps pol).any (inByteSpan tok.stop) with
        | false =>
          have hStopDis : isDisclosedAt pol tok.stop = true :=
            (hGapIff tok.stop (by omega)).mp hStopGap
          have hStopB := hRedByte tok.stop (by omega)
          simp only [hStopDis, ↓reduceIte] at hStopB
          rwa [← hStopB]
        | true =>
          exfalso
          obtain ⟨r, hMemGap⟩ := gap_starts_at_of_undisclosed_curr (elidedGaps pol) 0 pol.docByteLen
            tok.stop hOrd (by omega) hLastNoGap hStopGap
          have hDelim := (hGapProps (tok.stop, r) hMemGap).2
          simp only [gapDelimiterBounded, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, Bool.not_eq_true'] at hDelim
          rcases hDelim.1 with hStopZero | hDocPrevFalse
          · omega
          · have hLastPay := hAllPay (tok.stop - 1 - tok.start) (by omega)
            rw [show tok.start + (tok.stop - 1 - tok.start) = tok.stop - 1 by omega,
                ← (hEachDisAndEq (tok.stop - 1) (by omega) (by omega)).2] at hLastPay
            rw [hLastPay] at hDocPrevFalse; cases hDocPrevFalse
  refine ⟨hSingleSpan, hStEq, ?_⟩
  simp only [IsMaximalTokenSpan, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨hStLt, hStopLe⟩, hSliceEq⟩, fun k hk => ?_⟩, hLeftDoc⟩, hRightDoc⟩
  rw [(hEachDisAndEq (tok.start + k) (by omega) (by omega)).2]
  exact hAllPay k hk

/-- Non-vacuity / inhabitedness witness for `checkRedactionDelimiterConfined`, `IsMaximalTokenSpan`,
    and `isTokenPayloadByte`: redacting `"secret"` in `{"k":"a","s":"secret"}` passes
    `checkRedactionDelimiterConfined` and preserves `"a"` as an exact maximal token. -/
theorem checkRedactionDelimiterConfined_inhabited (u : Unit) :
    let _ := u
    let doc := "{\"k\":\"a\",\"s\":\"secret\"}".toByteArray
    let pol : RedactionSlicePolicy := ⟨22, #[(0, 14), (20, 22)]⟩
    isTokenPayloadByte 0x61 = true ∧
    IsMaximalTokenSpan doc ⟨6, 7, "a".toByteArray⟩ = true ∧
    checkRedactionDelimiterConfined doc pol = true ∧
    0 < (extractTokenSpans (applyRedactionPolicy doc pol)).size := by
  decide +kernel

end Obend.SemanticKG
end
