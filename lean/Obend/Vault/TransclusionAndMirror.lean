module
/-
# Obend.Vault.TransclusionAndMirror — a quote that cites its receipt, and a render that says who checked

1. **Transclusion.** A source cell's history is a chain of finalized receipts. A receipt's header
   carries the digest of its predecessor, its height, and a 32-byte cSHAKE256 commitment of each
   field (name and value, length-framed); the receipt's own digest is cSHAKE256 of the framed
   header. A `Transclusion` cites a receipt by digest and height and quotes one field's bytes.
   `admitTransclusion` checks the citation against the headers a reader holds, by digest.
   * `transclusion_is_observed_finalized_read`: an admitted quote cites a receipt in the finalized
     chain; what the source has staged and not finalized cannot be cited and changes no admission.
   * `transclusion_provenance_faithful`: the admitted bytes are the bytes the source finalized in
     that field at the cited receipt, or two receipts of the chain collide, or the two field
     preimages do.
   * `transclusion_forge_refused`: beside an admitted quote, a quote of the same citation whose
     commitment differs is refused with `digestMismatch`; any different value is refused or is a
     collision (`transclusion_lying_value_refused_or_collides`).
   * `transclusion_no_amplify`: a document that transcludes, any number of times, holds over the
     source exactly what it held; a write it could not make before is still refused.
   * `transclusion_stable_under_source_advance`: after the source finalizes any further turns, the
     same citation is admitted with the same bytes, dated against the new head: on a linked chain
     the staleness grows by the number of turns and is reported, never hidden.

2. **The mirror badge.** A render of an object is made by some party after some of the
   `VerificationGate`s ran on the reader's side. `classifyMirrorRender` gives the only badge the
   outcomes support: `selfVerifiedLocal` when every gate passed, a refusal naming a gate that
   failed, and otherwise `untrustedOriginMirror` listing every skipped gate with the canonical
   `obend://` address at which the reader can check for itself. `verifyMirrorBadge` validates a
   badge someone else produced. `serverMirror_never_claims_selfVerified` and
   `serverMirror_reports_all_skipped_gates` hold of both. Two gates are computed here:
   `chainGate` (the headers link by digest and height, as every chain `SourceCell.advance` builds
   does: `advance_linked`) and `transclusionGate`.
-/
public import Obend.Vault.FrustumMembrane

public section

namespace Obend.Vault.TransclusionAndMirror

set_option autoImplicit false

open Obend.Vault.Affordance (Auth fireGate)
open Obend.Vault.Rehydration (InteractionLog confined)
open Obend.Vault.FrustumMembrane (utf8 utf8_injective)
open Obend.Crypto (cshake32ByteArray cshake32ByteArray_size encodeListField
  encodeListField_prefix_inj leb128 leb128_prefix_inj byteArray_eq_of_toList_eq)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.HashBytes (CollisionAmong)
open Obend.Polis (cshake32_binds)

/-! ## 1. Field commitments and receipt digests -/

/-- Customization string of the field hash. -/
def fieldCustomization : List UInt8 := "OBEND.VAULT.TRANSCLUSION.FIELD/v1".toUTF8.data.toList

/-- What a field commitment hashes: the field's name and its value, each length-framed. -/
def fieldPreimage (name : String) (value : List UInt8) : List UInt8 :=
  encodeListField (utf8 name) ++ encodeListField value

/-- The 32-byte commitment of one finalized field. -/
def fieldCommit (name : String) (value : List UInt8) : ByteArray :=
  cshake32ByteArray fieldCustomization (fieldPreimage name value)

theorem fieldPreimage_injective {n₁ n₂ : String} {v₁ v₂ : List UInt8}
    (h : fieldPreimage n₁ v₁ = fieldPreimage n₂ v₂) : n₁ = n₂ ∧ v₁ = v₂ := by
  unfold fieldPreimage at h
  obtain ⟨hn, h⟩ := encodeListField_prefix_inj h
  obtain ⟨hv, _⟩ := encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)
  exact ⟨utf8_injective hn, hv⟩

theorem fieldCommit_size (name : String) (value : List UInt8) : (fieldCommit name value).size = 32 :=
  cshake32ByteArray_size _ _

/-- Equal commitments of a field hide equal values, or the two preimages collide. -/
theorem fieldCommit_binds {n : String} {v₁ v₂ : List UInt8} (h : fieldCommit n v₁ = fieldCommit n v₂) :
    v₁ = v₂ ∨ CollisionAmong (cshake256Bytes fieldCustomization)
      (fun x => x = fieldPreimage n v₁ ∨ x = fieldPreimage n v₂) :=
  (cshake32_binds fieldCustomization h).imp (fun hp => (fieldPreimage_injective hp).2) id

/-- A finalized receipt as a reader holds it: the predecessor's digest, the height, and the
commitment of each field. -/
structure ReceiptHeader where
  prev : ByteArray
  height : Nat
  commits : List (String × ByteArray)
deriving DecidableEq

/-- Each commitment tagged and framed; the list closed by a zero tag. -/
def encodeCommits : List (String × ByteArray) → List UInt8
  | [] => [0]
  | e :: rest => 1 :: (encodeListField (utf8 e.1) ++ (encodeListField e.2.data.toList ++ encodeCommits rest))

theorem encodeCommits_injective : ∀ (a b : List (String × ByteArray)),
    encodeCommits a = encodeCommits b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encodeCommits] at h
  | _ :: _, [], h => by simp [encodeCommits] at h
  | (n₁, c₁) :: r₁, (n₂, c₂) :: r₂, h => by
    simp only [encodeCommits, List.cons.injEq, true_and] at h
    obtain ⟨hn, h⟩ := encodeListField_prefix_inj h
    obtain ⟨hc, h⟩ := encodeListField_prefix_inj h
    rw [utf8_injective hn, byteArray_eq_of_toList_eq hc, encodeCommits_injective r₁ r₂ h]

/-- Customization string of the receipt hash. -/
def receiptCustomization : List UInt8 := "OBEND.VAULT.TRANSCLUSION.RECEIPT/v1".toUTF8.data.toList

/-- What a receipt digest hashes: every field of the header, framed. -/
def receiptPreimage (h : ReceiptHeader) : List UInt8 :=
  encodeListField h.prev.data.toList ++ (leb128 h.height ++ encodeCommits h.commits)

theorem receiptPreimage_injective {h₁ h₂ : ReceiptHeader}
    (h : receiptPreimage h₁ = receiptPreimage h₂) : h₁ = h₂ := by
  unfold receiptPreimage at h
  obtain ⟨hp, h⟩ := encodeListField_prefix_inj h
  obtain ⟨hh, h⟩ := leb128_prefix_inj h
  cases h₁; cases h₂
  simp only [ReceiptHeader.mk.injEq]
  exact ⟨byteArray_eq_of_toList_eq hp, hh, encodeCommits_injective _ _ h⟩

/-- The 32-byte digest that names a receipt. -/
def receiptDigest (h : ReceiptHeader) : ByteArray :=
  cshake32ByteArray receiptCustomization (receiptPreimage h)

theorem receiptDigest_size (h : ReceiptHeader) : (receiptDigest h).size = 32 :=
  cshake32ByteArray_size _ _

/-- Equal digests name equal receipts, or the two headers collide under the receipt hash. -/
theorem receiptDigest_binds {h₁ h₂ : ReceiptHeader} (h : receiptDigest h₁ = receiptDigest h₂) :
    h₁ = h₂ ∨ CollisionAmong (cshake256Bytes receiptCustomization)
      (fun x => x = receiptPreimage h₁ ∨ x = receiptPreimage h₂) :=
  (cshake32_binds receiptCustomization h).imp receiptPreimage_injective id

/-! ## 2. The source cell and its history -/

/-- A finalized turn as its source holds it: the fields in cleartext. -/
structure Receipt where
  prev : ByteArray
  height : Nat
  fields : List (String × List UInt8)
deriving DecidableEq

def Receipt.header (r : Receipt) : ReceiptHeader :=
  { prev := r.prev, height := r.height, commits := r.fields.map fun e => (e.1, fieldCommit e.1 e.2) }

/-- A source cell: its finalized receipts, oldest first, and what it has staged and not finalized. -/
structure SourceCell where
  finalized : List Receipt
  draft : List (String × List UInt8)

/-- The predecessor digest of the first receipt: thirty-two zero bytes. -/
def genesisDigest : ByteArray := ⟨Array.replicate 32 0⟩

/-- The digest of the last header of a chain. -/
def headDigest (chain : List ReceiptHeader) : ByteArray :=
  match chain.getLast? with
  | some h => receiptDigest h
  | none => genesisDigest

/-- What a reader holds of the source: the headers of its finalized receipts. -/
def SourceCell.observed (s : SourceCell) : List ReceiptHeader := s.finalized.map Receipt.header

def SourceCell.stage (s : SourceCell) (fields : List (String × List UInt8)) : SourceCell :=
  { s with draft := fields }

/-- Finalize the staged fields as the next receipt. -/
def SourceCell.finalize (s : SourceCell) : SourceCell :=
  { finalized := s.finalized ++ [⟨headDigest s.observed, s.finalized.length, s.draft⟩], draft := [] }

/-- The source takes further turns, each staged and finalized. -/
def SourceCell.advance (s : SourceCell) (turns : List (List (String × List UInt8))) : SourceCell :=
  turns.foldl (fun s fields => (s.stage fields).finalize) s

/-- The past is a prefix of the future: advancing appends one receipt per turn and alters none. -/
theorem advance_finalized (turns : List (List (String × List UInt8))) : ∀ s : SourceCell,
    ∃ more, (s.advance turns).finalized = s.finalized ++ more ∧ more.length = turns.length := by
  induction turns with
  | nil => intro s; exact ⟨[], by simp [SourceCell.advance], rfl⟩
  | cons t ts ih =>
    intro s
    obtain ⟨more, hm, hl⟩ := ih (s.stage t).finalize
    refine ⟨⟨headDigest s.observed, s.finalized.length, t⟩ :: more, ?_, by simp [hl]⟩
    show ((s.stage t).finalize.advance ts).finalized = _
    rw [hm]
    simp [SourceCell.finalize, SourceCell.stage, SourceCell.observed]

/-- The headers link: each names its predecessor's digest and the next height. -/
def linkedFrom : ByteArray → Nat → List ReceiptHeader → Bool
  | _, _, [] => true
  | prev, height, h :: rest =>
    decide (h.prev = prev) && h.height == height && linkedFrom (receiptDigest h) (height + 1) rest

theorem linkedFrom_append (b : ReceiptHeader) : ∀ (a : List ReceiptHeader) (prev : ByteArray)
    (height : Nat), linkedFrom prev height a = true →
    b.prev = (match a.getLast? with | some h => receiptDigest h | none => prev) →
    b.height = height + a.length → linkedFrom prev height (a ++ [b]) = true
  | [], prev, height, _, hp, hh => by simp_all [linkedFrom]
  | x :: xs, prev, height, hl, hp, hh => by
    simp only [linkedFrom, Bool.and_eq_true] at hl
    simp only [List.cons_append, linkedFrom, Bool.and_eq_true]
    refine ⟨hl.1, linkedFrom_append b xs _ _ hl.2 ?_ (by simp at hh; omega)⟩
    cases xs with
    | nil => simpa using hp
    | cons y ys =>
      rw [List.getLast?_cons_cons] at hp
      cases hg : (y :: ys).getLast? with
      | none => simp at hg
      | some z => rw [hg] at hp; simpa using hp

/-- On a linked chain a header's height is its position. -/
theorem linked_height_lt : ∀ (chain : List ReceiptHeader) (prev : ByteArray) (k : Nat)
    (hd : ReceiptHeader), linkedFrom prev k chain = true → hd ∈ chain → hd.height < k + chain.length
  | [], _, _, _, _, hm => by simp at hm
  | x :: xs, _, k, hd, hl, hm => by
    simp only [linkedFrom, Bool.and_eq_true, beq_iff_eq] at hl
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [List.length_cons]; omega
    · have := linked_height_lt xs _ (k + 1) hd hl.2 hm
      simp only [List.length_cons]; omega

/-- Finalizing keeps a linked chain linked. -/
theorem finalize_linked (s : SourceCell) (h : linkedFrom genesisDigest 0 s.observed = true) :
    linkedFrom genesisDigest 0 s.finalize.observed = true := by
  have hobs : s.finalize.observed = s.observed ++
      [(⟨headDigest s.observed, s.finalized.length, s.draft⟩ : Receipt).header] := by
    simp [SourceCell.observed, SourceCell.finalize]
  rw [hobs]
  apply linkedFrom_append _ _ _ _ h
  · simp only [Receipt.header, headDigest]
    cases s.observed.getLast? <;> rfl
  · simp [Receipt.header, SourceCell.observed]

/-- **Every chain a source builds by finalizing turns is linked.** -/
theorem advance_linked (turns : List (List (String × List UInt8))) : ∀ s : SourceCell,
    linkedFrom genesisDigest 0 s.observed = true →
    linkedFrom genesisDigest 0 (s.advance turns).observed = true := by
  induction turns with
  | nil => intro s h; exact h
  | cons t ts ih => intro s h; exact ih _ (finalize_linked (s.stage t) h)

/-! ## 3. Transclusion -/

/-- A quote of one field of a cited receipt. -/
structure Transclusion where
  cited : ByteArray
  height : Nat
  field : String
  quote : List UInt8
deriving DecidableEq

/-- Why a transclusion was not admitted. -/
inductive TransclusionRefusal where
  | uncitedReceipt
  | heightMismatch (found : Nat)
  | fieldAbsent
  | digestMismatch
deriving DecidableEq, Repr

/-- An admitted quote, dated: the height it cites and the height of the head it was checked
against. -/
structure DatedQuote where
  quote : List UInt8
  citedHeight : Nat
  headHeight : Nat
deriving DecidableEq, Repr

/-- How many receipts the source has finalized past the cited one. -/
def DatedQuote.staleness (d : DatedQuote) : Nat := d.headHeight - d.citedHeight

/-- **Admit a transclusion against the headers a reader holds**, or say why not. The quoted bytes
are compared by commitment with what the cited receipt committed. -/
def admitTransclusion (chain : List ReceiptHeader) (t : Transclusion) :
    Except TransclusionRefusal DatedQuote :=
  match chain.find? (fun h => decide (receiptDigest h = t.cited)) with
  | none => .error .uncitedReceipt
  | some h =>
    if h.height = t.height then
      match h.commits.lookup t.field with
      | none => .error .fieldAbsent
      | some c =>
        if fieldCommit t.field t.quote = c then .ok ⟨t.quote, t.height, chain.length - 1⟩
        else .error .digestMismatch
    else .error (.heightMismatch h.height)

/-- What an admission found. -/
theorem admit_ok {chain : List ReceiptHeader} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion chain t = .ok d) :
    ∃ hd, chain.find? (fun h => decide (receiptDigest h = t.cited)) = some hd ∧
      hd.height = t.height ∧ hd.commits.lookup t.field = some (fieldCommit t.field t.quote) ∧
      d = ⟨t.quote, t.height, chain.length - 1⟩ := by
  unfold admitTransclusion at h
  split at h
  · cases h
  · rename_i hd hfind
    split at h
    · rename_i hh
      split at h
      · cases h
      · rename_i c hc
        split at h
        · rename_i hq
          simp only [Except.ok.injEq] at h
          exact ⟨hd, hfind, hh, by rw [hc, hq], h.symm⟩
        · cases h
    · cases h

/-- A citation found, at its height, with its field committed to the quote, is admitted. -/
theorem admit_of_find {chain : List ReceiptHeader} {t : Transclusion} {hd : ReceiptHeader}
    (hfind : chain.find? (fun h => decide (receiptDigest h = t.cited)) = some hd)
    (hh : hd.height = t.height)
    (hc : hd.commits.lookup t.field = some (fieldCommit t.field t.quote)) :
    admitTransclusion chain t = .ok ⟨t.quote, t.height, chain.length - 1⟩ := by
  unfold admitTransclusion
  rw [hfind]
  simp [hh, hc]

theorem lookup_commits (k : String) : ∀ fields : List (String × List UInt8),
    (fields.map fun e => (e.1, fieldCommit e.1 e.2)).lookup k = (fields.lookup k).map (fieldCommit k)
  | [] => rfl
  | (n, v) :: rest => by
    by_cases hk : k = n
    · subst hk; simp [List.lookup]
    · have hne : (k == n) = false := by simpa using hk
      simp only [List.map_cons, List.lookup, hne]
      exact lookup_commits k rest

/-- **A transclusion is a read of an observed, finalized receipt.** An admitted quote cites a
receipt of the source's finalized chain, at its height, with the quoted field committed there; and
what the source has merely staged plays no part: staging anything leaves every admission as it was. -/
theorem transclusion_is_observed_finalized_read {s : SourceCell} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion s.observed t = .ok d) :
    (∃ r, r ∈ s.finalized ∧ receiptDigest r.header = t.cited ∧ r.height = t.height ∧
      (r.fields.lookup t.field).map (fieldCommit t.field) = some (fieldCommit t.field t.quote)) ∧
    ∀ staged, admitTransclusion (s.stage staged).observed t = .ok d := by
  obtain ⟨hd, hfind, hh, hc, _⟩ := admit_ok h
  refine ⟨?_, fun _ => h⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
  have hdig := List.find?_some hfind
  refine ⟨r, hr, by simpa using hdig, hh, ?_⟩
  rw [← lookup_commits]
  exact hc

/-- **Provenance is faithful.** Let `r₀` be a finalized receipt with the cited digest, holding
value `v` in the quoted field. Then an admitted quote is `v`, byte for byte; or two receipts of the
observed chain collide under the receipt hash; or the quote and `v` collide under the field hash. -/
theorem transclusion_provenance_faithful {s : SourceCell} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion s.observed t = .ok d) {r₀ : Receipt} (hr₀ : r₀ ∈ s.finalized)
    (hcite : receiptDigest r₀.header = t.cited) {v : List UInt8}
    (hv : r₀.fields.lookup t.field = some v) :
    d.quote = t.quote ∧
    (t.quote = v ∨
      CollisionAmong (cshake256Bytes receiptCustomization)
        (fun x => ∃ hd, hd ∈ s.observed ∧ x = receiptPreimage hd) ∨
      CollisionAmong (cshake256Bytes fieldCustomization)
        (fun x => x = fieldPreimage t.field t.quote ∨ x = fieldPreimage t.field v)) := by
  obtain ⟨hd, hfind, _, hc, rfl⟩ := admit_ok h
  refine ⟨rfl, ?_⟩
  have hmem : hd ∈ s.observed := List.mem_of_find?_eq_some hfind
  have hdig : receiptDigest hd = receiptDigest r₀.header := by
    have := List.find?_some hfind
    rw [hcite]
    simpa using this
  rcases receiptDigest_binds hdig with heq | hcol
  · subst heq
    have hc' : (r₀.fields.lookup t.field).map (fieldCommit t.field) =
        some (fieldCommit t.field t.quote) := by
      rw [← lookup_commits]; exact hc
    rw [hv] at hc'
    simp only [Option.map_some, Option.some.injEq] at hc'
    rcases fieldCommit_binds hc'.symm with hq | hcol
    · exact .inl hq
    · exact .inr (.inr hcol)
  · refine .inr (.inl (hcol.mono fun x hx => ?_))
    rcases hx with rfl | rfl
    · exact ⟨hd, hmem, rfl⟩
    · exact ⟨r₀.header, List.mem_map.mpr ⟨r₀, hr₀, rfl⟩, rfl⟩

/-- **A forged quote is refused.** Beside an admitted transclusion, one with the same citation and
field whose commitment differs is refused, and the refusal is `digestMismatch`. -/
theorem transclusion_forge_refused {chain : List ReceiptHeader} {t forged : Transclusion}
    {d : DatedQuote} (h : admitTransclusion chain t = .ok d)
    (hcited : forged.cited = t.cited) (hheight : forged.height = t.height)
    (hfield : forged.field = t.field)
    (hdigest : fieldCommit forged.field forged.quote ≠ fieldCommit t.field t.quote) :
    admitTransclusion chain forged = .error .digestMismatch := by
  obtain ⟨hd, hfind, hh, hc, _⟩ := admit_ok h
  unfold admitTransclusion
  rw [hcited, hfind]
  simp only [hheight, hh, ↓reduceIte, hfield, hc]
  rw [hfield] at hdigest
  simp [hdigest]

/-- **A lying value is refused, or it is a collision.** A quote of the same citation with different
bytes is refused with `digestMismatch`, unless the two values collide under the field hash. -/
theorem transclusion_lying_value_refused_or_collides {chain : List ReceiptHeader}
    {t forged : Transclusion} {d : DatedQuote} (h : admitTransclusion chain t = .ok d)
    (hcited : forged.cited = t.cited) (hheight : forged.height = t.height)
    (hfield : forged.field = t.field) (hlie : forged.quote ≠ t.quote) :
    admitTransclusion chain forged = .error .digestMismatch ∨
      CollisionAmong (cshake256Bytes fieldCustomization)
        (fun x => x = fieldPreimage t.field forged.quote ∨ x = fieldPreimage t.field t.quote) := by
  by_cases hdig : fieldCommit forged.field forged.quote = fieldCommit t.field t.quote
  · rw [hfield] at hdig
    rcases fieldCommit_binds hdig with hq | hcol
    · exact absurd hq hlie
    · exact .inr hcol
  · exact .inl (transclusion_forge_refused h hcited hheight hfield hdig)

/-- **A citation survives the source's future.** After the source finalizes any further turns, an
admitted transclusion is admitted again with the same bytes at the same cited height, dated against
the new head; on a linked chain its staleness has grown by exactly the number of turns, and is in
the result. The cited receipt itself is still in the chain, unaltered (`advance_finalized`). -/
theorem transclusion_stable_under_source_advance {s : SourceCell} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion s.observed t = .ok d) (turns : List (List (String × List UInt8))) :
    admitTransclusion (s.advance turns).observed t =
      .ok { d with headHeight := d.headHeight + turns.length } ∧
    (linkedFrom genesisDigest 0 s.observed = true →
      ({ d with headHeight := d.headHeight + turns.length } : DatedQuote).staleness =
        d.staleness + turns.length) := by
  obtain ⟨hd, hfind, hh, hc, rfl⟩ := admit_ok h
  obtain ⟨more, hmore, hlen⟩ := advance_finalized turns s
  have hobs : (s.advance turns).observed = s.observed ++ more.map Receipt.header := by
    simp [SourceCell.observed, hmore]
  have hmem : hd ∈ s.observed := List.mem_of_find?_eq_some hfind
  have hpos : 0 < s.observed.length := List.length_pos_of_mem hmem
  have hfind' : (s.advance turns).observed.find? (fun h => decide (receiptDigest h = t.cited)) =
      some hd := by rw [hobs, List.find?_append, hfind]; rfl
  have hlen' : (s.advance turns).observed.length - 1 = s.observed.length - 1 + turns.length := by
    rw [hobs, List.length_append, List.length_map, hlen]; omega
  refine ⟨by rw [admit_of_find hfind' hh hc, hlen'], fun hlinked => ?_⟩
  have hlt := linked_height_lt s.observed _ 0 hd hlinked hmem
  show s.observed.length - 1 + turns.length - t.height =
    s.observed.length - 1 - t.height + turns.length
  omega

/-- A document that quotes a source: what its holder holds over the source cell, and its quotes. -/
structure Document where
  held : List Auth
  quotes : List DatedQuote

/-- Transclude: an admitted quote is added to the document; a refused one changes nothing. -/
def Document.transclude (doc : Document) (chain : List ReceiptHeader) (t : Transclusion) : Document :=
  match admitTransclusion chain t with
  | .ok d => { doc with quotes := doc.quotes ++ [d] }
  | .error _ => doc

def Document.transcludeAll (doc : Document) (chain : List ReceiptHeader) (ts : List Transclusion) :
    Document :=
  ts.foldl (fun d t => d.transclude chain t) doc

/-- What a document's holder may ask of the source cell. -/
inductive SourceRequest where
  | read
  | write (fields : List (String × List UInt8))
  | invoke (affordance : String)

def SourceRequest.needs : SourceRequest → List Auth
  | .read => [.read]
  | .write _ => [.write]
  | .invoke _ => [.call]

/-- The source serves a request only under the rights the document's holder holds; a served write
is a finalized turn. -/
def serveSource (doc : Document) (s : SourceCell) (req : SourceRequest) : Option SourceCell :=
  if fireGate req.needs doc.held then
    some (match req with
      | .write fields => (s.stage fields).finalize
      | _ => s)
  else none

theorem transcludeAll_held (chain : List ReceiptHeader) (ts : List Transclusion) :
    ∀ doc : Document, (doc.transcludeAll chain ts).held = doc.held := by
  induction ts with
  | nil => intro doc; rfl
  | cons t ts ih =>
    intro doc
    show ((doc.transclude chain t).transcludeAll chain ts).held = doc.held
    rw [ih]
    unfold Document.transclude
    split <;> rfl

/-- **Transclusion confers no authority.** After any number of transclusions a document's holder
holds over the source exactly what it held; the source answers every request as it would have; and
a holder without `write` or `call` still has every write and every invocation refused. -/
theorem transclusion_no_amplify (doc : Document) (s : SourceCell) (ts : List Transclusion) :
    (doc.transcludeAll s.observed ts).held = doc.held ∧
    (∀ req, serveSource (doc.transcludeAll s.observed ts) s req = serveSource doc s req) ∧
    (Auth.write ∉ doc.held → ∀ fields,
      serveSource (doc.transcludeAll s.observed ts) s (.write fields) = none) ∧
    (Auth.call ∉ doc.held → ∀ aff,
      serveSource (doc.transcludeAll s.observed ts) s (.invoke aff) = none) := by
  have hheld := transcludeAll_held s.observed ts doc
  refine ⟨hheld, fun req => by simp [serveSource, hheld], fun hw fields => ?_, fun hc aff => ?_⟩
  · simp [serveSource, hheld, SourceRequest.needs, fireGate, hw]
  · simp [serveSource, hheld, SourceRequest.needs, fireGate, hc]

/-! ## 4. The mirror badge: who checked this -/

/-- The checks a reader's own machine can run on an object before believing a render of it. -/
inductive VerificationGate where
  | receiptChain
  | proofSignature
  | capabilityMembrane
  | transclusionProvenance
  | confinementReplay
deriving DecidableEq, Repr

def VerificationGate.all : List VerificationGate :=
  [.receiptChain, .proofSignature, .capabilityMembrane, .transclusionProvenance, .confinementReplay]

theorem VerificationGate.mem_all (g : VerificationGate) : g ∈ VerificationGate.all := by
  cases g <;> simp [VerificationGate.all]

/-- What became of a gate on the reader's side. -/
inductive GateOutcome where
  | passed
  | failed
  | skipped
deriving DecidableEq, Repr

/-- The outcome of a check that may not have run. -/
def GateOutcome.ofCheck : Option Bool → GateOutcome
  | some true => .passed
  | some false => .failed
  | none => .skipped

/-- Who checked: the reader's own machine, every gate; or nobody the reader can vouch for. -/
inductive MirrorTier where
  | selfVerifiedLocal
  | untrustedOriginMirror
deriving DecidableEq, Repr

/-- The canonical address of an object: its kind and its 32-byte content address. -/
structure ObendUri where
  kind : String
  address : ByteArray
deriving DecidableEq

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- `obend://<kind>/<hex address>`. -/
def ObendUri.render (u : ObendUri) : String :=
  "obend://" ++ u.kind ++ "/" ++
    String.ofList (u.address.data.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- The badge a render bears: its tier, the gates that did not run, and where to check instead. -/
structure MirrorRender where
  tier : MirrorTier
  skipped : List VerificationGate
  upgrade : ObendUri
deriving DecidableEq

/-- Why no render is shown. -/
inductive RenderRefusal where
  | gateFailed (gate : VerificationGate)
  | badAddress
deriving DecidableEq, Repr

/-- The gates an outcome table leaves skipped, in ladder order. -/
def skippedGates (outcomes : VerificationGate → GateOutcome) : List VerificationGate :=
  VerificationGate.all.filter fun g => outcomes g == .skipped

/-- **Classify a render.** A failed gate refuses it. With every gate passed it is self-verified;
otherwise it is an untrusted mirror listing every skipped gate. -/
def classifyMirrorRender (outcomes : VerificationGate → GateOutcome) (kind : String)
    (address : ByteArray) : Except RenderRefusal MirrorRender :=
  if address.size = 32 then
    match VerificationGate.all.find? (fun g => outcomes g == .failed) with
    | some g => .error (.gateFailed g)
    | none =>
      match skippedGates outcomes with
      | [] => .ok ⟨.selfVerifiedLocal, [], ⟨kind, address⟩⟩
      | g :: gs => .ok ⟨.untrustedOriginMirror, g :: gs, ⟨kind, address⟩⟩
  else .error .badAddress

/-- **Validate a badge someone else produced** against what the reader's machine ran. -/
def verifyMirrorBadge (outcomes : VerificationGate → GateOutcome) (kind : String)
    (address : ByteArray) (r : MirrorRender) : Bool :=
  decide (address.size = 32) && decide (r.upgrade = ⟨kind, address⟩) &&
    VerificationGate.all.all (fun g => outcomes g != .failed) &&
    match r.tier with
    | .selfVerifiedLocal => VerificationGate.all.all fun g => outcomes g == .passed
    | .untrustedOriginMirror => decide (r.skipped = skippedGates outcomes)

theorem mem_skippedGates {outcomes : VerificationGate → GateOutcome} {g : VerificationGate} :
    g ∈ skippedGates outcomes ↔ outcomes g = .skipped := by
  simp [skippedGates, VerificationGate.mem_all]

/-- What an admitted classification is. -/
theorem classify_ok {outcomes : VerificationGate → GateOutcome} {kind : String} {address : ByteArray}
    {r : MirrorRender} (h : classifyMirrorRender outcomes kind address = .ok r) :
    address.size = 32 ∧ (∀ g, outcomes g ≠ .failed) ∧ r.upgrade = ⟨kind, address⟩ ∧
    r.skipped = skippedGates outcomes ∧ (r.tier = .selfVerifiedLocal ↔ skippedGates outcomes = []) := by
  unfold classifyMirrorRender at h
  split at h
  · rename_i hsize
    split at h
    · cases h
    · rename_i hfail
      have hnf : ∀ g, outcomes g ≠ .failed := fun g hg => by
        have := List.find?_eq_none.mp hfail g (VerificationGate.mem_all g)
        simp [hg] at this
      split at h
      · rename_i hs
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hsize, hnf, rfl, hs.symm, by simp [hs]⟩
      · rename_i g gs hs
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hsize, hnf, rfl, hs.symm, by simp [hs]⟩
  · cases h

/-- The classifier's badge passes the validator. -/
theorem classify_verifies {outcomes : VerificationGate → GateOutcome} {kind : String}
    {address : ByteArray} {r : MirrorRender}
    (h : classifyMirrorRender outcomes kind address = .ok r) :
    verifyMirrorBadge outcomes kind address r = true := by
  obtain ⟨hsize, hnf, hup, hsk, htier⟩ := classify_ok h
  unfold verifyMirrorBadge
  simp only [hsize, hup, decide_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun g _ => by simpa using hnf g, ?_⟩
  cases ht : r.tier with
  | selfVerifiedLocal =>
    simp only [List.all_eq_true]
    intro g _
    have hnone := htier.mp ht
    have hns : outcomes g ≠ .skipped := fun hg => by
      have := mem_skippedGates.mpr hg
      rw [hnone] at this
      simp at this
    have hnfg := hnf g
    cases hg : outcomes g <;> simp_all
  | untrustedOriginMirror => simpa using hsk

/-- A badge the validator accepts as self-verified: every gate passed on the reader's side. -/
theorem badge_selfVerified_all_passed {outcomes : VerificationGate → GateOutcome} {kind : String}
    {address : ByteArray} {r : MirrorRender} (h : verifyMirrorBadge outcomes kind address r = true)
    (htier : r.tier = .selfVerifiedLocal) (g : VerificationGate) : outcomes g = .passed := by
  unfold verifyMirrorBadge at h
  simp only [htier, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2 g (VerificationGate.mem_all g)

/-- A badge the validator accepts as an untrusted mirror lists exactly the skipped gates and carries
the object's own 32-byte address. -/
theorem badge_untrusted_lists_skipped {outcomes : VerificationGate → GateOutcome} {kind : String}
    {address : ByteArray} {r : MirrorRender} (h : verifyMirrorBadge outcomes kind address r = true)
    (htier : r.tier = .untrustedOriginMirror) :
    r.skipped = skippedGates outcomes ∧ r.upgrade = ⟨kind, address⟩ ∧ address.size = 32 := by
  unfold verifyMirrorBadge at h
  simp only [htier, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.2, h.1.1.2, h.1.1.1⟩

/-- **A render made without running every gate never bears `selfVerifiedLocal`.** Of the
classifier's badge and of any badge the validator accepts: if some gate did not pass on the
reader's side, the tier is `untrustedOriginMirror`. A server's preview, for which the reader ran
nothing, cannot say otherwise. -/
theorem serverMirror_never_claims_selfVerified (outcomes : VerificationGate → GateOutcome)
    (kind : String) (address : ByteArray) (r : MirrorRender) (g : VerificationGate)
    (hnot : outcomes g ≠ .passed) :
    (verifyMirrorBadge outcomes kind address r = true → r.tier = .untrustedOriginMirror) ∧
    (classifyMirrorRender outcomes kind address = .ok r → r.tier = .untrustedOriginMirror) := by
  have hv : verifyMirrorBadge outcomes kind address r = true → r.tier = .untrustedOriginMirror := by
    intro h
    cases ht : r.tier with
    | untrustedOriginMirror => rfl
    | selfVerifiedLocal => exact absurd (badge_selfVerified_all_passed h ht g) hnot
  exact ⟨hv, fun h => hv (classify_verifies h)⟩

/-- **An untrusted mirror reports every skipped gate, verbatim, and where to check instead.** Of the
classifier's badge and of any badge the validator accepts at the untrusted tier: its list is
exactly the gates the reader did not run, in ladder order, none omitted and none invented, and it
carries the object's canonical 32-byte `obend://` address. -/
theorem serverMirror_reports_all_skipped_gates (outcomes : VerificationGate → GateOutcome)
    (kind : String) (address : ByteArray) (r : MirrorRender)
    (h : verifyMirrorBadge outcomes kind address r = true ∨
      classifyMirrorRender outcomes kind address = .ok r)
    (htier : r.tier = .untrustedOriginMirror) :
    r.skipped = skippedGates outcomes ∧ (∀ g, outcomes g = .skipped ↔ g ∈ r.skipped) ∧
    r.upgrade = ⟨kind, address⟩ ∧ address.size = 32 := by
  obtain ⟨hsk, hup, hsize⟩ :=
    badge_untrusted_lists_skipped (h.elim id classify_verifies) htier
  exact ⟨hsk, fun g => by rw [hsk]; exact mem_skippedGates.symm, hup, hsize⟩

/-- The receipt-chain gate: do the headers link from genesis? -/
def chainGate (chain : Option (List ReceiptHeader)) : GateOutcome :=
  .ofCheck (chain.map (linkedFrom genesisDigest 0))

/-- The transclusion gate: is the quote admitted against the chain? -/
def transclusionGate (chain : Option (List ReceiptHeader)) (t : Transclusion) : GateOutcome :=
  .ofCheck (chain.map fun c => match admitTransclusion c t with
    | .ok _ => true
    | .error _ => false)

/-- The confinement gate: does the witness log replay? -/
def confinementGate (log : Option InteractionLog) : GateOutcome := .ofCheck (log.map confined)

/-- A gate with nothing to run on is skipped; it never passes by default. -/
theorem gates_skip_without_evidence (t : Transclusion) :
    chainGate none = .skipped ∧ transclusionGate none t = .skipped ∧
      confinementGate none = .skipped := ⟨rfl, rfl, rfl⟩

/-! ## 5. The premises are inhabited -/

/-- A source that has finalized one turn, and a truthful quote of it. -/
def demoSource : SourceCell := (SourceCell.mk [] []).advance [[("title", [7])]]

example : linkedFrom genesisDigest 0 demoSource.observed = true :=
  advance_linked _ _ rfl

example : ∃ (outcomes : VerificationGate → GateOutcome) (g : VerificationGate),
    outcomes g ≠ .passed := ⟨fun _ => .skipped, .receiptChain, by simp⟩

example : ∃ r, classifyMirrorRender (fun _ => .skipped) "page" genesisDigest = .ok r ∧
    r.tier = .untrustedOriginMirror := ⟨_, rfl, rfl⟩

end Obend.Vault.TransclusionAndMirror

end
