module
/-
Salted transclusion and receipt provenance, verified notebook boundaries, and canonical mirror
badges. Source headers frame predecessor, height and named field commitments. Notebook snips
preserve snapshots for any visible set; edits reuse a boundary only under downstream closure.
Admission checks graph acyclicity as well as every boundary opening. The mirror badge is exactly
the classification of the reader's own gate outcomes, including the ordered skipped-gate list.
-/
public import Obend.Vault.FrustumMembrane
public import Obend.Doc.ReactiveNotebook
import all Obend.Doc.ReactiveNotebook
import all Obend.Vault.FrustumMembrane

public section

namespace Obend.Vault.TransclusionAndMirror

set_option autoImplicit false

open Obend.Vault.Affordance (Auth fireGate)
open Obend.Vault.Rehydration (InteractionLog confined)
open Obend.Vault.FrustumMembrane (utf8 utf8_injective SealedSlot sealCommit sealCommit_size
  sealCommit_binds sealPreimage sealCustomization Frustum CellView Cap Disposition BoundaryPin
  makeFace mem_cut snip_reifies_cut mem_of_lookup)
open Obend.Doc.Reactive
open Obend.Crypto (cshake32ByteArray cshake32ByteArray_size encodeListField
  encodeListField_prefix_inj leb128 leb128_prefix_inj byteArray_eq_of_toList_eq)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.HashBytes (CollisionAmong)
open Obend.Polis (cshake32_binds)

/-! ## 1. Field commitments and receipt digests -/

/-- What a field commitment seals: the field's name and its value, each length-framed. -/
def fieldPreimage (name : String) (value : List UInt8) : List UInt8 :=
  encodeListField (utf8 name) ++ encodeListField value

/-- The sealed slot a field commits: its framed name and value as the secret, under the salt of the
slot `o` its owner holds (`o.secret` the value's bytes, `o.salt` the field's salt). -/
def fieldSlot (name : String) (o : SealedSlot) : SealedSlot :=
  ⟨fieldPreimage name o.secret, o.salt⟩

/-- **The 32-byte commitment of one finalized field: the membrane's seal of its slot.** -/
def fieldCommit (name : String) (o : SealedSlot) : ByteArray := sealCommit (fieldSlot name o)

theorem fieldPreimage_injective {n₁ n₂ : String} {v₁ v₂ : List UInt8}
    (h : fieldPreimage n₁ v₁ = fieldPreimage n₂ v₂) : n₁ = n₂ ∧ v₁ = v₂ := by
  unfold fieldPreimage at h
  obtain ⟨hn, h⟩ := encodeListField_prefix_inj h
  obtain ⟨hv, _⟩ := encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)
  exact ⟨utf8_injective hn, hv⟩

theorem fieldSlot_injective {n₁ n₂ : String} {o₁ o₂ : SealedSlot}
    (h : fieldSlot n₁ o₁ = fieldSlot n₂ o₂) : n₁ = n₂ ∧ o₁ = o₂ := by
  simp only [fieldSlot, SealedSlot.mk.injEq] at h
  obtain ⟨hn, hv⟩ := fieldPreimage_injective h.1
  have hs := h.2
  cases o₁
  cases o₂
  simp_all

theorem fieldCommit_size (name : String) (o : SealedSlot) : (fieldCommit name o).size = 32 :=
  sealCommit_size _

/-- **Salted binding.** Equal commitments seal the same name, the same bytes and the same salt, or
the two sealed slots collide under the seal hash. -/
theorem fieldCommit_binds {n₁ n₂ : String} {o₁ o₂ : SealedSlot}
    (h : fieldCommit n₁ o₁ = fieldCommit n₂ o₂) :
    (n₁ = n₂ ∧ o₁ = o₂) ∨ CollisionAmong (cshake256Bytes sealCustomization)
      (fun x => x = sealPreimage (fieldSlot n₁ o₁) ∨ x = sealPreimage (fieldSlot n₂ o₂)) :=
  (sealCommit_binds h).imp fieldSlot_injective id

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

/-- A finalized turn as its source holds it: each field's bytes and its salt. -/
structure Receipt where
  prev : ByteArray
  height : Nat
  fields : List (String × SealedSlot)
deriving DecidableEq

def Receipt.header (r : Receipt) : ReceiptHeader :=
  { prev := r.prev, height := r.height, commits := r.fields.map fun e => (e.1, fieldCommit e.1 e.2) }

/-- A source cell: its finalized receipts, oldest first, and what it has staged and not finalized. -/
structure SourceCell where
  finalized : List Receipt
  draft : List (String × SealedSlot)

/-- The predecessor digest of the first receipt: thirty-two zero bytes. -/
def genesisDigest : ByteArray := ⟨Array.replicate 32 0⟩

/-- The digest of the last header of a chain. -/
def headDigest (chain : List ReceiptHeader) : ByteArray :=
  match chain.getLast? with
  | some h => receiptDigest h
  | none => genesisDigest

/-- What a reader holds of the source: the headers of its finalized receipts. -/
def SourceCell.observed (s : SourceCell) : List ReceiptHeader := s.finalized.map Receipt.header

def SourceCell.stage (s : SourceCell) (fields : List (String × SealedSlot)) : SourceCell :=
  { s with draft := fields }

/-- Finalize the staged fields as the next receipt. -/
def SourceCell.finalize (s : SourceCell) : SourceCell :=
  { finalized := s.finalized ++ [⟨headDigest s.observed, s.finalized.length, s.draft⟩], draft := [] }

/-- The source takes further turns, each staged and finalized. -/
def SourceCell.advance (s : SourceCell) (turns : List (List (String × SealedSlot))) : SourceCell :=
  turns.foldl (fun s fields => (s.stage fields).finalize) s

/-- The past is a prefix of the future: advancing appends one receipt per turn and alters none. -/
theorem advance_finalized (turns : List (List (String × SealedSlot))) : ∀ s : SourceCell,
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
theorem advance_linked (turns : List (List (String × SealedSlot))) : ∀ s : SourceCell,
    linkedFrom genesisDigest 0 s.observed = true →
    linkedFrom genesisDigest 0 (s.advance turns).observed = true := by
  induction turns with
  | nil => intro s h; exact h
  | cons t ts ih => intro s h; exact ih _ (finalize_linked (s.stage t) h)

/-! ## 3. Transclusion -/

/-- A quote of one field of a cited receipt: the opening carries the quoted bytes and the salt. -/
structure Transclusion where
  cited : ByteArray
  height : Nat
  field : String
  opening : SealedSlot
deriving DecidableEq

/-- Why a transclusion was not admitted. -/
inductive TransclusionRefusal where
  | uncitedReceipt
  | heightMismatch (found : Nat)
  | fieldAbsent
  | saltWidth (found : Nat)
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

/-- **Check one opening against the commitments a reader holds**: `none` when it is admitted. A salt
that is not 256 bits is refused before any commitment is compared; an opening is admitted only if
sealing it under its own salt gives the committed bytes. -/
def openingRefusal (commits : List (String × ByteArray)) (field : String) (o : SealedSlot) :
    Option TransclusionRefusal :=
  match commits.lookup field with
  | none => some .fieldAbsent
  | some c =>
    if o.salt.length = 32 then
      if fieldCommit field o = c then none else some .digestMismatch
    else some (.saltWidth o.salt.length)

theorem openingRefusal_none {commits : List (String × ByteArray)} {field : String} {o : SealedSlot} :
    openingRefusal commits field o = none ↔
      commits.lookup field = some (fieldCommit field o) ∧ o.salt.length = 32 := by
  unfold openingRefusal
  cases hl : commits.lookup field with
  | none => simp
  | some c =>
    by_cases hs : o.salt.length = 32
    · by_cases hc : fieldCommit field o = c
      · simp [hs, hc]
      · have hc' : ¬ c = fieldCommit field o := fun h => hc h.symm
        simp [hs, hc, hc']
    · simp [hs]

/-- **Admit a transclusion against the headers a reader holds**, or say why not. The opening is
compared by commitment with what the cited receipt committed. -/
def admitTransclusion (chain : List ReceiptHeader) (t : Transclusion) :
    Except TransclusionRefusal DatedQuote :=
  match chain.find? (fun h => decide (receiptDigest h = t.cited)) with
  | none => .error .uncitedReceipt
  | some h =>
    if h.height = t.height then
      match openingRefusal h.commits t.field t.opening with
      | some why => .error why
      | none => .ok ⟨t.opening.secret, t.height, chain.length - 1⟩
    else .error (.heightMismatch h.height)

/-- What an admission found. -/
theorem admit_ok {chain : List ReceiptHeader} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion chain t = .ok d) :
    ∃ hd, chain.find? (fun h => decide (receiptDigest h = t.cited)) = some hd ∧
      hd.height = t.height ∧ hd.commits.lookup t.field = some (fieldCommit t.field t.opening) ∧
      t.opening.salt.length = 32 ∧ d = ⟨t.opening.secret, t.height, chain.length - 1⟩ := by
  unfold admitTransclusion at h
  split at h
  · cases h
  · rename_i hd hfind
    split at h
    · rename_i hh
      split at h
      · cases h
      · rename_i hnone
        simp only [Except.ok.injEq] at h
        obtain ⟨hc, hs⟩ := openingRefusal_none.mp hnone
        exact ⟨hd, hfind, hh, hc, hs, h.symm⟩
    · cases h

/-- A citation found, at its height, with its field committed to the opening under a 256-bit salt,
is admitted. -/
theorem admit_of_find {chain : List ReceiptHeader} {t : Transclusion} {hd : ReceiptHeader}
    (hfind : chain.find? (fun h => decide (receiptDigest h = t.cited)) = some hd)
    (hh : hd.height = t.height)
    (hc : hd.commits.lookup t.field = some (fieldCommit t.field t.opening))
    (hs : t.opening.salt.length = 32) :
    admitTransclusion chain t = .ok ⟨t.opening.secret, t.height, chain.length - 1⟩ := by
  unfold admitTransclusion
  rw [hfind]
  simp [hh, openingRefusal_none.mpr ⟨hc, hs⟩]

theorem lookup_commits (k : String) : ∀ fields : List (String × SealedSlot),
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
      (r.fields.lookup t.field).map (fieldCommit t.field) = some (fieldCommit t.field t.opening)) ∧
    ∀ staged, admitTransclusion (s.stage staged).observed t = .ok d := by
  obtain ⟨hd, hfind, hh, hc, _⟩ := admit_ok h
  refine ⟨?_, fun _ => h⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
  have hdig := List.find?_some hfind
  refine ⟨r, hr, by simpa using hdig, hh, ?_⟩
  rw [← lookup_commits]
  exact hc

/-- **Provenance is faithful.** Let `r₀` be a finalized receipt with the cited digest, holding the
slot `v` in the quoted field. Then an admitted opening is `v`, bytes and salt; or two receipts of
the observed chain collide under the receipt hash; or the opening and `v` collide under the seal
hash. -/
theorem transclusion_provenance_faithful {s : SourceCell} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion s.observed t = .ok d) {r₀ : Receipt} (hr₀ : r₀ ∈ s.finalized)
    (hcite : receiptDigest r₀.header = t.cited) {v : SealedSlot}
    (hv : r₀.fields.lookup t.field = some v) :
    d.quote = t.opening.secret ∧
    (t.opening = v ∨
      CollisionAmong (cshake256Bytes receiptCustomization)
        (fun x => ∃ hd, hd ∈ s.observed ∧ x = receiptPreimage hd) ∨
      CollisionAmong (cshake256Bytes sealCustomization)
        (fun x => x = sealPreimage (fieldSlot t.field t.opening) ∨
          x = sealPreimage (fieldSlot t.field v))) := by
  obtain ⟨hd, hfind, _, hc, _, rfl⟩ := admit_ok h
  refine ⟨rfl, ?_⟩
  have hmem : hd ∈ s.observed := List.mem_of_find?_eq_some hfind
  have hdig : receiptDigest hd = receiptDigest r₀.header := by
    have := List.find?_some hfind
    rw [hcite]
    simpa using this
  rcases receiptDigest_binds hdig with heq | hcol
  · subst heq
    have hc' : (r₀.fields.lookup t.field).map (fieldCommit t.field) =
        some (fieldCommit t.field t.opening) := by
      rw [← lookup_commits]; exact hc
    rw [hv] at hc'
    simp only [Option.map_some, Option.some.injEq] at hc'
    rcases fieldCommit_binds hc'.symm with hq | hcol
    · exact .inl hq.2
    · exact .inr (.inr hcol)
  · refine .inr (.inl (hcol.mono fun x hx => ?_))
    rcases hx with rfl | rfl
    · exact ⟨hd, hmem, rfl⟩
    · exact ⟨r₀.header, List.mem_map.mpr ⟨r₀, hr₀, rfl⟩, rfl⟩

/-- What the opening check answers beside an admitted transclusion of the same citation and field. -/
theorem forged_refusal {chain : List ReceiptHeader} {t forged : Transclusion} {d : DatedQuote}
    (h : admitTransclusion chain t = .ok d) (hcited : forged.cited = t.cited)
    (hheight : forged.height = t.height) (hfield : forged.field = t.field)
    {why : TransclusionRefusal}
    (hwhy : (if forged.opening.salt.length = 32 then
        if fieldCommit t.field forged.opening = fieldCommit t.field t.opening then none
        else some TransclusionRefusal.digestMismatch
      else some (.saltWidth forged.opening.salt.length)) = some why) :
    admitTransclusion chain forged = .error why := by
  obtain ⟨hd, hfind, hh, hc, _, _⟩ := admit_ok h
  have href : openingRefusal hd.commits forged.field forged.opening = some why := by
    unfold openingRefusal
    rw [hfield, hc]
    exact hwhy
  unfold admitTransclusion
  rw [hcited, hfind]
  simp [hheight, hh, href]

/-- **A forged quote is refused.** Beside an admitted transclusion, one with the same citation and
field, a 256-bit salt and a different commitment is refused, and the refusal is `digestMismatch`. -/
theorem transclusion_forge_refused {chain : List ReceiptHeader} {t forged : Transclusion}
    {d : DatedQuote} (h : admitTransclusion chain t = .ok d)
    (hcited : forged.cited = t.cited) (hheight : forged.height = t.height)
    (hfield : forged.field = t.field) (hsalt : forged.opening.salt.length = 32)
    (hdigest : fieldCommit forged.field forged.opening ≠ fieldCommit t.field t.opening) :
    admitTransclusion chain forged = .error .digestMismatch := by
  rw [hfield] at hdigest
  exact forged_refusal h hcited hheight hfield (by simp [hsalt, hdigest])

/-- **An unsalted opening is never admitted.** Whatever chain it is checked against, a transclusion
whose salt is not 256 bits is refused: no guessable, saltless opening passes. -/
theorem transclusion_unsalted_refused (chain : List ReceiptHeader) (t : Transclusion)
    (hsalt : t.opening.salt.length ≠ 32) (d : DatedQuote) : admitTransclusion chain t ≠ .ok d :=
  fun h => by
    obtain ⟨_, _, _, _, hs, _⟩ := admit_ok h
    exact hsalt hs

/-- **A lying opening is refused, or it is a collision.** Beside an admitted transclusion, one of
the same citation and field whose opening differs, in its bytes or in its salt, is refused, with
`digestMismatch` or, if its salt is not 256 bits, with `saltWidth`; unless the two sealed slots
collide under the seal hash. -/
theorem transclusion_lying_opening_refused_or_collides {chain : List ReceiptHeader}
    {t forged : Transclusion} {d : DatedQuote} (h : admitTransclusion chain t = .ok d)
    (hcited : forged.cited = t.cited) (hheight : forged.height = t.height)
    (hfield : forged.field = t.field) (hlie : forged.opening ≠ t.opening) :
    admitTransclusion chain forged = .error .digestMismatch ∨
    (forged.opening.salt.length ≠ 32 ∧
      admitTransclusion chain forged = .error (.saltWidth forged.opening.salt.length)) ∨
    CollisionAmong (cshake256Bytes sealCustomization)
      (fun x => x = sealPreimage (fieldSlot t.field forged.opening) ∨
        x = sealPreimage (fieldSlot t.field t.opening)) := by
  by_cases hsalt : forged.opening.salt.length = 32
  · by_cases hdig : fieldCommit t.field forged.opening = fieldCommit t.field t.opening
    · rcases fieldCommit_binds hdig with hq | hcol
      · exact absurd hq.2 hlie
      · exact .inr (.inr hcol)
    · exact .inl (forged_refusal h hcited hheight hfield (by simp [hsalt, hdig]))
  · exact .inr (.inl ⟨hsalt, forged_refusal h hcited hheight hfield (by simp [hsalt])⟩)

/-- **Salt separation.** Beside an admitted transclusion, an opening of the same citation and field
under any other 256-bit salt, whatever bytes it claims, is refused with `digestMismatch`, unless the
two sealed slots collide under the seal hash. -/
theorem transclusion_wrong_salt_refused_or_collides {chain : List ReceiptHeader}
    {t forged : Transclusion} {d : DatedQuote} (h : admitTransclusion chain t = .ok d)
    (hcited : forged.cited = t.cited) (hheight : forged.height = t.height)
    (hfield : forged.field = t.field) (hwidth : forged.opening.salt.length = 32)
    (hsalt : forged.opening.salt ≠ t.opening.salt) :
    admitTransclusion chain forged = .error .digestMismatch ∨
    CollisionAmong (cshake256Bytes sealCustomization)
      (fun x => x = sealPreimage (fieldSlot t.field forged.opening) ∨
        x = sealPreimage (fieldSlot t.field t.opening)) := by
  by_cases hdig : fieldCommit t.field forged.opening = fieldCommit t.field t.opening
  · rcases fieldCommit_binds hdig with hq | hcol
    · exact absurd (congrArg SealedSlot.salt hq.2) hsalt
    · exact .inr hcol
  · exact .inl (forged_refusal h hcited hheight hfield (by simp [hwidth, hdig]))

/-- **A citation survives the source's future.** After the source finalizes any further turns, an
admitted transclusion is admitted again with the same bytes at the same cited height, dated against
the new head; on a linked chain its staleness has grown by exactly the number of turns, and is in
the result. The cited receipt itself is still in the chain, unaltered (`advance_finalized`). -/
theorem transclusion_stable_under_source_advance {s : SourceCell} {t : Transclusion} {d : DatedQuote}
    (h : admitTransclusion s.observed t = .ok d) (turns : List (List (String × SealedSlot))) :
    admitTransclusion (s.advance turns).observed t =
      .ok { d with headHeight := d.headHeight + turns.length } ∧
    (linkedFrom genesisDigest 0 s.observed = true →
      ({ d with headHeight := d.headHeight + turns.length } : DatedQuote).staleness =
        d.staleness + turns.length) := by
  obtain ⟨hd, hfind, hh, hc, hs, rfl⟩ := admit_ok h
  obtain ⟨more, hmore, hlen⟩ := advance_finalized turns s
  have hobs : (s.advance turns).observed = s.observed ++ more.map Receipt.header := by
    simp [SourceCell.observed, hmore]
  have hmem : hd ∈ s.observed := List.mem_of_find?_eq_some hfind
  have hpos : 0 < s.observed.length := List.length_pos_of_mem hmem
  have hfind' : (s.advance turns).observed.find? (fun h => decide (receiptDigest h = t.cited)) =
      some hd := by rw [hobs, List.find?_append, hfind]; rfl
  have hlen' : (s.advance turns).observed.length - 1 = s.observed.length - 1 + turns.length := by
    rw [hobs, List.length_append, List.length_map, hlen]; omega
  refine ⟨by rw [admit_of_find hfind' hh hc hs, hlen'], fun hlinked => ?_⟩
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
  | write (fields : List (String × SealedSlot))
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

/-! ## 4. A frustum of a notebook

A viewer holds the cells of a reactive notebook whose ids are in `V`, in schedule order, and in
place of the redacted cells an environment for the symbols its own cells read. First the evaluation
(`snip_preserves_evaluation`, `snip_edit_preserves_receipts`), for any environment that is right at
the boundary; then the boundary sealed as field commitments, which is how a viewer knows its
environment is right; then the same cut made by `Frustum.snip` in a membrane world. -/

/-- The value a cached cell publishes for a symbol. -/
def published (x : CachedCell) (s : SymbolName) : Int :=
  x.result.values[x.cell.defs.idxOf s]?.getD 0

/-- The symbols the redacted cells publish. -/
def boundarySymbols (redacted : List CachedCell) : List SymbolName :=
  redacted.flatMap fun x => x.cell.defs

/-- What the redacted cells publish for a symbol; zero if none of them exports it. -/
def boundaryValue (redacted : List CachedCell) (s : SymbolName) : Int :=
  match redacted.find? (fun x => x.cell.defs.contains s) with
  | some x => published x s
  | none => 0

/-- An environment that is right at the boundary: on every symbol a visible cell reads, it holds
what the redacted cells published. -/
def BoundaryAgrees (visible : List ReactiveCell) (redacted : List CachedCell)
    (env : Doc.Reactive.Environment) : Prop :=
  ∀ c ∈ visible, ∀ s ∈ c.reads, env s = boundaryValue redacted s

theorem boundaryValue_absent {redacted : List CachedCell} {s : SymbolName}
    (h : s ∉ boundarySymbols redacted) : boundaryValue redacted s = 0 := by
  unfold boundaryValue
  cases hf : redacted.find? (fun x => x.cell.defs.contains s) with
  | none => rfl
  | some x =>
    have hx := List.find?_some hf
    exact absurd (List.mem_flatMap.mpr ⟨x, List.mem_of_find?_eq_some hf, by simpa using hx⟩) h

/-- The viewer's sweep and the whole notebook's, side by side. On the symbols `W` the visible cells
read, the viewer's environment holds the whole notebook's wherever no pending redacted cell exports
the symbol, and already holds what that cell is going to publish where one does. -/
theorem snip_schedule (k : CellKernel) (V : List CellId) (W : SymbolName → Prop)
    (cs : List ReactiveCell) (envF envS : Doc.Reactive.Environment)
    (hp : cs.Pairwise (fun a b => a.id < b.id)) (hn : (cs.flatMap ReactiveCell.defs).Nodup)
    (he : ∀ p ∈ cs, ∀ u ∈ cs, dependency p u → p.id < u.id)
    (hW : ∀ c ∈ cs, c.id ∈ V → ∀ s ∈ c.reads, W s)
    (hinv : ∀ s, W s → envS s =
      if s ∈ boundarySymbols (redactCache V (evalSchedule k cs envF)) then
        boundaryValue (redactCache V (evalSchedule k cs envF)) s
      else envF s) :
    snipCache V (evalSchedule k cs envF) = evalSchedule k (snipCells V cs) envS := by
  induction cs generalizing envF envS with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨hhead, hp'⟩ := List.pairwise_cons.mp hp
    rw [List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨_, hn', hdisj⟩ := hn
    have he' : ∀ p ∈ cs, ∀ u ∈ cs, dependency p u → p.id < u.id :=
      fun p hp u hu => he p (.tail _ hp) u (.tail _ hu)
    have hW' : ∀ d ∈ cs, d.id ∈ V → ∀ s ∈ d.reads, W s := fun d hd => hW d (.tail _ hd)
    have hpending : ∀ (env : Doc.Reactive.Environment) (s : SymbolName),
        s ∈ boundarySymbols (redactCache V (evalSchedule k cs env)) → s ∉ c.defs := by
      intro env s hmem hsc
      obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.mp hmem
      exact hdisj s hsc s (List.mem_flatMap.mpr ⟨x.cell, redactCache_cell_mem hx, hsx⟩) rfl
    by_cases hv : c.id ∈ V
    · have hred : redactCache V (evalSchedule k (c :: cs) envF) =
          redactCache V (evalSchedule k cs (publish c (evalCell k c envF) envF)) := by
        simp [redactCache, evalSchedule, hv]
      have hreads : ∀ s ∈ c.reads, envF s = envS s := by
        intro s hs
        have hi := hinv s (hW c (.head _) hv s hs)
        rw [hred] at hi
        have hnot : s ∉ boundarySymbols
            (redactCache V (evalSchedule k cs (publish c (evalCell k c envF) envF))) := by
          intro hmem
          obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.mp hmem
          have hcell : x.cell ∈ cs := redactCache_cell_mem hx
          exact Nat.lt_asymm (hhead x.cell hcell)
            (he x.cell (.tail _ hcell) c (.head _) ⟨s, hsx, hs⟩)
        simp only [hnot, ↓reduceIte] at hi
        exact hi.symm
      have hr : evalCell k c envF = evalCell k c envS := evalCell_frame k c envF envS hreads
      have hstep : snipCache V (evalSchedule k (c :: cs) envF) =
          ⟨c, evalCell k c envS⟩ ::
            snipCache V (evalSchedule k cs (publish c (evalCell k c envS) envF)) := by
        simp [snipCache, evalSchedule, hr, hv]
      have hstep' : evalSchedule k (snipCells V (c :: cs)) envS =
          ⟨c, evalCell k c envS⟩ ::
            evalSchedule k (snipCells V cs) (publish c (evalCell k c envS) envS) := by
        simp [snipCells, evalSchedule, hv]
      rw [hstep, hstep']
      congr 1
      apply ih _ _ hp' hn' he' hW'
      intro s hs
      have hi := hinv s hs
      rw [hred, hr] at hi
      by_cases hmem : s ∈ boundarySymbols
          (redactCache V (evalSchedule k cs (publish c (evalCell k c envS) envF)))
      · simp only [hmem, ↓reduceIte] at hi ⊢
        have hsc := hpending _ s hmem
        simp only [publish, hsc, ↓reduceIte]
        exact hi
      · simp only [hmem, ↓reduceIte] at hi ⊢
        by_cases hsc : s ∈ c.defs <;> simp [publish, hsc, hi]
    · have hstep : snipCache V (evalSchedule k (c :: cs) envF) =
          snipCache V (evalSchedule k cs (publish c (evalCell k c envF) envF)) := by
        simp [snipCache, evalSchedule, hv]
      have hstep' : snipCells V (c :: cs) = snipCells V cs := by simp [snipCells, hv]
      have hred : redactCache V (evalSchedule k (c :: cs) envF) =
          ⟨c, evalCell k c envF⟩ ::
            redactCache V (evalSchedule k cs (publish c (evalCell k c envF) envF)) := by
        simp [redactCache, evalSchedule, hv]
      rw [hstep, hstep']
      apply ih _ _ hp' hn' he' hW'
      intro s hs
      have hi := hinv s hs
      rw [hred] at hi
      rw [hi]
      have hcons : ∀ R' : List CachedCell, s ∈ boundarySymbols (⟨c, evalCell k c envF⟩ :: R') ↔
          (s ∈ c.defs ∨ s ∈ boundarySymbols R') := by
        intro R'
        simp [boundarySymbols]
      by_cases hsc : s ∈ c.defs
      · have hnot : s ∉ boundarySymbols
            (redactCache V (evalSchedule k cs (publish c (evalCell k c envF) envF))) :=
          fun hmem => hpending _ s hmem hsc
        simp [hcons, hsc, hnot, boundaryValue, published, publish]
      · by_cases hmem : s ∈ boundarySymbols
            (redactCache V (evalSchedule k cs (publish c (evalCell k c envF) envF)))
        · simp [hcons, hsc, hmem, boundaryValue]
        · simp [hcons, hsc, hmem, publish]

/-- **Snipping preserves evaluation.** On an admitted notebook, a viewer who holds the cells of `V`
and an environment that is right at the boundary computes, for each of its cells, the cached result
the whole notebook computes: the same values and the same 256-bit receipt. -/
theorem snip_preserves_evaluation (k : CellKernel) (V : List CellId) (cs : List ReactiveCell)
    (env : Doc.Reactive.Environment) (hdag : checkNotebookDag cs = true)
    (hb : BoundaryAgrees (snipCells V cs) (redactCache V (evalFromScratch k cs).cells) env) :
    evalSchedule k (snipCells V cs) env = snipCache V (evalFromScratch k cs).cells := by
  have hc := hdag
  simp only [checkNotebookDag, uniqueExports, scheduleCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hc
  have hb' : BoundaryAgrees (snipCells V cs) (redactCache V (evalSchedule k cs fun _ => 0)) env := hb
  show _ = snipCache V (evalSchedule k cs fun _ => 0)
  refine (snip_schedule k V (fun s => ∃ c ∈ snipCells V cs, s ∈ c.reads) cs (fun _ => 0) env
    hc.2.1 hc.1 hc.2.2 ?_ ?_).symm
  · intro c hcm hv s hs
    exact ⟨c, List.mem_filter.mpr ⟨hcm, by simpa using hv⟩, hs⟩
  · rintro s ⟨c, hcm, hs⟩
    rw [hb' c hcm s hs]
    split
    · rfl
    · rename_i h
      exact boundaryValue_absent h

/-- **A visible edit recomputes the same receipts in the snipped notebook, against the same
boundary.** When the visible set is closed downstream, an edit to a visible cell leaves every
redacted cached cell as it was, so the boundary the viewer holds is still the boundary; and the
viewer's incremental recompute over its own cells, from its boundary environment, yields exactly
the visible part of the whole notebook's recompute. -/
theorem snip_edit_preserves_receipts (k : CellKernel) (V : List CellId) (cs : List ReactiveCell)
    (env : Doc.Reactive.Environment) (a : NotebookAction) (hdag : checkNotebookDag cs = true)
    (hclosed : frustumClosed V cs = true) (ht : a.target ∈ V)
    (hb : BoundaryAgrees (snipCells V cs) (redactCache V (evalFromScratch k cs).cells) env) :
    redactCache V (editCellAndRecompute k (evalFromScratch k cs) a).cells =
      redactCache V (evalFromScratch k cs).cells ∧
    recompute k a (snipCache V (evalFromScratch k cs).cells) env [] =
      snipCache V (editCellAndRecompute k (evalFromScratch k cs) a).cells := by
  have hred : redactCache V (evalFromScratch k (applyEdit a cs)).cells =
      redactCache V (evalFromScratch k cs).cells :=
    redact_schedule_edit k V a ht cs _ _ [] (of_decide_eq_true hclosed)
      (fun _ _ _ _ _ => List.not_mem_nil) (fun _ _ => rfl)
  have hcomm : applyEdit a (snipCells V cs) = snipCells V (applyEdit a cs) := by
    simp only [applyEdit, snipCells, List.filter_map, Function.comp_def, editCell_id]
  rw [incrementalRecompute_eq_fromScratch]
  refine ⟨hred, ?_⟩
  rw [← snip_preserves_evaluation k V cs env hdag hb,
    recompute_eq_schedule k a _ env env [] (fun _ _ => rfl), hcomm]
  apply snip_preserves_evaluation k V _ env (by rw [checkNotebookDag_edit]; exact hdag)
  intro c hc s hs
  rw [← hcomm] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  rw [editCell_reads] at hs
  rw [hb c₀ hc₀ s hs]
  exact congrArg (fun R => boundaryValue R s) hred.symm

/-! ### The boundary, sealed

The owner seals what each redacted cell publishes as a field commitment under that symbol's own
256-bit salt. The viewer holds the commitments, and openings for the symbols its cells read. -/

/-- One boundary symbol opened to a viewer: its value and its salt. -/
structure BoundaryOpening where
  symbol : String
  value : Int
  salt : List UInt8
deriving DecidableEq, Repr

/-- The slot an opening claims: the framed value under the salt. -/
def BoundaryOpening.slot (o : BoundaryOpening) : SealedSlot := ⟨frameInt o.value, o.salt⟩

/-- The slot the owner holds for a boundary symbol. -/
def ownerSlot (salt : String → List UInt8) (redacted : List CachedCell) (s : String) : SealedSlot :=
  ⟨frameInt (boundaryValue redacted s), salt s⟩

/-- **The sealed boundary**: the field commitment of every symbol a redacted cell publishes. -/
def sealedBoundary (salt : String → List UInt8) (redacted : List CachedCell) :
    List (String × ByteArray) :=
  (boundarySymbols redacted).map fun s => (s, fieldCommit s (ownerSlot salt redacted s))

/-- What a viewer holds of a notebook: its cells, the sealed boundary, and openings. -/
structure NotebookSnip where
  cells : List ReactiveCell
  boundary : List (String × ByteArray)
  openings : List BoundaryOpening

/-- The environment the openings give: the first opening of a symbol; zero where there is none. -/
def snipEnv (openings : List BoundaryOpening) : Doc.Reactive.Environment :=
  fun s => match openings.find? (fun o => o.symbol == s) with
    | some o => o.value
    | none => 0

/-- Why a snipped notebook was not evaluated. -/
inductive SnipRefusal where
  | opening (symbol : String) (why : TransclusionRefusal)
  | unopened (symbol : String)
  | invalidDag
deriving DecidableEq, Repr

/-- **Evaluate a snipped notebook**, or say why not. Every opening is checked against the boundary
as a transclusion's is against a receipt; every symbol a cell reads that the boundary commits must
be opened. -/
def evalSnip (k : CellKernel) (n : NotebookSnip) : Except SnipRefusal (List CachedCell) :=
  if checkNotebookDag n.cells = false then .error .invalidDag else
  match n.openings.findSome? (fun o =>
      (openingRefusal n.boundary o.symbol o.slot).map (SnipRefusal.opening o.symbol)) with
  | some why => .error why
  | none =>
    match (n.cells.flatMap fun c => c.reads).find? (fun s =>
        (n.boundary.lookup s).isSome && !n.openings.any (fun o => o.symbol == s)) with
    | some s => .error (.unopened s)
    | none => .ok (evalSchedule k n.cells (snipEnv n.openings))

/-- A malformed or cyclic snip is refused before any boundary or kernel work. -/
theorem evalSnip_refuses_invalidDag (k : CellKernel) (n : NotebookSnip)
    (h : checkNotebookDag n.cells = false) : evalSnip k n = .error .invalidDag := by
  simp only [evalSnip, h, ite_true]

/-- **Snip a notebook for a viewer of `V`**: the visible cells, the sealed boundary of the redacted
ones, and openings of exactly the boundary symbols the visible cells read. -/
def snipNotebook (k : CellKernel) (salt : String → List UInt8) (V : List CellId)
    (cs : List ReactiveCell) : NotebookSnip :=
  { cells := snipCells V cs,
    boundary := sealedBoundary salt (redactCache V (evalFromScratch k cs).cells),
    openings := ((boundarySymbols (redactCache V (evalFromScratch k cs).cells)).filter fun s =>
        (snipCells V cs).any fun c => c.reads.contains s).map fun s =>
      ⟨s, boundaryValue (redactCache V (evalFromScratch k cs).cells) s, salt s⟩ }

theorem lookup_keyed {β : Type} (g : String → β) (s : String) : ∀ keys : List String,
    (keys.map fun k => (k, g k)).lookup s = if s ∈ keys then some (g s) else none
  | [] => by simp
  | k :: rest => by
    by_cases hk : s = k
    · subst hk
      simp
    · have hne : (s == k) = false := by simpa using hk
      simp only [List.map_cons, List.lookup, hne, List.mem_cons, hk, false_or]
      exact lookup_keyed g s rest

theorem lookup_sealedBoundary (salt : String → List UInt8) (redacted : List CachedCell) (s : String) :
    (sealedBoundary salt redacted).lookup s =
      if s ∈ boundarySymbols redacted then some (fieldCommit s (ownerSlot salt redacted s))
      else none :=
  lookup_keyed (fun s => fieldCommit s (ownerSlot salt redacted s)) s _

/-- What an admitted snip checked. -/
theorem evalSnip_ok {k : CellKernel} {n : NotebookSnip} {out : List CachedCell}
    (h : evalSnip k n = .ok out) :
    (∀ o ∈ n.openings, n.boundary.lookup o.symbol = some (fieldCommit o.symbol o.slot) ∧
      o.salt.length = 32) ∧
    (∀ c ∈ n.cells, ∀ s ∈ c.reads, (n.boundary.lookup s).isSome = true →
      ∃ o ∈ n.openings, o.symbol = s) ∧
    out = evalSchedule k n.cells (snipEnv n.openings) := by
  unfold evalSnip at h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i hbad
    split at h
    · cases h
    · rename_i hcov
      simp only [Except.ok.injEq] at h
      refine ⟨fun o ho => ?_, fun c hc s hs hb => ?_, h.symm⟩
      · have hnone := List.findSome?_eq_none_iff.mp hbad o ho
        exact openingRefusal_none.mp (by simpa using hnone)
      · have hno : ¬ ((n.boundary.lookup s).isSome &&
            !n.openings.any (fun o => o.symbol == s)) = true :=
          List.find?_eq_none.mp hcov s (List.mem_flatMap.mpr ⟨c, hc, hs⟩)
        cases ha : n.openings.any (fun o => o.symbol == s) with
        | true =>
          obtain ⟨o, ho, hos⟩ := List.any_eq_true.mp ha
          exact ⟨o, ho, by simpa using hos⟩
        | false =>
          rw [hb, ha] at hno
          exact absurd rfl hno

/-- A snip whose openings verify and cover its reads is evaluated. -/
theorem evalSnip_of_checks {k : CellKernel} {n : NotebookSnip}
    (hdag : checkNotebookDag n.cells = true)
    (hopen : ∀ o ∈ n.openings, n.boundary.lookup o.symbol = some (fieldCommit o.symbol o.slot) ∧
      o.salt.length = 32)
    (hcov : ∀ c ∈ n.cells, ∀ s ∈ c.reads, (n.boundary.lookup s).isSome = true →
      ∃ o ∈ n.openings, o.symbol = s) :
    evalSnip k n = .ok (evalSchedule k n.cells (snipEnv n.openings)) := by
  have h₁ : n.openings.findSome? (fun o =>
      (openingRefusal n.boundary o.symbol o.slot).map (SnipRefusal.opening o.symbol)) = none :=
    List.findSome?_eq_none_iff.mpr fun o ho => by
      have hnone : openingRefusal n.boundary o.symbol o.slot = none :=
        openingRefusal_none.mpr (hopen o ho)
      simp [hnone]
  have h₂ : (n.cells.flatMap fun c => c.reads).find? (fun s =>
      (n.boundary.lookup s).isSome && !n.openings.any (fun o => o.symbol == s)) = none :=
    List.find?_eq_none.mpr fun s hs hbad => by
      obtain ⟨c, hc, hsc⟩ := List.mem_flatMap.mp hs
      have hbad' : ((n.boundary.lookup s).isSome &&
          !n.openings.any (fun o => o.symbol == s)) = true := hbad
      rw [Bool.and_eq_true] at hbad'
      obtain ⟨o, ho, hos⟩ := hcov c hc s hsc hbad'.1
      have hany : n.openings.any (fun o => o.symbol == s) = true :=
        List.any_eq_true.mpr ⟨o, ho, by simp [hos]⟩
      rw [hany] at hbad'
      exact absurd hbad'.2 (by decide)
  unfold evalSnip
  simp only [hdag, Bool.true_eq_false, ite_false, h₁, h₂]

/-- The seal preimages a boundary check compares: the owner's slots and the supplied openings. -/
def boundaryPreimages (salt : String → List UInt8) (redacted : List CachedCell)
    (openings : List BoundaryOpening) : List UInt8 → Prop :=
  fun x => (∃ s ∈ boundarySymbols redacted,
      x = sealPreimage (fieldSlot s (ownerSlot salt redacted s))) ∨
    (∃ o ∈ openings, x = sealPreimage (fieldSlot o.symbol o.slot))

/-- Openings that verify against the sealed boundary are the owner's slots, or two sealed slots
collide. -/
theorem openings_owned_or_collide (salt : String → List UInt8) (redacted : List CachedCell)
    (openings : List BoundaryOpening)
    (hopen : ∀ o ∈ openings,
      (sealedBoundary salt redacted).lookup o.symbol = some (fieldCommit o.symbol o.slot)) :
    (∀ o ∈ openings, o.symbol ∈ boundarySymbols redacted ∧
      o.slot = ownerSlot salt redacted o.symbol) ∨
    CollisionAmong (cshake256Bytes sealCustomization)
      (boundaryPreimages salt redacted openings) := by
  cases hf : openings.find? (fun o => decide (o.slot ≠ ownerSlot salt redacted o.symbol)) with
  | none =>
    refine .inl fun o ho => ?_
    have hl := hopen o ho
    rw [lookup_sealedBoundary] at hl
    by_cases hm : o.symbol ∈ boundarySymbols redacted
    · exact ⟨hm, by simpa using List.find?_eq_none.mp hf o ho⟩
    · simp [hm] at hl
  | some o =>
    have ho := List.mem_of_find?_eq_some hf
    have hne : o.slot ≠ ownerSlot salt redacted o.symbol := by simpa using List.find?_some hf
    have hl := hopen o ho
    rw [lookup_sealedBoundary] at hl
    by_cases hm : o.symbol ∈ boundarySymbols redacted
    · simp only [hm, ↓reduceIte, Option.some.injEq] at hl
      rcases fieldCommit_binds hl with hq | hcol
      · exact absurd hq.2.symm hne
      · exact .inr (hcol.mono fun x hx =>
          hx.elim (fun h => .inl ⟨o.symbol, hm, h⟩) (fun h => .inr ⟨o, ho, h⟩))
    · simp [hm] at hl

/-- Openings that are the owner's slots and cover the visible reads give an environment that is
right at the boundary. -/
theorem owned_openings_agree (salt : String → List UInt8) {visible : List ReactiveCell}
    {redacted : List CachedCell} {openings : List BoundaryOpening}
    (hown : ∀ o ∈ openings, o.symbol ∈ boundarySymbols redacted ∧
      o.slot = ownerSlot salt redacted o.symbol)
    (hcov : ∀ c ∈ visible, ∀ s ∈ c.reads, s ∈ boundarySymbols redacted →
      ∃ o ∈ openings, o.symbol = s) :
    BoundaryAgrees visible redacted (snipEnv openings) := by
  intro c hc s hs
  unfold snipEnv
  cases hf : openings.find? (fun o => o.symbol == s) with
  | none =>
    have hm : s ∉ boundarySymbols redacted := fun hm => by
      obtain ⟨o, ho, hos⟩ := hcov c hc s hs hm
      exact List.find?_eq_none.mp hf o ho (by simp [hos])
    exact (boundaryValue_absent hm).symm
  | some o =>
    have hsym : o.symbol = s := by simpa using List.find?_some hf
    obtain ⟨_, hslot⟩ := hown o (List.mem_of_find?_eq_some hf)
    have hval : frameInt o.value = frameInt (boundaryValue redacted o.symbol) :=
      congrArg SealedSlot.secret hslot
    rw [← hsym]
    exact frameInt_injective hval

/-- The owner's snip opens its own slots, and every boundary symbol a visible cell reads. -/
theorem snipNotebook_owned (k : CellKernel) (salt : String → List UInt8) (V : List CellId)
    (cs : List ReactiveCell) :
    (∀ o ∈ (snipNotebook k salt V cs).openings,
      (o.symbol ∈ boundarySymbols (redactCache V (evalFromScratch k cs).cells) ∧
        o.slot = ownerSlot salt (redactCache V (evalFromScratch k cs).cells) o.symbol) ∧
      o.salt = salt o.symbol) ∧
    (∀ c ∈ snipCells V cs, ∀ s ∈ c.reads,
      s ∈ boundarySymbols (redactCache V (evalFromScratch k cs).cells) →
      ∃ o ∈ (snipNotebook k salt V cs).openings, o.symbol = s) := by
  constructor
  · intro o ho
    simp only [snipNotebook, List.mem_map, List.mem_filter] at ho
    obtain ⟨s, ⟨hmem, _⟩, rfl⟩ := ho
    exact ⟨⟨hmem, rfl⟩, rfl⟩
  · intro c hc s hs hmem
    refine ⟨⟨s, boundaryValue (redactCache V (evalFromScratch k cs).cells) s, salt s⟩, ?_, rfl⟩
    simp only [snipNotebook, List.mem_map, List.mem_filter]
    exact ⟨s, ⟨hmem, List.any_eq_true.mpr ⟨c, hc, by simpa using hs⟩⟩, rfl⟩

/-- **Snipping a frustum out of a notebook preserves evaluation and receipts.** On an admitted
notebook, with 256-bit salts, the owner's snip for a viewer of `V` is admitted by `evalSnip`, and
what the viewer computes from its own cells and the opened boundary is, cell for cell, the cached
result the whole notebook computes: for every visible id, the same values and the same 256-bit
receipt. -/
theorem snip_preserves_receipts (k : CellKernel) (salt : String → List UInt8) (V : List CellId)
    (cs : List ReactiveCell) (hdag : checkNotebookDag cs = true)
    (hsalt : ∀ s, (salt s).length = 32) :
    evalSnip k (snipNotebook k salt V cs) = .ok (snipCache V (evalFromScratch k cs).cells) ∧
    ∀ i ∈ V, cacheLookup (snipCache V (evalFromScratch k cs).cells) i =
      cacheLookup (evalFromScratch k cs).cells i := by
  refine ⟨?_, fun i hi => cacheLookup_snipCache V hi _⟩
  obtain ⟨hown, hcov⟩ := snipNotebook_owned k salt V cs
  have hopen : ∀ o ∈ (snipNotebook k salt V cs).openings,
      (snipNotebook k salt V cs).boundary.lookup o.symbol = some (fieldCommit o.symbol o.slot) ∧
      o.salt.length = 32 := by
    intro o ho
    obtain ⟨⟨hm, hslot⟩, hs⟩ := hown o ho
    refine ⟨?_, by rw [hs]; exact hsalt _⟩
    show (sealedBoundary salt _).lookup o.symbol = _
    rw [lookup_sealedBoundary, hslot]
    simp [hm]
  have hcov' : ∀ c ∈ (snipNotebook k salt V cs).cells, ∀ s ∈ c.reads,
      ((snipNotebook k salt V cs).boundary.lookup s).isSome = true →
      ∃ o ∈ (snipNotebook k salt V cs).openings, o.symbol = s := by
    intro c hc s hs hsome
    refine hcov c hc s hs ?_
    have hsome' : ((sealedBoundary salt (redactCache V (evalFromScratch k cs).cells)).lookup
        s).isSome = true := hsome
    rw [lookup_sealedBoundary] at hsome'
    by_cases hm : s ∈ boundarySymbols (redactCache V (evalFromScratch k cs).cells)
    · exact hm
    · simp [hm] at hsome'
  rw [evalSnip_of_checks (checkNotebookDag_snip V cs hdag) hopen hcov']
  exact congrArg Except.ok (snip_preserves_evaluation k V cs _ hdag
    (owned_openings_agree salt (fun o ho => (hown o ho).1) hcov))

/-- **A tampered boundary opening is refused, or it is a collision.** Let a viewer hold the visible
cells and the owner's sealed boundary, with any openings at all. If `evalSnip` admits them, then
every opening is the owner's slot for its symbol, value and salt, and the result is the visible
part of the whole notebook's run; or two sealed slots, among the owner's and the supplied ones,
collide under the seal hash. -/
theorem snip_tampered_refused_or_collides (k : CellKernel) (salt : String → List UInt8)
    (V : List CellId) (cs : List ReactiveCell) (hdag : checkNotebookDag cs = true)
    (n : NotebookSnip) (hcells : n.cells = snipCells V cs)
    (hboundary : n.boundary = sealedBoundary salt (redactCache V (evalFromScratch k cs).cells))
    {out : List CachedCell} (h : evalSnip k n = .ok out) :
    ((∀ o ∈ n.openings, o.symbol ∈ boundarySymbols (redactCache V (evalFromScratch k cs).cells) ∧
        o.slot = ownerSlot salt (redactCache V (evalFromScratch k cs).cells) o.symbol) ∧
      out = snipCache V (evalFromScratch k cs).cells) ∨
    CollisionAmong (cshake256Bytes sealCustomization)
      (boundaryPreimages salt (redactCache V (evalFromScratch k cs).cells) n.openings) := by
  obtain ⟨hopen, hcov, hout⟩ := evalSnip_ok h
  rw [hboundary] at hopen hcov
  rw [hcells] at hcov hout
  rcases openings_owned_or_collide salt _ n.openings (fun o ho => (hopen o ho).1) with hown | hcol
  · refine .inl ⟨hown, ?_⟩
    rw [hout]
    refine snip_preserves_evaluation k V cs _ hdag
      (owned_openings_agree salt hown fun c hc s hs hm => hcov c hc s hs ?_)
    rw [lookup_sealedBoundary]
    simp [hm]
  · exact .inr hcol

/-- **An edit to a visible cell has the same cone and the same receipts in the snipped notebook.**
On an admitted notebook whose visible set is closed downstream (`frustumClosed`: no redacted cell
reads a visible one), for an edit to a visible cell: the dirty cone is the same list of cells on
both sides, all of them visible; the sealed boundary of the edited notebook is the boundary the
viewer already holds; and the viewer's incremental recompute, from its own cache and the opened
boundary, yields exactly the visible part of the whole notebook's recompute, receipts included. -/
theorem snip_edit_preserves_cone_and_receipts (k : CellKernel) (salt : String → List UInt8)
    (V : List CellId) (cs : List ReactiveCell) (a : NotebookAction)
    (hdag : checkNotebookDag cs = true) (hclosed : frustumClosed V cs = true)
    (ht : a.target ∈ V) :
    (dirtyCone (snipCells V cs) a.target = dirtyCone cs a.target ∧
      ∀ i ∈ dirtyCone cs a.target, i ∈ V) ∧
    (snipNotebook k salt V (applyEdit a cs)).boundary = (snipNotebook k salt V cs).boundary ∧
    recompute k a (snipCache V (evalFromScratch k cs).cells)
        (snipEnv (snipNotebook k salt V cs).openings) [] =
      snipCache V (editCellAndRecompute k (evalFromScratch k cs) a).cells := by
  obtain ⟨hown, hcov⟩ := snipNotebook_owned k salt V cs
  obtain ⟨hR, hrec⟩ := snip_edit_preserves_receipts k V cs _ a hdag hclosed ht
    (owned_openings_agree salt (fun o ho => (hown o ho).1) hcov)
  refine ⟨dirtyCone_snip V cs a.target hclosed ht, ?_, hrec⟩
  rw [incrementalRecompute_eq_fromScratch] at hR
  show sealedBoundary salt (redactCache V (evalFromScratch k (applyEdit a cs)).cells) =
    sealedBoundary salt (redactCache V (evalFromScratch k cs).cells)
  rw [hR]

/-! ### The same cut, in the membrane

A notebook's run has a face in a `FrustumMembrane` frustum: each cell at its `cellAddress`, its
exports sealed. `Frustum.snip` of the visible addresses reifies the boundary above as its pins. -/

/-- What a frustum shows of one cell of a run: nothing in the clear, each export sealed as a field
commitment, and a read capability to every cell it reads. -/
def cellFace (salt : String → List UInt8) (full : List CachedCell) (x : CachedCell) : CellView :=
  { state := .record [],
    sealed := x.cell.defs.map fun s => (s, fieldCommit s ⟨frameInt (published x s), salt s⟩),
    caps := (full.filter fun p => decide (dependency p.cell x.cell)).map fun p =>
      ⟨cellAddress p.cell.id, [Auth.read]⟩,
    lit := [], epoch := 0 }

/-- **The membrane face of a notebook run**: every cell at its `cellAddress`. -/
def notebookFrustum (viewer : Obend.Vault.FrustumMembrane.CellId) (salt : String → List UInt8)
    (full : List CachedCell) : Frustum :=
  { viewer := viewer, cells := full.map fun x => (cellAddress x.cell.id, cellFace salt full x) }

theorem reflect_notebookFrustum {viewer : Obend.Vault.FrustumMembrane.CellId}
    {salt : String → List UInt8} {full : List CachedCell} {a : Obend.Vault.FrustumMembrane.CellId}
    {v : CellView} (h : (notebookFrustum viewer salt full).reflect a = some v) :
    ∃ x ∈ full, a = cellAddress x.cell.id ∧ v = cellFace salt full x := by
  have hm : (a, v) ∈ full.map fun x => (cellAddress x.cell.id, cellFace salt full x) :=
    mem_of_lookup _ a v h
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  exact ⟨x, hx, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- Under unique exports, the boundary value of a symbol is what its one redacted exporter
published. -/
theorem boundaryValue_published {R : List CachedCell} (hn : (boundarySymbols R).Nodup)
    {y : CachedCell} (hy : y ∈ R) {s : SymbolName} (hs : s ∈ y.cell.defs) :
    boundaryValue R s = published y s := by
  induction R with
  | nil => cases hy
  | cons z R' ih =>
    simp only [boundarySymbols, List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨_, hnR, hdisj⟩ := hn
    by_cases hz : s ∈ z.cell.defs
    · rcases List.mem_cons.mp hy with rfl | hy'
      · simp [boundaryValue, hz]
      · exact absurd rfl (hdisj s hz s (List.mem_flatMap.mpr ⟨y, hy', hs⟩))
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd hs hz
      · simpa [boundaryValue, hz] using ih hnR hy'

theorem boundarySymbols_nodup (k : CellKernel) (V : List CellId) {cs : List ReactiveCell}
    (hdag : checkNotebookDag cs = true) :
    (boundarySymbols (redactCache V (evalFromScratch k cs).cells)).Nodup := by
  have hsub : ∀ xs : List CachedCell, List.Sublist (boundarySymbols (redactCache V xs))
      ((xs.map CachedCell.cell).flatMap ReactiveCell.defs) := by
    intro xs
    induction xs with
    | nil => exact List.Sublist.refl _
    | cons x xs ih =>
      have hc : redactCache V (x :: xs) =
          if (!V.contains x.cell.id) = true then x :: redactCache V xs else redactCache V xs :=
        List.filter_cons
      rw [hc]
      split
      · simp only [boundarySymbols, List.flatMap_cons, List.map_cons]
        exact List.Sublist.append (List.Sublist.refl _) ih
      · simp only [List.map_cons, List.flatMap_cons]
        exact ih.trans (List.sublist_append_right _ _)
  have h := hsub (evalSchedule k cs fun _ => 0)
  rw [evalSchedule_cells] at h
  exact h.nodup (checkNotebookDag_acyclic_sound cs hdag).2.1

/-- **The cut of a notebook's frustum is its sealed boundary.** Snip the addresses of `V` out of the
membrane face of an admitted notebook's run. Every pin `Frustum.snip` makes stands for a visible
cell reading a redacted one; the frustum shows that redacted cell, at the pin's target, as its
face, and every commitment on that face is the commitment `evalSnip` checks openings against. And
every read of a redacted cell by a visible one is such a pin. -/
theorem notebook_cut_is_boundary (viewer : Obend.Vault.FrustumMembrane.CellId)
    (salt : String → List UInt8) (k : CellKernel) (cs : List ReactiveCell) (V : List CellId)
    (policy : Obend.Vault.FrustumMembrane.CellId → Cap → Disposition) (conserved : List String)
    (hdag : checkNotebookDag cs = true) :
    (∀ pin ∈ ((notebookFrustum viewer salt (evalFromScratch k cs).cells).snip
        (V.map cellAddress) policy conserved).pins,
      ∃ c ∈ snipCache V (evalFromScratch k cs).cells,
      ∃ q ∈ redactCache V (evalFromScratch k cs).cells,
        dependency q.cell c.cell ∧ pin.holder = cellAddress c.cell.id ∧
        pin.target = cellAddress q.cell.id ∧
        (notebookFrustum viewer salt (evalFromScratch k cs).cells).reflect pin.target =
          some (cellFace salt (evalFromScratch k cs).cells q) ∧
        ∀ e ∈ (cellFace salt (evalFromScratch k cs).cells q).sealed,
          (sealedBoundary salt (redactCache V (evalFromScratch k cs).cells)).lookup e.1 =
            some e.2) ∧
    (∀ c ∈ snipCache V (evalFromScratch k cs).cells,
      ∀ q ∈ redactCache V (evalFromScratch k cs).cells, dependency q.cell c.cell →
      ∃ pin ∈ ((notebookFrustum viewer salt (evalFromScratch k cs).cells).snip
          (V.map cellAddress) policy conserved).pins,
        pin.holder = cellAddress c.cell.id ∧ pin.target = cellAddress q.cell.id) := by
  generalize hfull : (evalFromScratch k cs).cells = full
  have hcell : ∀ x ∈ full, x.cell ∈ cs := fun x hx => by
    rw [← hfull] at hx
    exact evalSchedule_cell_mem hx
  have hface : ∀ x ∈ full, ∃ y ∈ full, y.cell = x.cell ∧
      (notebookFrustum viewer salt full).reflect (cellAddress x.cell.id) =
        some (cellFace salt full y) := by
    intro x hx
    have hsome : (((full.map fun x => (cellAddress x.cell.id, cellFace salt full x)).lookup
        (cellAddress x.cell.id))).isSome = true :=
      List.lookup_isSome_iff.mpr
        ⟨(cellAddress x.cell.id, cellFace salt full x), List.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    have hv' : (notebookFrustum viewer salt full).reflect (cellAddress x.cell.id) = some v := hv
    obtain ⟨y, hy, ha, rfl⟩ := reflect_notebookFrustum hv'
    exact ⟨y, hy, id_injective cs (checkNotebookDag_acyclic_sound cs hdag).1 y.cell x.cell
      (hcell y hy) (hcell x hx) (cellAddress_injective ha).symm, hv'⟩
  have hout : ∀ i, cellAddress i ∈ V.map cellAddress → i ∈ V := fun i hi => by
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hi
    rw [← cellAddress_injective he]
    exact hj
  constructor
  · intro pin hpin
    have hpin' : pin ∈ ((notebookFrustum viewer salt full).cut (V.map cellAddress)).map
        (fun e => (⟨e.1, e.2.target, e.2.rights,
          makeFace (notebookFrustum viewer salt full) e.2 (policy e.1 e.2)⟩ : BoundaryPin)) := hpin
    obtain ⟨⟨h, cap⟩, hcut, rfl⟩ := List.mem_map.mp hpin'
    obtain ⟨hF, v, hv, hcap, htar⟩ := mem_cut.mp hcut
    obtain ⟨x, hx, rfl, rfl⟩ := reflect_notebookFrustum hv
    have hcap' : cap ∈ (full.filter fun p => decide (dependency p.cell x.cell)).map
        (fun p => (⟨cellAddress p.cell.id, [Auth.read]⟩ : Cap)) := hcap
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcap'
    obtain ⟨hpfull, hdep⟩ := List.mem_filter.mp hp
    obtain ⟨y, hy, hyc, hyr⟩ := hface p hpfull
    have hpV : p.cell.id ∉ V := fun hin => htar (List.mem_map.mpr ⟨_, hin, rfl⟩)
    have hyV : y.cell.id ∉ V := by rw [hyc]; exact hpV
    have hyR : y ∈ redactCache V full := List.mem_filter.mpr ⟨hy, by simpa using hyV⟩
    refine ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hout _ hF⟩, y, hyR, ?_, rfl, ?_, ?_, ?_⟩
    · rw [hyc]
      exact of_decide_eq_true hdep
    · show cellAddress p.cell.id = cellAddress y.cell.id
      rw [hyc]
    · show (notebookFrustum viewer salt full).reflect (cellAddress p.cell.id) = _
      exact hyr
    · intro e he
      have he' : e ∈ y.cell.defs.map fun s =>
          (s, fieldCommit s ⟨frameInt (published y s), salt s⟩) := he
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he'
      have hmem : s ∈ boundarySymbols (redactCache V full) := List.mem_flatMap.mpr ⟨y, hyR, hs⟩
      have hval := boundaryValue_published (hfull ▸ boundarySymbols_nodup k V hdag) hyR hs
      rw [lookup_sealedBoundary]
      simp only [hmem, ↓reduceIte, ownerSlot, hval]
  · intro c hc q hq hdep
    obtain ⟨hcfull, hcV⟩ := List.mem_filter.mp hc
    obtain ⟨hqfull, hqV⟩ := List.mem_filter.mp hq
    obtain ⟨y, hy, hyc, hyr⟩ := hface c hcfull
    have hcap : (⟨cellAddress q.cell.id, [Auth.read]⟩ : Cap) ∈ (cellFace salt full y).caps :=
      List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hqfull, by rw [hyc]; exact decide_eq_true hdep⟩, rfl⟩
    have hcut : (cellAddress c.cell.id, (⟨cellAddress q.cell.id, [Auth.read]⟩ : Cap)) ∈
        (notebookFrustum viewer salt full).cut (V.map cellAddress) :=
      mem_cut.mpr ⟨List.mem_map.mpr ⟨_, by simpa using hcV, rfl⟩, _, hyr, hcap, fun hin => by
        have hqin := hout _ hin
        simp [hqin] at hqV⟩
    obtain ⟨pin, hpin, hh, ht, _, _⟩ := (snip_reifies_cut _ _ policy conserved).1 _ _ hcut
    exact ⟨pin, hpin, hh, ht⟩

/-! ## 5. The mirror badge: who checked this -/

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
  match classifyMirrorRender outcomes kind address with
  | .ok expected => decide (expected = r)
  | .error _ => false

theorem verifyMirrorBadge_iff (outcomes : VerificationGate → GateOutcome) (kind : String)
    (address : ByteArray) (r : MirrorRender) :
    verifyMirrorBadge outcomes kind address r = true ↔ classifyMirrorRender outcomes kind address = .ok r := by
  cases h : classifyMirrorRender outcomes kind address <;> simp [verifyMirrorBadge, h]

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
  exact (verifyMirrorBadge_iff _ _ _ _).mpr h

/-- A badge the validator accepts as self-verified: every gate passed on the reader's side. -/
theorem badge_selfVerified_all_passed {outcomes : VerificationGate → GateOutcome} {kind : String}
    {address : ByteArray} {r : MirrorRender} (h : verifyMirrorBadge outcomes kind address r = true)
    (htier : r.tier = .selfVerifiedLocal) (g : VerificationGate) : outcomes g = .passed := by
  obtain ⟨_, hnf, _, _, ht⟩ := classify_ok ((verifyMirrorBadge_iff _ _ _ _).mp h)
  have hnone := ht.mp htier
  have hns : outcomes g ≠ .skipped := fun hg => by
    have hm := mem_skippedGates.mpr hg
    rw [hnone] at hm
    cases hm
  cases hg : outcomes g <;> simp_all

/-- A badge the validator accepts as an untrusted mirror lists exactly the skipped gates and carries
the object's own 32-byte address. -/
theorem badge_untrusted_lists_skipped {outcomes : VerificationGate → GateOutcome} {kind : String}
    {address : ByteArray} {r : MirrorRender} (h : verifyMirrorBadge outcomes kind address r = true)
    (htier : r.tier = .untrustedOriginMirror) :
    r.skipped = skippedGates outcomes ∧ r.upgrade = ⟨kind, address⟩ ∧ address.size = 32 ∧
      r.skipped ≠ [] := by
  have hc := classify_ok ((verifyMirrorBadge_iff _ _ _ _).mp h)
  refine ⟨hc.2.2.2.1, hc.2.2.1, hc.1, ?_⟩
  intro hnil
  have ht := hc.2.2.2.2.mpr (hc.2.2.2.1 ▸ hnil)
  simp [htier] at ht

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
  obtain ⟨hsk, hup, hsize, _⟩ :=
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

/-! ## 6. The premises are inhabited -/

/-- A source that has finalized one turn: one field, under a 256-bit salt. -/
def demoSource : SourceCell :=
  (SourceCell.mk [] []).advance [[("title", ⟨[7], List.replicate 32 1⟩)]]

example : linkedFrom genesisDigest 0 demoSource.observed = true :=
  advance_linked _ _ rfl

example : ∃ (outcomes : VerificationGate → GateOutcome) (g : VerificationGate),
    outcomes g ≠ .passed := ⟨fun _ => .skipped, .receiptChain, by simp⟩

example : ∃ r, classifyMirrorRender (fun _ => .skipped) "page" genesisDigest = .ok r ∧
    r.tier = .untrustedOriginMirror := ⟨_, rfl, rfl⟩

end Obend.Vault.TransclusionAndMirror

end
