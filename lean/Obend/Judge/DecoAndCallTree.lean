module
public import Obend.Crypto.BinaryTower256
public import Obend.Crypto.SameOpening
public import Obend.Judge.TranscriptPolicy
public import Obend.Digest.Cshake256
import all Obend.Crypto.Transcript
import all Obend.Crypto.BinaryTower256

public section
namespace Obend.Judge.DecoAndCallTree
open Obend.Crypto Obend.Crypto.BinaryTower256
open Obend.Digest.Cshake256
set_option autoImplicit false

instance byteArrayLawfulBEq : LawfulBEq ByteArray where
  eq_of_beq := by
    intro a b h
    change (a.data == b.data) = true at h
    exact ByteArray.ext (eq_of_beq h)
  rfl := by
    intro a
    change (a.data == a.data) = true
    exact beq_self_eq_true a.data

/-! Canonical framing: unbounded LEB128 lengths, followed by exact byte fields. -/
def encInt (n : Nat) : List UInt8 := leb128 n
def encBytes (xs : List UInt8) : List UInt8 := encodeListField xs

def decInt : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else match decInt bs with
      | none => none
      | some (n, rest) => some (b.toNat - 128 + 128 * n, rest)

theorem decInt_leb128Aux (fuel n : Nat) (rest : List UInt8) (hn : n ≤ fuel) :
    decInt (leb128Aux fuel n ++ rest) = some (n, rest) := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ fuel ih =>
    simp only [leb128Aux]
    split
    · rename_i hlt
      simp only [List.singleton_append, decInt, uint8_toNat_lt_256_of_lt (by omega : n < 256),
        hlt, ↓reduceIte]
    · rename_i hlt
      have hb : 128 + n % 128 < 256 := by omega
      have hd : n / 128 ≤ fuel := by omega
      simp only [List.cons_append, decInt, uint8_toNat_lt_256_of_lt hb]
      rw [ite_eq_right (by omega), ih _ hd]
      simp only [Nat.add_sub_cancel_left]
      congr 1
      congr 1
      omega

theorem decInt_encInt (n : Nat) (rest : List UInt8) :
    decInt (encInt n ++ rest) = some (n, rest) := decInt_leb128Aux n n rest (Nat.le_refl _)

def encFields : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => encBytes x ++ encFields xs

def encList (xs : List (List UInt8)) : List UInt8 := encInt xs.length ++ encFields xs

def decFields : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match decInt bs with
    | none => none
    | some (len, tail) =>
      if len ≤ tail.length then
        match decFields n (tail.drop len) with
        | none => none
        | some (fields, rest) => some (tail.take len :: fields, rest)
      else none

def decList (bs : List UInt8) : Option (List (List UInt8)) :=
  match decInt bs with
  | none => none
  | some (n, tail) => match decFields n tail with
    | none => none
    | some (fields, rest) => if rest.isEmpty then some fields else none

theorem decFields_encFields (xs : List (List UInt8)) (rest : List UInt8) :
    decFields xs.length (encFields xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, encFields, encBytes, encodeListField, List.append_assoc, decFields]
    rw [show leb128 x.length = encInt x.length from rfl, decInt_encInt]
    simp only [List.length_append]
    rw [ite_eq_left (by omega)]
    simp only [List.drop_left, List.take_left, ih]

theorem decList_encList (xs : List (List UInt8)) : decList (encList xs) = some xs := by
  unfold decList encList
  rw [decInt_encInt]
  dsimp only
  have h := decFields_encFields xs []
  rw [List.append_nil] at h
  rw [h]
  rfl

theorem encList_injective (xs ys : List (List UInt8)) (h : encList xs = encList ys) : xs = ys := by
  have he := congrArg decList h
  rw [decList_encList, decList_encList] at he
  exact Option.some.inj he

theorem encInt_injective (n m : Nat) (h : encInt n = encInt m) : n = m := by
  have h1 := decInt_encInt n []
  have h2 := decInt_encInt m []
  simp only [List.append_nil] at h1 h2
  rw [h, h2] at h1
  exact (Prod.mk.inj (Option.some.inj h1)).1.symm

abbrev Hash256 := { b : ByteArray // b.size = 32 }

def hash256 (domain : String) (input : List UInt8) : Hash256 :=
  ⟨cshake32ByteArray domain.toUTF8.data.toList input, cshake32ByteArray_size _ _⟩

/-- Collision evidence retains both distinct preimages and every output byte. -/
def CshakeCollision (domain : String) : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ cshake256Bytes domain.toUTF8.data.toList a =
    cshake256Bytes domain.toUTF8.data.toList b

theorem hash256_collision (domain : String) (a b : List UInt8)
    (hne : a ≠ b) (heq : hash256 domain a = hash256 domain b) : CshakeCollision domain := by
  refine ⟨a, b, hne, ?_⟩
  have h := congrArg (fun h : Hash256 => h.val.data.toList) heq
  simpa only [hash256, cshake32ByteArray, Native.bytesOfList_toList] using h

/-- The complete authenticated record supplied by the TLS/notary verification boundary.
Its membership in the verifier's record store is trusted input, not a signature algorithm. -/
structure SessionRecord where
  host : ByteArray
  notary : ByteArray
  time : Nat
  request : ByteArray
  response : ByteArray
  ghashTag : Tower128
  verifierNonce : ByteArray
  paymentIntentId : ByteArray
  deriving DecidableEq

def tagBytes (tag : Tower128) : List UInt8 := Obend.Digest.HashBytes.be 16 (packTower 7 tag).toNat

def recordFields (r : SessionRecord) : List (List UInt8) :=
  [r.host.data.toList, r.notary.data.toList, encInt r.time, r.request.data.toList, r.response.data.toList,
   tagBytes r.ghashTag, r.verifierNonce.data.toList, r.paymentIntentId.data.toList]

def recordPreimage (r : SessionRecord) : List UInt8 := encList (recordFields r)
def recordCommit (r : SessionRecord) : Hash256 := hash256 "Obend.https.record/v1" (recordPreimage r)

theorem tagBytes_injective (a b : Tower128) (h : tagBytes a = tagBytes b) : a = b := by
  apply packTower_injective 7
  apply BitVec.eq_of_toNat_eq
  have hp : 256 ^ 16 = 2 ^ 128 := by decide
  apply Obend.Digest.HashBytes.be_injective (w := 16) _ _ h <;>
    rw [hp] <;> exact BitVec.isLt _

theorem recordPreimage_injective (a b : SessionRecord) (h : recordPreimage a = recordPreimage b) : a = b := by
  have hf := encList_injective (recordFields a) (recordFields b) h
  simp only [recordFields, List.cons.injEq, and_true] at hf
  obtain ⟨hhost, hnotary, htime, hreq, hresp, htag, hnonce, hintent⟩ := hf
  have h1 := byteArray_eq_of_toList_eq hhost
  have h2 := byteArray_eq_of_toList_eq hnotary
  have h3 := encInt_injective _ _ htime
  have h4 := byteArray_eq_of_toList_eq hreq
  have h5 := byteArray_eq_of_toList_eq hresp
  have h6 := tagBytes_injective _ _ htag
  have h7 := byteArray_eq_of_toList_eq hnonce
  have h8 := byteArray_eq_of_toList_eq hintent
  cases a; cases b; simp_all

/-- A parser opening and a record opening use the same full commitment interface. -/
def OpeningRelation (commitment : Hash256) (record : SessionRecord) : Prop := recordCommit record = commitment

structure SharedCommitment where
  commitment : Hash256
  recordOpening : SessionRecord
  parserOpening : SessionRecord
  recordOpens : OpeningRelation commitment recordOpening
  parserOpens : OpeningRelation commitment parserOpening

/-- Exact witness sharing has zero mismatch indicator; hash-only sharing uses collision extraction. -/
def bindAdv (s : SharedCommitment) : Nat := if s.recordOpening = s.parserOpening then 0 else 1

def shareRecord (r : SessionRecord) : SharedCommitment :=
  ⟨recordCommit r, r, r, rfl, rfl⟩

theorem deco_sameOpening_bindAdv_zero (r : SessionRecord) : bindAdv (shareRecord r) = 0 := by
  simp [bindAdv, shareRecord]

theorem deco_binds_disclosed_facts_or_collision (s : SharedCommitment) :
    s.recordOpening = s.parserOpening ∨ CshakeCollision "Obend.https.record/v1" := by
  if h : s.recordOpening = s.parserOpening then exact Or.inl h
  else
    right
    exact hash256_collision _ _ _ (fun he => h (recordPreimage_injective _ _ he))
      (s.recordOpens.trans s.parserOpens.symm)

/-- A disclosed span names exact offsets; zero-length claims are refused. -/
structure DisclosedSpan where
  offset : Nat
  bytes : ByteArray
  deriving DecidableEq

/-- ByteArray implementation. Out-of-bounds and redacted indices are rejected. -/
def checkSpan (plain mask : ByteArray) (span : DisclosedSpan) : Bool :=
  decide (0 < span.bytes.size) && decide (span.offset + span.bytes.size ≤ plain.size) &&
  decide (mask.size = plain.size) &&
  (List.range span.bytes.size).all fun j =>
    mask[span.offset + j]! == 0 && plain[span.offset + j]! == span.bytes[j]!

/-- The semantic statement is equality to authenticated bytes at every disclosed offset. -/
def SpanMeaning (plain mask : ByteArray) (span : DisclosedSpan) : Prop :=
  0 < span.bytes.size ∧ span.offset + span.bytes.size ≤ plain.size ∧ mask.size = plain.size ∧
  ∀ j, j < span.bytes.size → mask[span.offset + j]! = 0 ∧ plain[span.offset + j]! = span.bytes[j]!

theorem checkSpan_iff (plain mask : ByteArray) (span : DisclosedSpan) :
    checkSpan plain mask span = true ↔ SpanMeaning plain mask span := by
  simp [checkSpan, SpanMeaning, Bool.and_eq_true, List.all_eq_true, List.mem_range, and_assoc]

theorem unmasked_match_binds_authenticated_bytes (plain mask : ByteArray) (span : DisclosedSpan)
    (h : checkSpan plain mask span = true) (j : Nat) (hj : j < span.bytes.size) :
    plain[span.offset + j]! = span.bytes[j]! ∧ mask[span.offset + j]! = 0 :=
  ⟨((checkSpan_iff _ _ _).mp h).2.2.2 j hj |>.2,
   ((checkSpan_iff _ _ _).mp h).2.2.2 j hj |>.1⟩

/-- Confinement reuses the transcript policy's delimiter classification. All redacted
bytes are non-structural; every other mask byte must be exactly 0x00 or 0xFF. -/
def checkMask (plain mask : ByteArray) : Bool :=
  decide (plain.size = mask.size) && (List.range plain.size).all fun i =>
    mask[i]! == 0 || (mask[i]! == 255 && !isStructuralDelimiterByte plain[i]!.toNat)

def MaskMeaning (plain mask : ByteArray) : Prop :=
  plain.size = mask.size ∧ ∀ i, i < plain.size →
    mask[i]! = 0 ∨ (mask[i]! = 255 ∧ isStructuralDelimiterByte plain[i]!.toNat = false)

theorem checkMask_iff (plain mask : ByteArray) : checkMask plain mask = true ↔ MaskMeaning plain mask := by
  simp [checkMask, MaskMeaning, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true]

structure DecoAttestation where
  record : SessionRecord
  recordTranscriptCommit : Hash256
  requestMask : ByteArray
  responseMask : ByteArray
  requestFacts : List DisclosedSpan
  responseFacts : List DisclosedSpan

/-- Authentication is a verifier-owned store of records obtained from a verified TLS
capture. The policy also pins identity, time and required secret-byte offsets. -/
structure DecoPolicy where
  authenticatedRecords : List SessionRecord
  notaries : List ByteArray
  hosts : List ByteArray
  minTime : Nat
  maxTime : Nat
  secretRequestOffsets : List Nat

structure SessionLedger where
  consumedNonces : List ByteArray
  consumedIntents : List ByteArray
  deriving Inhabited

def checkFresh (ledger : SessionLedger) (a : DecoAttestation) : Bool :=
  decide (a.record.verifierNonce ∉ ledger.consumedNonces) &&
  decide (a.record.paymentIntentId ∉ ledger.consumedIntents) &&
  decide (0 < a.record.verifierNonce.size) && decide (0 < a.record.paymentIntentId.size)

def Fresh (ledger : SessionLedger) (a : DecoAttestation) : Prop :=
  a.record.verifierNonce ∉ ledger.consumedNonces ∧
  a.record.paymentIntentId ∉ ledger.consumedIntents ∧
  0 < a.record.verifierNonce.size ∧ 0 < a.record.paymentIntentId.size

theorem checkFresh_iff (ledger : SessionLedger) (a : DecoAttestation) :
    checkFresh ledger a = true ↔ Fresh ledger a := by
  simp [checkFresh, Fresh, Bool.and_eq_true, and_assoc]

def checkPolicy (p : DecoPolicy) (a : DecoAttestation) : Bool :=
  decide (a.record ∈ p.authenticatedRecords) && decide (a.record.notary ∈ p.notaries) &&
  decide (a.record.host ∈ p.hosts) && decide (p.minTime ≤ a.record.time) &&
  decide (a.record.time ≤ p.maxTime) &&
  p.secretRequestOffsets.all (fun i => decide (i < a.requestMask.size) && a.requestMask[i]! == 255)

def PolicyMeaning (p : DecoPolicy) (a : DecoAttestation) : Prop :=
  a.record ∈ p.authenticatedRecords ∧ a.record.notary ∈ p.notaries ∧ a.record.host ∈ p.hosts ∧
  p.minTime ≤ a.record.time ∧ a.record.time ≤ p.maxTime ∧
  ∀ i ∈ p.secretRequestOffsets, i < a.requestMask.size ∧ a.requestMask[i]! = 255

theorem checkPolicy_iff (p : DecoPolicy) (a : DecoAttestation) :
    checkPolicy p a = true ↔ PolicyMeaning p a := by
  simp [checkPolicy, PolicyMeaning, Bool.and_eq_true, List.all_eq_true, and_assoc]

def checkDecoAttestation (p : DecoPolicy) (ledger : SessionLedger) (a : DecoAttestation) : Bool :=
  decide (a.recordTranscriptCommit = recordCommit a.record) && checkFresh ledger a && checkPolicy p a &&
  checkMask a.record.request a.requestMask && checkMask a.record.response a.responseMask &&
  a.requestFacts.all (checkSpan a.record.request a.requestMask) &&
  a.responseFacts.all (checkSpan a.record.response a.responseMask)

def DecoRelation (p : DecoPolicy) (ledger : SessionLedger) (a : DecoAttestation) : Prop :=
  a.recordTranscriptCommit = recordCommit a.record ∧ Fresh ledger a ∧ PolicyMeaning p a ∧
  MaskMeaning a.record.request a.requestMask ∧ MaskMeaning a.record.response a.responseMask ∧
  (∀ s ∈ a.requestFacts, SpanMeaning a.record.request a.requestMask s) ∧
  (∀ s ∈ a.responseFacts, SpanMeaning a.record.response a.responseMask s)

theorem checkDecoAttestation_iff_relation (p : DecoPolicy) (ledger : SessionLedger) (a : DecoAttestation) :
    checkDecoAttestation p ledger a = true ↔ DecoRelation p ledger a := by
  simp [checkDecoAttestation, DecoRelation, Bool.and_eq_true, checkFresh_iff,
    checkPolicy_iff, checkMask_iff, checkSpan_iff, List.all_eq_true, and_assoc]

def consume (ledger : SessionLedger) (a : DecoAttestation) : SessionLedger :=
  ⟨a.record.verifierNonce :: ledger.consumedNonces, a.record.paymentIntentId :: ledger.consumedIntents⟩

inductive ValidDecoTrace (p : DecoPolicy) : SessionLedger → List DecoAttestation → SessionLedger → Prop
  | nil (s) : ValidDecoTrace p s [] s
  | cons {s a as t} : DecoRelation p s a → ValidDecoTrace p (consume s a) as t →
      ValidDecoTrace p s (a :: as) t

def checkDecoTrace (p : DecoPolicy) : SessionLedger → List DecoAttestation → Bool
  | _, [] => true
  | s, a :: as => checkDecoAttestation p s a && checkDecoTrace p (consume s a) as

theorem checkDecoTrace_iff (p : DecoPolicy) (s : SessionLedger) (as : List DecoAttestation) :
    checkDecoTrace p s as = true ↔ ∃ t, ValidDecoTrace p s as t := by
  induction as generalizing s with
  | nil => exact ⟨fun _ => ⟨s, .nil s⟩, fun _ => rfl⟩
  | cons a as ih =>
    rw [checkDecoTrace, Bool.and_eq_true, checkDecoAttestation_iff_relation, ih]
    constructor
    · rintro ⟨ha, t, ht⟩; exact ⟨t, .cons ha ht⟩
    · rintro ⟨t, ht⟩; cases ht with | cons ha ht => exact ⟨ha, _, ht⟩

theorem ValidDecoTrace.nonces_mono {p : DecoPolicy} {s t : SessionLedger} {as : List DecoAttestation}
    (h : ValidDecoTrace p s as t) : ∀ n ∈ s.consumedNonces, n ∈ t.consumedNonces := by
  induction h with
  | nil => exact fun _ h => h
  | cons _ _ ih => exact fun n hn => ih n (.tail _ hn)

theorem ValidDecoTrace.intents_mono {p : DecoPolicy} {s t : SessionLedger} {as : List DecoAttestation}
    (h : ValidDecoTrace p s as t) : ∀ n ∈ s.consumedIntents, n ∈ t.consumedIntents := by
  induction h with
  | nil => exact fun _ h => h
  | cons _ _ ih => exact fun n hn => ih n (.tail _ hn)

theorem replay_nonce_rejected (p : DecoPolicy) (s t : SessionLedger) (as : List DecoAttestation)
    (h : ValidDecoTrace p s as t) (a : DecoAttestation) (hn : a.record.verifierNonce ∈ s.consumedNonces) :
    checkDecoAttestation p t a = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact ((checkDecoAttestation_iff_relation _ _ _).mp ha).2.1.1 (h.nonces_mono _ hn)

theorem replay_intent_rejected (p : DecoPolicy) (s t : SessionLedger) (as : List DecoAttestation)
    (h : ValidDecoTrace p s as t) (a : DecoAttestation) (hn : a.record.paymentIntentId ∈ s.consumedIntents) :
    checkDecoAttestation p t a = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact ((checkDecoAttestation_iff_relation _ _ _).mp ha).2.1.2.1 (h.intents_mono _ hn)

def spanFields (s : DisclosedSpan) : List UInt8 := encList [encInt s.offset, s.bytes.data.toList]

theorem spanFields_injective (a b : DisclosedSpan) (h : spanFields a = spanFields b) : a = b := by
  have he := encList_injective _ _ h
  simp only [List.cons.injEq, and_true] at he
  have h1 := encInt_injective _ _ he.1
  have h2 := byteArray_eq_of_toList_eq he.2
  cases a; cases b; simp_all

theorem map_injective_of_injective {α β : Type} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (as bs : List α) (h : as.map f = bs.map f) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      obtain ⟨hab, ht⟩ := List.cons.inj h
      rw [hf a b hab, ih bs ht]

def attestationFields (a : DecoAttestation) : List (List UInt8) :=
  [recordPreimage a.record, a.recordTranscriptCommit.val.data.toList, a.requestMask.data.toList,
   a.responseMask.data.toList, encList (a.requestFacts.map spanFields), encList (a.responseFacts.map spanFields)]

theorem attestationFields_injective (a b : DecoAttestation)
    (h : attestationFields a = attestationFields b) : a = b := by
  simp only [attestationFields, List.cons.injEq, and_true] at h
  obtain ⟨hr, hc, hq, hs, hqf, hsf⟩ := h
  have h1 := recordPreimage_injective _ _ hr
  have h2 : a.recordTranscriptCommit = b.recordTranscriptCommit :=
    Subtype.ext (byteArray_eq_of_toList_eq hc)
  have h3 := byteArray_eq_of_toList_eq hq
  have h4 := byteArray_eq_of_toList_eq hs
  have h5 := map_injective_of_injective spanFields spanFields_injective _ _ (encList_injective _ _ hqf)
  have h6 := map_injective_of_injective spanFields spanFields_injective _ _ (encList_injective _ _ hsf)
  cases a; cases b; simp_all

/-- MMR carry merges older peaks on the left, preserving order and height. -/
def mmrPush (height : Nat) (root : Hash256) : List (Nat × Hash256) → List (Nat × Hash256)
  | [] => [(height, root)]
  | (h, r) :: rest =>
    if h = height then
      mmrPush (height + 1) (hash256 "Obend.mmr.branch/v1" (encList [encInt height, r.val.data.toList, root.val.data.toList])) rest
    else (height, root) :: (h, r) :: rest

def mmrBag : List (Nat × Hash256) → Hash256
  | [] => hash256 "Obend.mmr.empty/v1" (encList [])
  | (h, r) :: rest => hash256 "Obend.mmr.bag/v1" (encList [encInt h, r.val.data.toList, (mmrBag rest).val.data.toList])

def mrootC (children : List Hash256) : Hash256 :=
  mmrBag (children.foldl (fun peaks r => mmrPush 0
    (hash256 "Obend.mmr.leaf/v1" (encList [r.val.data.toList])) peaks) [])

inductive HopKind where
  | localComputation
  | leafHttpsHop
  | recursiveHttpsCallee
  deriving DecidableEq

def kindTag : HopKind → Nat
  | .localComputation => 0
  | .leafHttpsHop => 1
  | .recursiveHttpsCallee => 2

theorem kindTag_injective (a b : HopKind) (h : kindTag a = kindTag b) : a = b := by
  cases a <;> cases b <;> simp_all [kindTag]

structure HttpsHop where
  kind : HopKind
  attestation : DecoAttestation
  rootOffset : Nat

inductive HttpsCallTree where
  | node (hop : HttpsHop) (children : List HttpsCallTree)

def nodePreimage (h : HttpsHop) (childrenRoot : Hash256) : List UInt8 :=
  encList [encInt (kindTag h.kind), encList (attestationFields h.attestation),
    encInt h.rootOffset, childrenRoot.val.data.toList]

/-- Every node-header field is bound, including disclosure masks, spans and root offset. -/
theorem nodePreimage_injective (a b : HttpsHop) (ar br : Hash256)
    (h : nodePreimage a ar = nodePreimage b br) : a = b ∧ ar = br := by
  have he := encList_injective _ _ h
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨hk, ha, ho, hr⟩ := he
  have h1 := kindTag_injective _ _ (encInt_injective _ _ hk)
  have h2 := attestationFields_injective _ _ (encList_injective _ _ ha)
  have h3 := encInt_injective _ _ ho
  have h4 : ar = br := Subtype.ext (byteArray_eq_of_toList_eq hr)
  refine ⟨?_, h4⟩
  cases a; cases b; simp_all

mutual
def treeRoot : HttpsCallTree → Hash256
  | .node h cs => hash256 "Obend.calltree.node/v1" (nodePreimage h (mrootC (treeRoots cs)))
termination_by structural t => t
def treeRoots : List HttpsCallTree → List Hash256
  | [] => []
  | t :: ts => treeRoot t :: treeRoots ts
termination_by structural ts => ts
end

/-- Lowercase hex encoding of every digest byte, including leading zeros. -/
def hexDigit (n : Nat) : UInt8 := UInt8.ofNat (if n < 10 then 48 + n else 87 + n)
def hex64 (h : Hash256) : List UInt8 :=
  h.val.data.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

theorem hex64_length (h : Hash256) : (hex64 h).length = 64 := by
  have aux (xs : List UInt8) :
      (xs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]).length = 2 * xs.length := by
    induction xs with
    | nil => rfl
    | cons b bs ih => simp [List.flatMap_cons, ih, Nat.mul_add, Nat.add_comm]; omega
  rw [hex64, aux]
  have hs : h.val.data.toList.length = 32 := by
    change h.val.data.toList.length = 32
    rw [Array.length_toList, ByteArray.size_data]
    exact h.property
  rw [hs]

def rootField (h : Hash256) : ByteArray :=
  ⟨("\"subtree_root\":\"".toUTF8.data.toList ++ hex64 h ++ "\"".toUTF8.data.toList).toArray⟩

def bodyStart (response : ByteArray) : Option Nat :=
  ((List.range response.size).find? fun i =>
    decide (i + 4 ≤ response.size) && response[i]! == 13 && response[i+1]! == 10 &&
      response[i+2]! == 13 && response[i+3]! == 10).map (· + 4)

def checkSubtreeRoot (a : DecoAttestation) (offset : Nat) (root : Hash256) : Bool :=
  match bodyStart a.record.response with
  | none => false
  | some start => decide (start ≤ offset) && checkSpan a.record.response a.responseMask ⟨offset, rootField root⟩

def SubtreeRootMeaning (a : DecoAttestation) (offset : Nat) (root : Hash256) : Prop :=
  ∃ start, bodyStart a.record.response = some start ∧ start ≤ offset ∧
    SpanMeaning a.record.response a.responseMask ⟨offset, rootField root⟩

theorem checkSubtreeRoot_iff (a : DecoAttestation) (offset : Nat) (root : Hash256) :
    checkSubtreeRoot a offset root = true ↔ SubtreeRootMeaning a offset root := by
  unfold checkSubtreeRoot SubtreeRootMeaning
  cases hs : bodyStart a.record.response <;> simp [Bool.and_eq_true, checkSpan_iff]

structure CallTreePolicy where
  deco : DecoPolicy
  ledger : SessionLedger
  recorders : List ByteArray
  /-- The deterministic local operation selected by this verifier. -/
  localEval : ByteArray → ByteArray

def checkHop (p : CallTreePolicy) (h : HttpsHop) (root : Hash256) (leaf : Bool) : Bool :=
  match h.kind with
  | .localComputation => decide (p.localEval h.attestation.record.request = h.attestation.record.response)
  | .leafHttpsHop => leaf && checkDecoAttestation p.deco p.ledger h.attestation
  | .recursiveHttpsCallee => checkDecoAttestation p.deco p.ledger h.attestation &&
      decide (h.attestation.record.host ∈ p.recorders) && checkSubtreeRoot h.attestation h.rootOffset root

def HopMeaning (p : CallTreePolicy) (h : HttpsHop) (root : Hash256) (leaf : Bool) : Prop :=
  match h.kind with
  | .localComputation => p.localEval h.attestation.record.request = h.attestation.record.response
  | .leafHttpsHop => leaf = true ∧ DecoRelation p.deco p.ledger h.attestation
  | .recursiveHttpsCallee => DecoRelation p.deco p.ledger h.attestation ∧
      h.attestation.record.host ∈ p.recorders ∧ SubtreeRootMeaning h.attestation h.rootOffset root

theorem checkHop_iff (p : CallTreePolicy) (h : HttpsHop) (root : Hash256) (leaf : Bool) :
    checkHop p h root leaf = true ↔ HopMeaning p h root leaf := by
  unfold checkHop HopMeaning
  cases h.kind <;> simp [Bool.and_eq_true, checkDecoAttestation_iff_relation,
    checkSubtreeRoot_iff, and_assoc]

mutual
def checkTree (p : CallTreePolicy) : HttpsCallTree → Bool
  | .node h cs => checkHop p h (mrootC (treeRoots cs)) cs.isEmpty && checkForest p cs
termination_by structural t => t
def checkForest (p : CallTreePolicy) : List HttpsCallTree → Bool
  | [] => true
  | t :: ts => checkTree p t && checkForest p ts
termination_by structural ts => ts
end

mutual
def TreeMeaning (p : CallTreePolicy) : HttpsCallTree → Prop
  | .node h cs => HopMeaning p h (mrootC (treeRoots cs)) cs.isEmpty ∧ ForestMeaning p cs
termination_by structural t => t
def ForestMeaning (p : CallTreePolicy) : List HttpsCallTree → Prop
  | [] => True
  | t :: ts => TreeMeaning p t ∧ ForestMeaning p ts
termination_by structural ts => ts
end

mutual
theorem checkTree_iff (p : CallTreePolicy) (t : HttpsCallTree) :
    checkTree p t = true ↔ TreeMeaning p t := by
  cases t with
  | node h cs =>
    simp only [checkTree, TreeMeaning, Bool.and_eq_true, checkHop_iff, checkForest_iff p cs]
termination_by structural t

theorem checkForest_iff (p : CallTreePolicy) (ts : List HttpsCallTree) :
    checkForest p ts = true ↔ ForestMeaning p ts := by
  cases ts with
  | nil => simp only [checkForest, ForestMeaning]
  | cons t ts =>
    simp only [checkForest, ForestMeaning, Bool.and_eq_true, checkTree_iff p t, checkForest_iff p ts]
termination_by structural ts
end

mutual
def treeHops : HttpsCallTree → List HttpsHop
  | .node h cs => h :: forestHops cs
termination_by structural t => t
def forestHops : List HttpsCallTree → List HttpsHop
  | [] => []
  | t :: ts => treeHops t ++ forestHops ts
termination_by structural ts => ts
end

def treeAttestations (t : HttpsCallTree) : List DecoAttestation :=
  (treeHops t).filterMap fun h => match h.kind with
    | .localComputation => none
    | _ => some h.attestation

structure DataflowEdge where
  fromNode : Nat
  toNode : Nat
  srcOff : Nat
  dstOff : Nat
  bytes : ByteArray
  deriving DecidableEq

def checkDataflowEdge (nodes : Array HttpsHop) (e : DataflowEdge) : Bool :=
  match nodes[e.fromNode]?, nodes[e.toNode]? with
  | some src, some dst => decide (e.fromNode < e.toNode) &&
      decide (src.kind ≠ .localComputation) && decide (dst.kind ≠ .localComputation) &&
      checkSpan src.attestation.record.response src.attestation.responseMask ⟨e.srcOff, e.bytes⟩ &&
      checkSpan dst.attestation.record.request dst.attestation.requestMask ⟨e.dstOff, e.bytes⟩
  | _, _ => false

def DataflowMeaning (nodes : Array HttpsHop) (e : DataflowEdge) : Prop :=
  ∃ src dst, nodes[e.fromNode]? = some src ∧ nodes[e.toNode]? = some dst ∧ e.fromNode < e.toNode ∧
    src.kind ≠ .localComputation ∧ dst.kind ≠ .localComputation ∧
    SpanMeaning src.attestation.record.response src.attestation.responseMask ⟨e.srcOff, e.bytes⟩ ∧
    SpanMeaning dst.attestation.record.request dst.attestation.requestMask ⟨e.dstOff, e.bytes⟩

theorem checkDataflowEdge_iff (nodes : Array HttpsHop) (e : DataflowEdge) :
    checkDataflowEdge nodes e = true ↔ DataflowMeaning nodes e := by
  unfold checkDataflowEdge DataflowMeaning
  cases hs : nodes[e.fromNode]? <;> cases hd : nodes[e.toNode]? <;>
    simp [Bool.and_eq_true, checkSpan_iff, and_assoc]

/-- The object contains the statement and its proposed execution; certificates only
select an audit round. Refuting clauses therefore concern the object at every round. -/
structure CallTreeClaim where
  policy : CallTreePolicy
  tree : HttpsCallTree
  expectedRoot : Hash256
  requiredEdges : List DataflowEdge

structure CallTreeCertificate where
  auditRound : Nat

def callTreeVerify (p : CallTreePolicy) (tree : HttpsCallTree) (expected : Hash256)
    (edges : List DataflowEdge) : Bool :=
  decide (treeRoot tree = expected) && checkTree p tree &&
  checkDecoTrace p.deco p.ledger (treeAttestations tree) &&
  edges.all (checkDataflowEdge (treeHops tree).toArray)

def CallTreeMeaning (p : CallTreePolicy) (tree : HttpsCallTree) (expected : Hash256)
    (edges : List DataflowEdge) : Prop :=
  treeRoot tree = expected ∧ TreeMeaning p tree ∧
  (∃ finalLedger, ValidDecoTrace p.deco p.ledger (treeAttestations tree) finalLedger) ∧
  ∀ edge ∈ edges, DataflowMeaning (treeHops tree).toArray edge

theorem callTreeVerify_iff (p : CallTreePolicy) (tree : HttpsCallTree) (expected : Hash256)
    (edges : List DataflowEdge) :
    callTreeVerify p tree expected edges = true ↔ CallTreeMeaning p tree expected edges := by
  simp [callTreeVerify, CallTreeMeaning, Bool.and_eq_true, checkTree_iff,
    checkDecoTrace_iff, checkDataflowEdge_iff, List.all_eq_true, and_assoc]

/-- This verifier checks explicit authenticated openings at every hop. Consequently
it proves the semantic branch directly; hash-only alternate openings have the
separate constructive collision extractor above. -/
theorem callTreeVerify_sound_or_collision (p : CallTreePolicy) (tree : HttpsCallTree) (expected : Hash256)
    (edges : List DataflowEdge) (h : callTreeVerify p tree expected edges = true) :
    CallTreeMeaning p tree expected edges ∨ CshakeCollision "Obend.calltree.node/v1" :=
  Or.inl ((callTreeVerify_iff _ _ _ _).mp h)

inductive CallTreeRefusal where
  | invalidExecution
  deriving DecidableEq

instance callTreeJudge : Obend.Judge CallTreeClaim CallTreeCertificate where
  Clause := CallTreeRefusal
  Meaning q _ := CallTreeMeaning q.policy q.tree q.expectedRoot q.requiredEdges
  check _ q _ := if callTreeVerify q.policy q.tree q.expectedRoot q.requiredEdges then .ok
    else .refused .invalidExecution []
  sound := by
    intro _ q _ h
    split at h
    · rename_i hcheck
      exact (callTreeVerify_iff _ _ _ _).mp hcheck
    · cases h
  refutes _ := true
  refuted := by
    intro _ q _ _ _ href _ c' hmeaning
    have hcheck := (callTreeVerify_iff _ _ _ _).mpr hmeaning
    simp [hcheck] at href
  Fragment _ := True
  complete := by
    intro q _ ⟨c, hc⟩
    refine ⟨c, 0, ?_⟩
    have hcheck := (callTreeVerify_iff _ _ _ _).mpr hc
    simp [hcheck]
  mono := by intros; rfl

end Obend.Judge.DecoAndCallTree
