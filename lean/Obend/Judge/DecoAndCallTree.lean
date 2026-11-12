module
/-
# Obend.Judge.DecoAndCallTree — committed HTTPS transcripts, GHASH-authenticated sessions, and call trees

An attestation of an HTTPS session holds no plaintext. Each direction is a `TranscriptView`: the
root of a span tree (`Obend.Judge.VpaJson.spanMerkleRoot` at cSHAKE256) and one slot per span,
either opened (the bytes and their inclusion path) or masked. Slot 0 is the HTTP head, opened;
the remaining slots partition the JSON body.

**What the verifier checks** (`checkDecoAttestation`, no plaintext): the nonce and payment intent
are fresh; the GHASH tag (`BinaryTower256.ghashAuth`) under the verifier's key for that nonce
authenticates the record commitment (as the two authenticated-data blocks) and the ciphertext
blocks; notary, host and time are in policy; in each view every opened slot verifies at its index,
the head ends at the first blank line, every mask is string-safe and sits in a value string
outside any escape (`TranscriptPolicy.spanConfined`, the core of `VpaJson.checkJsonRedaction`),
and the redacted body passes the JSON grammar. `deco_ghash_forgery_keys_bound`: the keys under
which two attestations with different GHASH polynomials share a tag are at most the block count.

**What the prover's opening adds** (`checkOpening`, the relation a proof of disclosure
establishes): the real spans commit to the view's root, opened slots are the real spans, and
each hidden span walks inside its value string back to the machine state, cutting no escape
(redacting the backslash of `\"` is refused here). `checkOpening_parses`: the real body drives
the JSON machine to the state the redacted body reaches, so both have one grammar verdict and one
set of object keys. `checkOpening_binds`: two openings of one view are equal, or cSHAKE256
collides at the span tag (computed by `Lsafe.spanRootCollision`).

**Callee linkage.** `checkSubtreeRoot` reads the depth-1 string members of the response body with
the JSON machine (`topLevelMembers`): a member counts only if its key and value came from opened
bytes with no escape. `"subtree_root"` inside a nested object, inside a string value, or under a
mask is not a member.

**Call trees.** `treeRoot` hashes every field of a hop, length-framed, with the span-tree root of
its children's roots. `treeRoot_binds`: one root, one tree, or a collision
(`CallTreeCollision`). `callTreeVerify_sound_or_collision`: every tree that opens the verified
root is the verified tree. `callTreeJudge` means `CallTreeSpec`: the root binds the tree, the
sessions replay as one ledger trace (`ValidDecoTrace`: no nonce or intent twice), every hop is
admitted, and every real transcript parses as its view. `decoCallTreeFormat` is the byte format
`deco-calltree@1`.

Not here: the AES-GCM link from plaintext to ciphertext blocks (the TLS adapter's; see
`BinaryTower256.ghashPoly`); redaction inside the HTTP head; the notary's signature.
-/
public import Obend.Crypto.BinaryTower256
public import Obend.Crypto.SameOpening
public import Obend.Judge.TranscriptPolicy
public import Obend.Vault.Lsafe
public import Obend.Digest.Cshake256
import all Obend.Crypto.Transcript
import all Obend.Crypto.BinaryTower256
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.TranscriptPolicy
import all Obend.Vault.Lsafe

public section
namespace Obend.Judge.DecoAndCallTree
open Obend.Crypto Obend.Crypto.BinaryTower256
open Obend.Digest.Cshake256
open Obend.Judge.VpaJson (JState JMode StrSub stepJson specRunJson specRunJson_append jsonAccepting
  SpanRoot spanMerkleRoot spanTag verifySpanMerkleInclusion)
open Obend.Judge.Commit (cshakeHasher HashCollision hexOf unhex)
open Obend.Judge (spanConfined spanConfined_run)
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

/-! ## Transcript views: committed spans, opened or masked -/

/-- The public metadata of a session. -/
structure SessionHeader where
  host : ByteArray
  notary : ByteArray
  time : Nat
  verifierNonce : ByteArray
  paymentIntentId : ByteArray

/-- One span of a committed transcript as the verifier sees it. -/
inductive SpanSlot where
  | opened (bytes : ByteArray) (siblings : List ByteArray)
  | masked (mask : ByteArray)
  deriving DecidableEq

/-- The verifier's view of a transcript: the span root and one slot per span. Slot 0 is the HTTP
head; the rest partition the JSON body. -/
structure TranscriptView where
  root : SpanRoot
  slots : List SpanSlot
  deriving DecidableEq

/-- The bytes a slot shows: the span, or its mask. -/
def SpanSlot.shown : SpanSlot → List UInt8
  | .opened b _ => b.data.toList
  | .masked m => m.data.toList

/-- The redacted transcript. -/
def viewBytes : List SpanSlot → List UInt8
  | [] => []
  | s :: rest => s.shown ++ viewBytes rest

/-- The bytes of real spans, in order. -/
def realBytes : List ByteArray → List UInt8
  | [] => []
  | s :: rest => s.data.toList ++ realBytes rest

/-- Every opened slot verifies at its index against the root. -/
def slotsOpen (root : SpanRoot) : List SpanSlot → Nat → Bool
  | [], _ => true
  | .opened b sibs :: rest, i =>
    verifySpanMerkleInclusion cshakeHasher spanTag root b ⟨i, sibs⟩ && slotsOpen root rest (i + 1)
  | .masked _ :: rest, i => slotsOpen root rest (i + 1)

/-- The JSON machine over body slots: an opened slot is read; a masked slot must sit in a value
string outside any escape, with a string-safe mask, and leaves the machine where it is. -/
def bodyRun : JState → List SpanSlot → Option JState
  | st, [] => some st
  | st, .opened b _ :: rest => bodyRun (specRunJson b.data.toList st) rest
  | st, .masked m :: rest => if spanConfined st [] m.data.toList then bodyRun st rest else none

/-- The offset just past the first blank line. -/
def bodyStart (head : ByteArray) : Option Nat :=
  ((List.range head.size).find? fun i =>
    decide (i + 4 ≤ head.size) && head[i]! == 13 && head[i+1]! == 10 &&
      head[i+2]! == 13 && head[i+3]! == 10).map (· + 4)

/-- **The public check of a view.** One slot per committed span; opened slots verify; slot 0 is
the head and ends at its first blank line; masks are confined; the redacted body is empty or one
JSON document. -/
def checkView (v : TranscriptView) : Bool :=
  decide (v.slots.length = v.root.count) && slotsOpen v.root v.slots 0 &&
    match v.slots with
    | .opened head _ :: body =>
      decide (bodyStart head = some head.size) &&
        match bodyRun JState.init body with
        | some st => body.isEmpty || jsonAccepting st
        | none => false
    | _ => false

/-- **The mask check**, slot by slot: an opened slot is the real span; a hidden span is confined
at the machine state the body has reached (`spanConfined`, the core of
`VpaJson.checkJsonRedaction`): it sits in a value string and cuts no escape. -/
def checkMask : JState → List SpanSlot → List ByteArray → Bool
  | _, [], [] => true
  | st, .opened b _ :: rest, s :: spans =>
    decide (s = b) && checkMask (specRunJson b.data.toList st) rest spans
  | st, .masked m :: rest, s :: spans =>
    spanConfined st s.data.toList m.data.toList && checkMask st rest spans
  | _, _, _ => false

/-- **The opening relation**: the real spans commit to the view's root, the head is the real
head, and the body slots are faithful. -/
def checkOpening (v : TranscriptView) (spans : List ByteArray) : Bool :=
  decide (spanMerkleRoot cshakeHasher spanTag spans = v.root) &&
    match v.slots, spans with
    | .opened head _ :: body, s :: rest => decide (s = head) && checkMask JState.init body rest
    | _, _ => false

theorem spanConfined_nil {st : JState} {span mask : List UInt8}
    (h : spanConfined st span mask = true) : spanConfined st [] mask = true := by
  simp only [spanConfined, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1, rfl⟩, h.2⟩

/-- Faithful slots: the redacted body and the real body drive the machine alike. -/
theorem checkMask_run (slots : List SpanSlot) : ∀ (spans : List ByteArray) (st : JState),
    checkMask st slots spans = true →
    bodyRun st slots = some (specRunJson (realBytes spans) st) ∧
      specRunJson (viewBytes slots) st = specRunJson (realBytes spans) st := by
  induction slots with
  | nil =>
    intro spans st h
    cases spans with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp [checkMask] at h
  | cons slot rest ih =>
    intro spans st h
    cases spans with
    | nil => cases slot <;> simp [checkMask] at h
    | cons s spans =>
      cases slot with
      | opened b sibs =>
        simp only [checkMask, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hs, hr⟩ := h
        subst hs
        obtain ⟨i1, i2⟩ := ih spans _ hr
        simp only [bodyRun, viewBytes, realBytes, SpanSlot.shown, specRunJson_append]
        exact ⟨i1, i2⟩
      | masked m =>
        simp only [checkMask, Bool.and_eq_true] at h
        obtain ⟨hc, hr⟩ := h
        obtain ⟨hspan, hmask⟩ := spanConfined_run hc
        obtain ⟨i1, i2⟩ := ih spans st hr
        simp only [bodyRun, viewBytes, realBytes, SpanSlot.shown, specRunJson_append,
          spanConfined_nil hc, ↓reduceIte, hspan, hmask]
        exact ⟨i1, i2⟩

/-- The public run of the body slots is the machine's run over the redacted body. -/
theorem bodyRun_viewBytes (slots : List SpanSlot) : ∀ (st st' : JState),
    bodyRun st slots = some st' → specRunJson (viewBytes slots) st = st' := by
  induction slots with
  | nil => intro st st' h; cases h; rfl
  | cons slot rest ih =>
    intro st st' h
    cases slot with
    | opened b sibs =>
      simp only [bodyRun] at h
      simp only [viewBytes, SpanSlot.shown, specRunJson_append]
      exact ih _ _ h
    | masked m =>
      simp only [bodyRun] at h
      split at h
      · rename_i hc
        simp only [viewBytes, SpanSlot.shown, specRunJson_append, (spanConfined_run hc).2]
        exact ih _ _ h
      · cases h

/-- **An opened view parses as the real transcript.** The real body and the redacted body end in
one machine state: one grammar verdict, one set of object keys. -/
theorem checkOpening_parses {v : TranscriptView} {spans : List ByteArray} :
    checkOpening v spans = true →
    spanMerkleRoot cshakeHasher spanTag spans = v.root ∧
      ∃ head sibs body rest, v.slots = .opened head sibs :: body ∧ spans = head :: rest ∧
        specRunJson (realBytes rest) JState.init = specRunJson (viewBytes body) JState.init := by
  intro h
  simp only [checkOpening, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hroot, hm⟩ := h
  refine ⟨hroot, ?_⟩
  obtain ⟨root, slots⟩ := v
  cases slots with
  | nil => simp at hm
  | cons slot body =>
    cases slot with
    | masked m => simp at hm
    | opened head sibs =>
      cases spans with
      | nil => simp at hm
      | cons s rest =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        exact ⟨head, sibs, body, rest, rfl, by rw [hm.1],
          (checkMask_run body rest _ hm.2).2.symm⟩

/-- **Openings bind.** Two openings of one view are the same spans, or cSHAKE256 collides at the
span tag. -/
theorem checkOpening_binds {v : TranscriptView} {s₁ s₂ : List ByteArray} :
    checkOpening v s₁ = true → checkOpening v s₂ = true →
    s₁ = s₂ ∨ Nonempty (HashCollision cshakeHasher spanTag) := by
  intro h₁ h₂
  by_cases hne : s₁ = s₂
  · exact Or.inl hne
  · have e := (checkOpening_parses h₁).1.trans (checkOpening_parses h₂).1.symm
    exact Or.inr ⟨Obend.Vault.Lsafe.spanRootCollision cshakeHasher spanTag hne (congrArg (·.top) e)⟩

/-! ## Depth-1 string members of a body -/

/-- The reader of depth-1 string members: the machine, the member being read, and whether its
key and value so far came from opened bytes with no escape. -/
structure Scan where
  st : JState
  key : ByteArray
  val : ByteArray
  clean : Bool
  found : List (ByteArray × ByteArray)

def Scan.init : Scan := ⟨JState.init, ByteArray.empty, ByteArray.empty, false, []⟩

/-- Exactly one bracket is open and it is an object. -/
def depthOne (st : JState) : Bool :=
  match st.stack with
  | [f] => f.isObj
  | _ => false

/-- One opened byte. At depth 1: a key opens, a key closes, a string value is read byte by byte
(an escape spoils it), a string value closes and the member is recorded if clean. -/
def scanByte (s : Scan) (b : UInt8) : Scan :=
  if depthOne s.st then
    match s.st.mode, (stepJson s.st b).mode with
    | .key _, .str true .normal => { s with st := stepJson s.st b, clean := true }
    | .str true _, .colon =>
      { s with st := stepJson s.st b, key := s.st.curKey, val := ByteArray.empty }
    | .str false .normal, .str false .normal => { s with st := stepJson s.st b, val := s.val.push b }
    | .str false _, .str false _ => { s with st := stepJson s.st b, clean := false }
    | .str false .normal, .after =>
      { s with st := stepJson s.st b, clean := false,
               found := if s.clean then (s.key, s.val) :: s.found else s.found }
    | _, _ => { s with st := stepJson s.st b }
  else { s with st := stepJson s.st b }

/-- Opened slots are read; a masked slot spoils the member being read. -/
def scanSlots : Scan → List SpanSlot → Scan
  | s, [] => s
  | s, .opened b _ :: rest => scanSlots (b.data.toList.foldl scanByte s) rest
  | s, .masked _ :: rest => scanSlots { s with clean := false } rest

/-- **The depth-1 string members of a body** that were read entirely from opened bytes. -/
def topLevelMembers (body : List SpanSlot) : List (ByteArray × ByteArray) :=
  (scanSlots Scan.init body).found

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

def subtreeKey : ByteArray := "subtree_root".toByteArray

/-- **Callee linkage**: the response body has the depth-1 member `"subtree_root"` whose string
value is the root in hex, read from opened bytes. A nested or reflected occurrence is not one. -/
def checkSubtreeRoot (v : TranscriptView) (root : Hash256) : Bool :=
  match v.slots with
  | _ :: body => decide ((subtreeKey, (⟨(hex64 root).toArray⟩ : ByteArray)) ∈ topLevelMembers body)
  | [] => false

/-- Callee linkage is membership among the depth-1 members read from opened bytes of the body. -/
theorem checkSubtreeRoot_iff (v : TranscriptView) (root : Hash256) :
    checkSubtreeRoot v root = true ↔ ∃ head body, v.slots = head :: body ∧
      (subtreeKey, (⟨(hex64 root).toArray⟩ : ByteArray)) ∈ topLevelMembers body := by
  unfold checkSubtreeRoot
  cases v.slots with
  | nil => simp
  | cons s body =>
    simp only [decide_eq_true_eq, List.cons.injEq]
    exact ⟨fun h => ⟨s, body, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨_, hb⟩, h⟩ => hb ▸ h⟩

/-! ## Attestations: GHASH over the record commitment, policy, freshness -/

/-- An attestation: the header, the two views, the ciphertext blocks and the GHASH tag. -/
structure DecoAttestation where
  header : SessionHeader
  request : TranscriptView
  response : TranscriptView
  ctBlocks : List Tower128
  lenBlock : Tower128
  ghashTag : Tower128

def tagBytes (tag : Tower128) : List UInt8 := Obend.Digest.HashBytes.be 16 (packTower 7 tag).toNat

theorem tagBytes_injective (a b : Tower128) (h : tagBytes a = tagBytes b) : a = b := by
  apply packTower_injective 7
  apply BitVec.eq_of_toNat_eq
  have hp : 256 ^ 16 = 2 ^ 128 := by decide
  apply Obend.Digest.HashBytes.be_injective (w := 16) _ _ h <;>
    rw [hp] <;> exact BitVec.isLt _

/-- Sixteen bytes as a tower element. -/
def blockOfBytes (bs : List UInt8) : Tower128 :=
  unpackTower 7 (BitVec.ofNat (2 ^ 7) (Obend.Digest.HashBytes.ofBE bs))

def rootFields (r : SpanRoot) : List UInt8 := encList [encInt r.count, r.top.data.toList]

theorem rootFields_injective (a b : SpanRoot) (h : rootFields a = rootFields b) : a = b := by
  have he := encList_injective _ _ h
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨c₁, t₁⟩ := a
  obtain ⟨c₂, t₂⟩ := b
  have h1 := encInt_injective _ _ he.1
  have h2 := byteArray_eq_of_toList_eq he.2
  simp only at h1 h2
  rw [h1, h2]

/-- The bytes the record commitment is hashed from: the header and both span roots. -/
def recordPreimage (a : DecoAttestation) : List UInt8 :=
  encList [a.header.host.data.toList, a.header.notary.data.toList, encInt a.header.time,
    a.header.verifierNonce.data.toList, a.header.paymentIntentId.data.toList,
    rootFields a.request.root, rootFields a.response.root]

def recordCommit (a : DecoAttestation) : Hash256 :=
  hash256 "Obend.https.record/v2" (recordPreimage a)

/-- The record commitment as the two authenticated-data blocks. -/
def commitBlocks (c : Hash256) : List Tower128 :=
  [blockOfBytes (c.val.data.toList.take 16), blockOfBytes (c.val.data.toList.drop 16)]

/-- The blocks GHASH authenticates: the record commitment, the ciphertext, the length block. -/
def ghashMessage (a : DecoAttestation) : List Tower128 :=
  commitBlocks (recordCommit a) ++ a.ctBlocks ++ [a.lenBlock]

/-- **The tag check**: `ghashAuth` under the key, over the record commitment as authenticated data
and the ciphertext blocks, is the attested tag. -/
def tagVerifies (key : Tower128) (a : DecoAttestation) : Bool :=
  decide (ghashAuth key (commitBlocks (recordCommit a)) a.ctBlocks a.lenBlock = a.ghashTag)

/-- **Forgery needs a root.** If two attestations whose GHASH polynomials differ carry one tag,
the keys under which both verify are roots of the difference: at most `L` of them. -/
theorem deco_ghash_forgery_keys_bound (a b : DecoAttestation) (L : Nat) (keys : List Tower128)
    (ha : (ghashMessage a).length ≤ L) (hb : (ghashMessage b).length ≤ L) (hnd : keys.Nodup)
    (hne : ∃ H, ghashPoly H (ghashMessage a) ≠ ghashPoly H (ghashMessage b))
    (htag : a.ghashTag = b.ghashTag)
    (hok : ∀ H ∈ keys, tagVerifies H a = true ∧ tagVerifies H b = true) : keys.length ≤ L := by
  refine ghashDiff_roots_bound _ _ L keys ha hb hnd hne fun H hH => ?_
  obtain ⟨h1, h2⟩ := hok H hH
  have e1 : ghashPoly H (ghashMessage a) = a.ghashTag := of_decide_eq_true h1
  have e2 : ghashPoly H (ghashMessage b) = b.ghashTag := of_decide_eq_true h2
  rw [e1, e2, htag]

/-- The verifier's side: its GHASH key for each of its nonces, the notaries and hosts it accepts,
the time window, and the request slots that must be masked. -/
structure DecoPolicy where
  sessionKeys : List (ByteArray × Tower128)
  notaries : List ByteArray
  hosts : List ByteArray
  minTime : Nat
  maxTime : Nat
  secretRequestSlots : List Nat

structure SessionLedger where
  consumedNonces : List ByteArray
  consumedIntents : List ByteArray
  deriving Inhabited

def sessionKey (p : DecoPolicy) (nonce : ByteArray) : Option Tower128 :=
  (p.sessionKeys.find? fun kv => decide (kv.1 = nonce)).map (·.2)

def slotMasked (slots : List SpanSlot) (i : Nat) : Bool :=
  match slots[i]? with
  | some (.masked _) => true
  | _ => false

def checkFresh (ledger : SessionLedger) (a : DecoAttestation) : Bool :=
  decide (a.header.verifierNonce ∉ ledger.consumedNonces) &&
  decide (a.header.paymentIntentId ∉ ledger.consumedIntents) &&
  decide (0 < a.header.verifierNonce.size) && decide (0 < a.header.paymentIntentId.size)

def Fresh (ledger : SessionLedger) (a : DecoAttestation) : Prop :=
  a.header.verifierNonce ∉ ledger.consumedNonces ∧
  a.header.paymentIntentId ∉ ledger.consumedIntents ∧
  0 < a.header.verifierNonce.size ∧ 0 < a.header.paymentIntentId.size

theorem checkFresh_iff (ledger : SessionLedger) (a : DecoAttestation) :
    checkFresh ledger a = true ↔ Fresh ledger a := by
  simp [checkFresh, Fresh, Bool.and_eq_true, and_assoc]

def checkPolicy (p : DecoPolicy) (a : DecoAttestation) : Bool :=
  (match sessionKey p a.header.verifierNonce with
    | some key => tagVerifies key a
    | none => false) &&
  decide (a.header.notary ∈ p.notaries) && decide (a.header.host ∈ p.hosts) &&
  decide (p.minTime ≤ a.header.time) && decide (a.header.time ≤ p.maxTime) &&
  p.secretRequestSlots.all (slotMasked a.request.slots)

/-- The session is authenticated under the verifier's key for its nonce, and in policy. -/
def PolicyMeaning (p : DecoPolicy) (a : DecoAttestation) : Prop :=
  (∃ key, sessionKey p a.header.verifierNonce = some key ∧
    ghashAuth key (commitBlocks (recordCommit a)) a.ctBlocks a.lenBlock = a.ghashTag) ∧
  a.header.notary ∈ p.notaries ∧ a.header.host ∈ p.hosts ∧
  p.minTime ≤ a.header.time ∧ a.header.time ≤ p.maxTime ∧
  ∀ i ∈ p.secretRequestSlots, slotMasked a.request.slots i = true

theorem checkPolicy_iff (p : DecoPolicy) (a : DecoAttestation) :
    checkPolicy p a = true ↔ PolicyMeaning p a := by
  unfold checkPolicy PolicyMeaning
  cases sessionKey p a.header.verifierNonce <;>
    simp [tagVerifies, Bool.and_eq_true, List.all_eq_true, and_assoc]

/-- **The verifier's check of one attestation.** No plaintext is read. -/
def checkDecoAttestation (p : DecoPolicy) (ledger : SessionLedger) (a : DecoAttestation) : Bool :=
  checkFresh ledger a && checkPolicy p a && checkView a.request && checkView a.response

def DecoRelation (p : DecoPolicy) (ledger : SessionLedger) (a : DecoAttestation) : Prop :=
  Fresh ledger a ∧ PolicyMeaning p a ∧ checkView a.request = true ∧ checkView a.response = true

theorem checkDecoAttestation_iff_relation (p : DecoPolicy) (ledger : SessionLedger)
    (a : DecoAttestation) : checkDecoAttestation p ledger a = true ↔ DecoRelation p ledger a := by
  simp [checkDecoAttestation, DecoRelation, Bool.and_eq_true, checkFresh_iff, checkPolicy_iff,
    and_assoc]

def consume (ledger : SessionLedger) (a : DecoAttestation) : SessionLedger :=
  ⟨a.header.verifierNonce :: ledger.consumedNonces,
    a.header.paymentIntentId :: ledger.consumedIntents⟩

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
    (h : ValidDecoTrace p s as t) (a : DecoAttestation)
    (hn : a.header.verifierNonce ∈ s.consumedNonces) : checkDecoAttestation p t a = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact ((checkDecoAttestation_iff_relation _ _ _).mp ha).1.1 (h.nonces_mono _ hn)

theorem replay_intent_rejected (p : DecoPolicy) (s t : SessionLedger) (as : List DecoAttestation)
    (h : ValidDecoTrace p s as t) (a : DecoAttestation)
    (hn : a.header.paymentIntentId ∈ s.consumedIntents) : checkDecoAttestation p t a = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact ((checkDecoAttestation_iff_relation _ _ _).mp ha).1.2.1 (h.intents_mono _ hn)

/-! ## Call trees: every field framed, one root, one tree -/

def slotFields : SpanSlot → List UInt8
  | .opened b sibs => encList [[0], b.data.toList, encList (sibs.map fun x => x.data.toList)]
  | .masked m => encList [[1], m.data.toList]

theorem slotFields_injective (a b : SpanSlot) (h : slotFields a = slotFields b) : a = b := by
  cases a with
  | opened b₁ s₁ =>
    cases b with
    | opened b₂ s₂ =>
      have he := encList_injective _ _ (show encList _ = encList _ from h)
      simp only [List.cons.injEq, true_and, and_true] at he
      rw [byteArray_eq_of_toList_eq he.1,
        map_injective_of_injective (fun x : ByteArray => x.data.toList)
          (fun _ _ => byteArray_eq_of_toList_eq) _ _ (encList_injective _ _ he.2)]
    | masked m₂ =>
      have he := encList_injective _ _ (show encList _ = encList _ from h)
      simp at he
  | masked m₁ =>
    cases b with
    | opened b₂ s₂ =>
      have he := encList_injective _ _ (show encList _ = encList _ from h)
      simp at he
    | masked m₂ =>
      have he := encList_injective _ _ (show encList _ = encList _ from h)
      simp only [List.cons.injEq, true_and, and_true] at he
      rw [byteArray_eq_of_toList_eq he]

def viewFields (v : TranscriptView) : List UInt8 :=
  encList [rootFields v.root, encList (v.slots.map slotFields)]

theorem viewFields_injective (a b : TranscriptView) (h : viewFields a = viewFields b) : a = b := by
  have he := encList_injective _ _ h
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨r₁, s₁⟩ := a
  obtain ⟨r₂, s₂⟩ := b
  have h1 := rootFields_injective _ _ he.1
  have h2 := map_injective_of_injective slotFields slotFields_injective _ _
    (encList_injective _ _ he.2)
  simp only at h1 h2
  rw [h1, h2]

/-- Every field of an attestation, each a byte string to be length-framed. -/
def attestationFields (a : DecoAttestation) : List (List UInt8) :=
  [a.header.host.data.toList, a.header.notary.data.toList, encInt a.header.time,
   a.header.verifierNonce.data.toList, a.header.paymentIntentId.data.toList,
   viewFields a.request, viewFields a.response, encList (a.ctBlocks.map tagBytes),
   tagBytes a.lenBlock, tagBytes a.ghashTag]

theorem attestationFields_injective (a b : DecoAttestation)
    (h : attestationFields a = attestationFields b) : a = b := by
  obtain ⟨⟨h1, n1, t1, v1, p1⟩, q1, r1, c1, l1, g1⟩ := a
  obtain ⟨⟨h2, n2, t2, v2, p2⟩, q2, r2, c2, l2, g2⟩ := b
  simp only [attestationFields, List.cons.injEq, and_true] at h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h
  have a1 : h1 = h2 := byteArray_eq_of_toList_eq e1
  have a2 : n1 = n2 := byteArray_eq_of_toList_eq e2
  have a3 : t1 = t2 := encInt_injective _ _ e3
  have a4 : v1 = v2 := byteArray_eq_of_toList_eq e4
  have a5 : p1 = p2 := byteArray_eq_of_toList_eq e5
  have a6 : q1 = q2 := viewFields_injective _ _ e6
  have a7 : r1 = r2 := viewFields_injective _ _ e7
  have a8 : c1 = c2 :=
    map_injective_of_injective tagBytes tagBytes_injective _ _ (encList_injective _ _ e8)
  have a9 : l1 = l2 := tagBytes_injective _ _ e9
  have a10 : g1 = g2 := tagBytes_injective _ _ e10
  rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]

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

inductive HttpsCallTree where
  | node (hop : HttpsHop) (children : List HttpsCallTree)

def nodeDomain : String := "Obend.calltree.node/v2"
def childrenTag : String := "Obend.calltree.children/v2"

def nodePreimage (h : HttpsHop) (childrenRoot : Hash256) : List UInt8 :=
  encList [encInt (kindTag h.kind), encList (attestationFields h.attestation),
    childrenRoot.val.data.toList]

/-- Every field of a node is bound: kind, header, both views, ciphertext, tag, children root. -/
theorem nodePreimage_injective (a b : HttpsHop) (ar br : Hash256)
    (h : nodePreimage a ar = nodePreimage b br) : a = b ∧ ar = br := by
  have he := encList_injective _ _ h
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨hk, ha, hr⟩ := he
  obtain ⟨k₁, a₁⟩ := a
  obtain ⟨k₂, a₂⟩ := b
  have h1 := kindTag_injective _ _ (encInt_injective _ _ hk)
  have h2 := attestationFields_injective _ _ (encList_injective _ _ ha)
  simp only at h1 h2
  exact ⟨by rw [h1, h2], Subtype.ext (byteArray_eq_of_toList_eq hr)⟩

/-- The root of a list of child roots: the top of their span tree under the children tag, which
binds their number. -/
def mrootC (children : List Hash256) : Hash256 :=
  ⟨(spanMerkleRoot cshakeHasher childrenTag (children.map Subtype.val)).top,
    cshakeHasher.size_eq _ _⟩

mutual
def treeRoot : HttpsCallTree → Hash256
  | .node h cs => hash256 nodeDomain (nodePreimage h (mrootC (treeRoots cs)))
termination_by structural t => t
def treeRoots : List HttpsCallTree → List Hash256
  | [] => []
  | t :: ts => treeRoot t :: treeRoots ts
termination_by structural ts => ts
end

/-- A collision of the node hash, or of the children tree. -/
def CallTreeCollision : Prop :=
  CshakeCollision nodeDomain ∨ Nonempty (HashCollision cshakeHasher childrenTag)

theorem mrootC_binds {r₁ r₂ : List Hash256} (h : mrootC r₁ = mrootC r₂) :
    r₁ = r₂ ∨ Nonempty (HashCollision cshakeHasher childrenTag) := by
  by_cases hv : r₁.map Subtype.val = r₂.map Subtype.val
  · exact Or.inl (map_injective_of_injective Subtype.val (fun _ _ => Subtype.ext) _ _ hv)
  · exact Or.inr ⟨Obend.Vault.Lsafe.spanRootCollision cshakeHasher childrenTag hv
      (congrArg Subtype.val h)⟩

mutual
/-- **Tree roots bind.** Two trees with one root are one tree (every hop, every field, every
child), or the node hash or the children tree collides. -/
theorem treeRoot_binds (t₁ t₂ : HttpsCallTree) (h : treeRoot t₁ = treeRoot t₂) :
    t₁ = t₂ ∨ CallTreeCollision := by
  cases t₁ with
  | node h₁ cs₁ =>
    cases t₂ with
    | node h₂ cs₂ =>
      simp only [treeRoot] at h
      by_cases hp : nodePreimage h₁ (mrootC (treeRoots cs₁)) =
          nodePreimage h₂ (mrootC (treeRoots cs₂))
      · obtain ⟨hh, hr⟩ := nodePreimage_injective _ _ _ _ hp
        rcases mrootC_binds hr with hrs | hc
        · rcases treeRoots_binds cs₁ cs₂ hrs with hcs | hc
          · exact Or.inl (by rw [hh, hcs])
          · exact Or.inr hc
        · exact Or.inr (Or.inr hc)
      · exact Or.inr (Or.inl (hash256_collision _ _ _ hp h))
termination_by structural t₁

theorem treeRoots_binds (ts₁ ts₂ : List HttpsCallTree) (h : treeRoots ts₁ = treeRoots ts₂) :
    ts₁ = ts₂ ∨ CallTreeCollision := by
  cases ts₁ with
  | nil =>
    cases ts₂ with
    | nil => exact Or.inl rfl
    | cons _ _ => simp [treeRoots] at h
  | cons t₁ r₁ =>
    cases ts₂ with
    | nil => simp [treeRoots] at h
    | cons t₂ r₂ =>
      simp only [treeRoots, List.cons.injEq] at h
      rcases treeRoot_binds t₁ t₂ h.1 with ht | hc
      · rcases treeRoots_binds r₁ r₂ h.2 with hr | hc
        · exact Or.inl (by rw [ht, hr])
        · exact Or.inr hc
      · exact Or.inr hc
termination_by structural ts₁
end

/-- The deterministic local operations a verifier can select. -/
inductive LocalOp where
  | identity
  | digest
  deriving DecidableEq

def runLocalOp : LocalOp → ByteArray → ByteArray
  | .identity, b => b
  | .digest, b => (hash256 "Obend.calltree.local/v2" b.data.toList).val

structure CallTreePolicy where
  deco : DecoPolicy
  ledger : SessionLedger
  recorders : List ByteArray
  localOp : LocalOp

def allOpened (slots : List SpanSlot) : Bool :=
  slots.all fun s => match s with
    | .opened _ _ => true
    | .masked _ => false

def viewDoc (v : TranscriptView) : ByteArray := ⟨(viewBytes v.slots).toArray⟩

/-- A local hop is fully opened and is the selected operation; a leaf hop is an admitted session
with no children; a recursive callee is an admitted session of a recorder whose response names
the root of its children. -/
def checkHop (p : CallTreePolicy) (h : HttpsHop) (root : Hash256) (leaf : Bool) : Bool :=
  match h.kind with
  | .localComputation =>
    allOpened h.attestation.request.slots && allOpened h.attestation.response.slots &&
      decide (runLocalOp p.localOp (viewDoc h.attestation.request) = viewDoc h.attestation.response)
  | .leafHttpsHop => leaf && checkDecoAttestation p.deco p.ledger h.attestation
  | .recursiveHttpsCallee => checkDecoAttestation p.deco p.ledger h.attestation &&
      decide (h.attestation.header.host ∈ p.recorders) &&
      checkSubtreeRoot h.attestation.response root

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
def treeHops : HttpsCallTree → List HttpsHop
  | .node h cs => h :: forestHops cs
termination_by structural t => t
def forestHops : List HttpsCallTree → List HttpsHop
  | [] => []
  | t :: ts => treeHops t ++ forestHops ts
termination_by structural ts => ts
end

/-- The attested sessions of a tree, in preorder. -/
def treeAttestations (t : HttpsCallTree) : List DecoAttestation :=
  (treeHops t).filterMap fun h => match h.kind with
    | .localComputation => none
    | _ => some h.attestation

/-- Bytes that flow from an opened response slot of one hop to an opened request slot of a
later one. -/
structure DataflowEdge where
  fromNode : Nat
  toNode : Nat
  srcSlot : Nat
  dstSlot : Nat
  bytes : ByteArray
  deriving DecidableEq

def slotOpenedAs (slots : List SpanSlot) (i : Nat) (bytes : ByteArray) : Bool :=
  match slots[i]? with
  | some (.opened b _) => decide (b = bytes) && decide (0 < bytes.size)
  | _ => false

def checkDataflowEdge (nodes : Array HttpsHop) (e : DataflowEdge) : Bool :=
  match nodes[e.fromNode]?, nodes[e.toNode]? with
  | some src, some dst => decide (e.fromNode < e.toNode) &&
      decide (src.kind ≠ .localComputation) && decide (dst.kind ≠ .localComputation) &&
      slotOpenedAs src.attestation.response.slots e.srcSlot e.bytes &&
      slotOpenedAs dst.attestation.request.slots e.dstSlot e.bytes
  | _, _ => false

/-- **The public verification of a call tree.** -/
def callTreeVerify (p : CallTreePolicy) (tree : HttpsCallTree) (expected : Hash256)
    (edges : List DataflowEdge) : Bool :=
  decide (treeRoot tree = expected) && checkTree p tree &&
  checkDecoTrace p.deco p.ledger (treeAttestations tree) &&
  edges.all (checkDataflowEdge (treeHops tree).toArray)

/-- **The verified root has one opening.** Every tree whose root is the verified root is the
verified tree, so it is admitted hop by hop and its sessions replay as one ledger trace; or the
node hash or a children tree collides. -/
theorem callTreeVerify_sound_or_collision (p : CallTreePolicy) (tree : HttpsCallTree)
    (expected : Hash256) (edges : List DataflowEdge) :
    callTreeVerify p tree expected edges = true →
    ∀ other : HttpsCallTree, treeRoot other = expected →
      (other = tree ∧ checkTree p other = true ∧
        ∃ final, ValidDecoTrace p.deco p.ledger (treeAttestations other) final) ∨
      CallTreeCollision := by
  intro h other ho
  simp only [callTreeVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hroot, htree⟩, htrace⟩, _⟩ := h
  rcases treeRoot_binds other tree (ho.trans hroot.symm) with he | hc
  · subst he
    exact Or.inl ⟨rfl, htree, (checkDecoTrace_iff _ _ _).1 htrace⟩
  · exact Or.inr hc

/-! ## The judge: public claim, private openings -/

structure CallTreeClaim where
  policy : CallTreePolicy
  tree : HttpsCallTree
  expectedRoot : Hash256
  requiredEdges : List DataflowEdge

/-- The prover's openings of one attested session. -/
structure HopOpening where
  request : List ByteArray
  response : List ByteArray

/-- The certificate: one opening per attested session, in preorder. -/
abbrev CallTreeWitness := List HopOpening

def checkOpenings : List DecoAttestation → List HopOpening → Bool
  | [], [] => true
  | a :: as, w :: ws =>
    checkOpening a.request w.request && checkOpening a.response w.response && checkOpenings as ws
  | _, _ => false

/-- A view and the real spans tell one story: the spans commit to the view's root, the head is
the real head, and the real body drives the JSON machine to the state the redacted body reaches. -/
def ViewParses (v : TranscriptView) (spans : List ByteArray) : Prop :=
  spanMerkleRoot cshakeHasher spanTag spans = v.root ∧
    ∃ head sibs body rest, v.slots = .opened head sibs :: body ∧ spans = head :: rest ∧
      specRunJson (realBytes rest) JState.init = specRunJson (viewBytes body) JState.init

def OpeningsParse : List DecoAttestation → List HopOpening → Prop
  | [], [] => True
  | a :: as, w :: ws =>
    ViewParses a.request w.request ∧ ViewParses a.response w.response ∧ OpeningsParse as ws
  | _, _ => False

theorem checkOpenings_parse : ∀ (as : List DecoAttestation) (ws : List HopOpening),
    checkOpenings as ws = true → OpeningsParse as ws
  | [], [], _ => trivial
  | [], _ :: _, h => by simp [checkOpenings] at h
  | _ :: _, [], h => by simp [checkOpenings] at h
  | a :: as, w :: ws, h => by
    simp only [checkOpenings, Bool.and_eq_true] at h
    exact ⟨checkOpening_parses h.1.1, checkOpening_parses h.1.2, checkOpenings_parse as ws h.2⟩

/-- **What an accepted call tree means.** The root binds this tree and no other; its sessions
replay as one ledger trace (authenticated, in policy, no nonce or intent twice); every hop is
admitted with its callee links; the required flows are opened on both sides; and every real
transcript parses as its redacted view. -/
structure CallTreeSpec (q : CallTreeClaim) (w : CallTreeWitness) : Prop where
  rooted : treeRoot q.tree = q.expectedRoot
  bound : ∀ t', treeRoot t' = q.expectedRoot → t' = q.tree ∨ CallTreeCollision
  trace : ∃ final, ValidDecoTrace q.policy.deco q.policy.ledger (treeAttestations q.tree) final
  hops : checkTree q.policy q.tree = true
  flows : ∀ e ∈ q.requiredEdges, checkDataflowEdge (treeHops q.tree).toArray e = true
  faithful : OpeningsParse (treeAttestations q.tree) w

inductive CallTreeRefusal where
  /-- the public verification fails: no opening can repair it -/
  | invalidExecution
  /-- the openings are not the committed transcripts, or cut an escape -/
  | unfaithfulOpening
  deriving DecidableEq

def callTreeCheck (q : CallTreeClaim) (w : CallTreeWitness) : Judge.Verdict CallTreeRefusal :=
  if callTreeVerify q.policy q.tree q.expectedRoot q.requiredEdges = false then
    .refused .invalidExecution []
  else if checkOpenings (treeAttestations q.tree) w = false then .refused .unfaithfulOpening []
  else .ok

theorem callTreeSpec_verify {q : CallTreeClaim} {w : CallTreeWitness} (h : CallTreeSpec q w) :
    callTreeVerify q.policy q.tree q.expectedRoot q.requiredEdges = true := by
  simp only [callTreeVerify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨h.rooted, h.hops⟩, (checkDecoTrace_iff _ _ _).2 h.trace⟩, h.flows⟩

/-- **The call tree judge.** A failed public verification refutes the claim under every opening;
completeness is claimed on the claims that have a faithful opening. -/
instance callTreeJudge : Obend.Judge CallTreeClaim CallTreeWitness where
  Clause := CallTreeRefusal
  Meaning := CallTreeSpec
  check _ := callTreeCheck
  sound := by
    intro _ q w h
    unfold callTreeCheck at h
    split at h
    · cases h
    · rename_i hv
      split at h
      · cases h
      · rename_i ho
        have hv' : callTreeVerify q.policy q.tree q.expectedRoot q.requiredEdges = true := by
          simpa using hv
        have hv2 := hv'
        simp only [callTreeVerify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv2
        obtain ⟨⟨⟨hroot, htree⟩, htrace⟩, hflows⟩ := hv2
        exact ⟨hroot, fun t' ht' => treeRoot_binds t' q.tree (ht'.trans hroot.symm),
          (checkDecoTrace_iff _ _ _).1 htrace, htree, hflows,
          checkOpenings_parse _ _ (by simpa using ho)⟩
  refutes k := decide (k = .invalidExecution)
  refuted := by
    intro _ q w k p h hk w' hm
    have hk' : k = .invalidExecution := of_decide_eq_true hk
    subst hk'
    unfold callTreeCheck at h
    split at h
    · rename_i hv
      rw [callTreeSpec_verify hm] at hv
      cases hv
    · split at h <;> cases h
  Fragment q := ∃ w, checkOpenings (treeAttestations q.tree) w = true
  complete := by
    rintro q ⟨w, hw⟩ ⟨_, hm⟩
    refine ⟨w, 0, ?_⟩
    show callTreeCheck q w = .ok
    simp [callTreeCheck, callTreeSpec_verify hm, hw]
  mono := by intro _ _ _ _ _ _; rfl

/-! ## The byte format `deco-calltree@1`

A claim and a witness are the hex of their canonical framing: `encList` of byte fields, lists as
nested `encList`, naturals as LEB128, tower elements as sixteen big-endian bytes. -/

def decNat (bs : List UInt8) : Option Nat :=
  match decInt bs with
  | some (n, []) => some n
  | _ => none

def decBytes (bs : List UInt8) : ByteArray := ⟨bs.toArray⟩

def decListOf {α : Type} (f : List UInt8 → Option α) (bs : List UInt8) : Option (List α) :=
  (decList bs).bind fun fields => fields.mapM f

def decTower (bs : List UInt8) : Option Tower128 :=
  if bs.length = 16 then some (blockOfBytes bs) else none

def decHash (bs : List UInt8) : Option Hash256 :=
  if h : (decBytes bs).size = 32 then some ⟨decBytes bs, h⟩ else none

def encBytesList (xs : List ByteArray) : List UInt8 := encList (xs.map fun x => x.data.toList)
def decBytesList (bs : List UInt8) : Option (List ByteArray) := decListOf (fun x => some (decBytes x)) bs

def decSlot (bs : List UInt8) : Option SpanSlot :=
  match decList bs with
  | some [[0], b, sibs] => (decBytesList sibs).map (.opened (decBytes b))
  | some [[1], m] => some (.masked (decBytes m))
  | _ => none

def decView (bs : List UInt8) : Option TranscriptView :=
  match decList bs with
  | some [root, slots] =>
    match decList root, decListOf decSlot slots with
    | some [count, top], some ss => (decNat count).map fun n => ⟨⟨n, decBytes top⟩, ss⟩
    | _, _ => none
  | _ => none

def decAttestation (bs : List UInt8) : Option DecoAttestation :=
  match decList bs with
  | some [host, notary, time, nonce, intent, req, resp, ct, len, tag] =>
    match decNat time, decView req, decView resp, decListOf decTower ct, decTower len, decTower tag with
    | some t, some q, some r, some c, some l, some g =>
      some ⟨⟨decBytes host, decBytes notary, t, decBytes nonce, decBytes intent⟩, q, r, c, l, g⟩
    | _, _, _, _, _, _ => none
  | _ => none

def decKind (bs : List UInt8) : Option HopKind :=
  match decNat bs with
  | some 0 => some .localComputation
  | some 1 => some .leafHttpsHop
  | some 2 => some .recursiveHttpsCallee
  | _ => none

mutual
def encTree : HttpsCallTree → List UInt8
  | .node h cs => encList [encInt (kindTag h.kind), encList (attestationFields h.attestation),
      encList (encForest cs)]
termination_by structural t => t
def encForest : List HttpsCallTree → List (List UInt8)
  | [] => []
  | t :: ts => encTree t :: encForest ts
termination_by structural ts => ts
end

/-- Decode a tree at a fuel (the byte count suffices: every level consumes a frame). -/
def decTree : Nat → List UInt8 → Option HttpsCallTree
  | 0, _ => none
  | fuel + 1, bs =>
    match decList bs with
    | some [kind, att, kids] =>
      match decKind kind, decAttestation att, decListOf (decTree fuel) kids with
      | some k, some a, some cs => some (.node ⟨k, a⟩ cs)
      | _, _, _ => none
    | _ => none

def encKey (kv : ByteArray × Tower128) : List UInt8 := encList [kv.1.data.toList, tagBytes kv.2]
def decKey (bs : List UInt8) : Option (ByteArray × Tower128) :=
  match decList bs with
  | some [n, k] => (decTower k).map fun key => (decBytes n, key)
  | _ => none

def encPolicy (p : CallTreePolicy) : List UInt8 :=
  encList [encList (p.deco.sessionKeys.map encKey), encBytesList p.deco.notaries,
    encBytesList p.deco.hosts, encInt p.deco.minTime, encInt p.deco.maxTime,
    encList (p.deco.secretRequestSlots.map encInt), encBytesList p.ledger.consumedNonces,
    encBytesList p.ledger.consumedIntents, encBytesList p.recorders,
    encInt (match p.localOp with | .identity => 0 | .digest => 1)]

def decPolicy (bs : List UInt8) : Option CallTreePolicy :=
  match decList bs with
  | some [keys, notaries, hosts, lo, hi, secret, nonces, intents, recorders, op] =>
    match decListOf decKey keys, decBytesList notaries, decBytesList hosts, decNat lo, decNat hi,
      decListOf decNat secret, decBytesList nonces, decBytesList intents, decBytesList recorders,
      decNat op with
    | some ks, some ns, some hs, some lo, some hi, some sec, some cn, some ci, some rec, some op =>
      some ⟨⟨ks, ns, hs, lo, hi, sec⟩, ⟨cn, ci⟩, rec, if op = 0 then .identity else .digest⟩
    | _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

def encEdge (e : DataflowEdge) : List UInt8 :=
  encList [encInt e.fromNode, encInt e.toNode, encInt e.srcSlot, encInt e.dstSlot,
    e.bytes.data.toList]

def decEdge (bs : List UInt8) : Option DataflowEdge :=
  match decList bs with
  | some [f, t, s, d, b] =>
    match decNat f, decNat t, decNat s, decNat d with
    | some f, some t, some s, some d => some ⟨f, t, s, d, decBytes b⟩
    | _, _, _, _ => none
  | _ => none

def encodeCallTreeClaim (q : CallTreeClaim) : String :=
  hexOf ⟨(encList [encPolicy q.policy, encTree q.tree, q.expectedRoot.val.data.toList,
    encList (q.requiredEdges.map encEdge)]).toArray⟩

def decodeCallTreeClaim (s : String) : Except String CallTreeClaim :=
  match unhex s with
  | .error e => .error e
  | .ok b =>
    match decList b.data.toList with
    | some [pol, tree, root, edges] =>
      match decPolicy pol, decTree tree.length tree, decHash root, decListOf decEdge edges with
      | some p, some t, some r, some es => .ok ⟨p, t, r, es⟩
      | _, _, _, _ => .error "deco-calltree@1: a field of the claim does not decode"
    | _ => .error "deco-calltree@1: a claim is four framed fields"

def encodeCallTreeWitness (w : CallTreeWitness) : String :=
  hexOf ⟨(encList (w.map fun o => encList [encBytesList o.request, encBytesList o.response])).toArray⟩

def decOpening (bs : List UInt8) : Option HopOpening :=
  match decList bs with
  | some [q, r] =>
    match decBytesList q, decBytesList r with
    | some q, some r => some ⟨q, r⟩
    | _, _ => none
  | _ => none

def decodeCallTreeWitness (s : String) : Except String CallTreeWitness :=
  match unhex s with
  | .error e => .error e
  | .ok b =>
    match decListOf decOpening b.data.toList with
    | some w => .ok w
    | none => .error "deco-calltree@1: the witness does not decode"

/-- The planted claim: a leaf hop with a child. -/
def plantedAttestation : DecoAttestation :=
  ⟨⟨ByteArray.empty, ByteArray.empty, 0, ByteArray.empty, ByteArray.empty⟩,
    ⟨⟨0, ByteArray.empty⟩, []⟩, ⟨⟨0, ByteArray.empty⟩, []⟩, [], towerZero 7, towerZero 7⟩

def plantedTree : HttpsCallTree :=
  .node ⟨.leafHttpsHop, plantedAttestation⟩ [.node ⟨.leafHttpsHop, plantedAttestation⟩ []]

def plantedClaim : CallTreeClaim :=
  ⟨⟨⟨[], [], [], 0, 0, []⟩, ⟨[], []⟩, [], .identity⟩, plantedTree, treeRoot plantedTree, []⟩

theorem plantedCallTree_refused :
    ∃ k p, callTreeJudge.check 0 plantedClaim ([] : CallTreeWitness) = .refused k p := by
  have h : checkTree plantedClaim.policy plantedClaim.tree = false := by
    simp [plantedClaim, plantedTree, checkTree, checkHop]
  refine ⟨.invalidExecution, [], ?_⟩
  show callTreeCheck plantedClaim [] = _
  simp [callTreeCheck, callTreeVerify, h]

/-- **The registered format** `deco-calltree@1`. Roots are cSHAKE256, which runs compiled. -/
@[expose] def decoCallTreeFormat : Judge.Format where
  name := "deco-calltree"
  version := "1"
  Obj := CallTreeClaim
  Cert := CallTreeWitness
  judge := callTreeJudge
  decodeObj := decodeCallTreeClaim
  decodeCert := decodeCallTreeWitness
  trust := .compiled
  regime := .attestable
  bad := (plantedClaim, [])
  badGrade := 0
  bad_refused := plantedCallTree_refused

end Obend.Judge.DecoAndCallTree
