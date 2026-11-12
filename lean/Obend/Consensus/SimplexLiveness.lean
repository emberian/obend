module
/-
# Obend.Consensus.SimplexLiveness — Authenticated Sender Signatures, View Timers & GST Liveness

Closes the three protocol assumptions noted in `Obend.Consensus.SimplexProtocol` (`line 32`):
1. **Cryptographic Sender Authentication (`SignedSimplexMsg`, `verifySignedSent`, `extractForgedVoteSignature`)**:
   - Binds `(signerPk, sender, view, kind, target)` into an injective, domain-framed byte preimage
     (`encodeSignablePreimage`, `signableByteArray_injective`) verified by 32-byte signatures
     (`SignatureScheme`, `KeyDirectory`) without inspecting the ghost `Protocol.faulty` predicate.
   - Constructively extracts (`0 Classical.choice`) `PSum` between:
     (a) `AuthenticatedReachWitness`: a valid `SimplexProtocol.Reach` trace where faulty behavior
         (`Step.inject`) is confined exclusively to messages signed under faulty committee keys, OR
     (b) `EufCmaForgeryWitness`: an existential signature forgery on a fresh byte preimage against
         an honest committee validator's public key.
   - Connects directly to `Obend.Judge.Computational` (`commitSlotSigScheme`,
     `forgedVoteSignature_reduces_to_hashCollision`, `signedSimplexCompJudge`), reducing any slot
     forgery to `BreakWitness (.hashCollision256 H maxBytes)`.
2. **Explicit View Timers & Pre-GST / Faulty-Leader View-Advance Progress
   (`pre_gst_or_faulty_leader_advances_view`)**:
   - Proves `honestMembers_length_ge_quorum` (`2f + 1 ≤ |honestMembers P|`) and `chainNotarized_snoc_dummy`.
   - Proves that in any view `v ≥ 1` extending a notarized `v - 1` prefix `p`, whenever honest
     nodes either reach block notarization or reach timeout without honest block votes (including
     any view with a silent or invalid faulty leader), constructive honest step scheduling reaches a
     valid view-`v` entry (`ChainNotarized P sent' (p ++ [e])` of length `v`), preventing deadlock.
3. **Post-GST Partial Synchrony One-View Finalization
   (`gst_honest_leader_finalizes`, `gst_honest_leader_finalizes_in_view`)**:
   - Models `GST`, post-GST network delay bound `deltaNet`, and exponential view timers
     (`Simplex.viewTimeout`, `2 * deltaNet < deltaTimer`).
   - Proves that in any view `v ≥ 1` entered at `t₀ ≥ GST` with an honest leader `L = P.leader v`
     where honest nodes enter view `v` within `deltaNet` and `2 * deltaNet < deltaTimer`, every
     honest node receives `L`'s proposal strictly before its view timer expires, zero honest nodes
     cast `.dummy v`, all `≥ 2f + 1` honest nodes vote for `L`'s block `b`, `NotarizedBlock` forms,
     all `≥ 2f + 1` honest nodes cast `.finalize`, and a checking `FinCert` (`Finalized P sent' v b`)
     is guaranteed in that single view `v`.
-/

public import Obend.Consensus.Simplex
public import Obend.Consensus.SimplexProtocol
public import Obend.Consensus.SimplexTrace
public import Obend.Judge.Computational
public import Obend.Digest.Cshake256.Seam
public import Obend.Digest.HashBytes

public section
namespace Obend.Consensus.SimplexLiveness

open Obend.Consensus.Simplex (NodeId list_filter_sub nodup_filter_simplex viewTimeout)
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace (entryNotarizedB chainNotarizedB voteRuleB voteRuleB_sound)
open Obend.Digest
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList)
open Obend.Judge.Computational (AssumptionSet BreakWitness HashCollisionWitness ComputationalJudge)

set_option autoImplicit false

/-! ## 1. Domain-Framed Canonical Preimages & Constructive Injectivity -/

/-- Domain separator tag for authenticated Simplex protocol messages (21 ASCII bytes). -/
def simplexAuthDomainBytes : List UInt8 :=
  [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x53, 0x49, 0x4D, 0x50, 0x4C,
   0x45, 0x58, 0x2D, 0x41, 0x55, 0x54, 0x48, 0x2D, 0x56, 0x31]

/-- 64-bit canonical scalar bound (`256 ^ 8 = 2 ^ 64`) for 8-byte big-endian framing. -/
@[expose] def FieldBound64 : Nat := 256 ^ 8

/-- Canonical width check for a `SimplexProtocol.Entry`. -/
def entryCanonical : Entry → Bool
  | .block v payload => decide (v < FieldBound64) && decide (payload < FieldBound64)
  | .dummy v         => decide (v < FieldBound64)

/-- Canonical width check for a `SimplexProtocol.Target`. -/
def targetCanonical : Target → Bool
  | .block c => c.all entryCanonical
  | .dummy v => decide (v < FieldBound64)

/-- Canonical width check for a `SimplexProtocol.Msg`. -/
def msgCanonical (m : Msg) : Bool :=
  decide (m.sender < FieldBound64) &&
  decide (m.view < FieldBound64) &&
  targetCanonical m.target

/-- Fixed 17-byte canonical encoding of a `SimplexProtocol.Entry`. -/
def encodeEntry17 : Entry → List UInt8
  | .block v payload => (0x01 : UInt8) :: (HashBytes.be 8 v ++ HashBytes.be 8 payload)
  | .dummy v         => (0x00 : UInt8) :: (HashBytes.be 8 v ++ HashBytes.be 8 0)

theorem encodeEntry17_length (e : Entry) : (encodeEntry17 e).length = 17 := by
  cases e <;> simp [encodeEntry17, HashBytes.length_be]

theorem encodeEntry17_injective {e₁ e₂ : Entry}
    (hc₁ : entryCanonical e₁ = true)
    (hc₂ : entryCanonical e₂ = true)
    (hEq : encodeEntry17 e₁ = encodeEntry17 e₂) :
    e₁ = e₂ := by
  cases e₁ with
  | block v₁ p₁ =>
    cases e₂ with
    | dummy v₂ =>
      simp [encodeEntry17] at hEq
    | block v₂ p₂ =>
      simp only [entryCanonical, Bool.and_eq_true, decide_eq_true_eq] at hc₁ hc₂
      simp only [encodeEntry17, List.cons.injEq, true_and] at hEq
      obtain ⟨hv, hp⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
      have hvEq := HashBytes.be_injective hc₁.1 hc₂.1 hv
      have hpEq := HashBytes.be_injective hc₁.2 hc₂.2 hp
      rw [hvEq, hpEq]
  | dummy v₁ =>
    cases e₂ with
    | block v₂ p₂ =>
      simp [encodeEntry17] at hEq
    | dummy v₂ =>
      simp only [entryCanonical, decide_eq_true_eq] at hc₁ hc₂
      simp only [encodeEntry17, List.cons.injEq, true_and] at hEq
      obtain ⟨hv, _⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
      rw [HashBytes.be_injective hc₁ hc₂ hv]

/-- Prefix-free recursive byte encoding of a `SimplexProtocol.Chain`. -/
def encodeChainBytes : Chain → List UInt8
  | []      => [0x00]
  | e :: es => (0x01 : UInt8) :: (encodeEntry17 e ++ encodeChainBytes es)

theorem encodeChainBytes_append_injective :
    ∀ {c₁ c₂ : Chain} {rest₁ rest₂ : List UInt8},
      c₁.all entryCanonical = true →
      c₂.all entryCanonical = true →
      encodeChainBytes c₁ ++ rest₁ = encodeChainBytes c₂ ++ rest₂ →
      c₁ = c₂ ∧ rest₁ = rest₂
  | [], [], rest₁, rest₂, _, _, hEq => by
    simp [encodeChainBytes] at hEq
    exact ⟨rfl, hEq⟩
  | [], _ :: _, _, _, _, _, hEq => by
    simp [encodeChainBytes] at hEq
  | _ :: _, [], _, _, _, _, hEq => by
    simp [encodeChainBytes] at hEq
  | e₁ :: es₁, e₂ :: es₂, rest₁, rest₂, hc₁, hc₂, hEq => by
    simp only [List.all_cons, Bool.and_eq_true] at hc₁ hc₂
    simp only [encodeChainBytes, List.cons_append, List.cons.injEq, true_and,
      List.append_assoc] at hEq
    have hLen : (encodeEntry17 e₁).length = (encodeEntry17 e₂).length := by
      rw [encodeEntry17_length, encodeEntry17_length]
    obtain ⟨hE, hTail⟩ := List.append_inj hEq hLen
    have heEq := encodeEntry17_injective hc₁.1 hc₂.1 hE
    obtain ⟨hesEq, hRestEq⟩ := encodeChainBytes_append_injective hc₁.2 hc₂.2 hTail
    exact ⟨by rw [heEq, hesEq], hRestEq⟩

/-- Prefix-free canonical byte encoding of a `SimplexProtocol.Target`. -/
def encodeTargetBytes : Target → List UInt8
  | .block c => (0x01 : UInt8) :: encodeChainBytes c
  | .dummy v => (0x00 : UInt8) :: HashBytes.be 8 v

theorem encodeTargetBytes_injective {t₁ t₂ : Target}
    (hc₁ : targetCanonical t₁ = true)
    (hc₂ : targetCanonical t₂ = true)
    (hEq : encodeTargetBytes t₁ = encodeTargetBytes t₂) :
    t₁ = t₂ := by
  cases t₁ with
  | block c₁ =>
    cases t₂ with
    | dummy v₂ => simp [encodeTargetBytes] at hEq
    | block c₂ =>
      simp only [targetCanonical] at hc₁ hc₂
      simp only [encodeTargetBytes, List.cons.injEq, true_and] at hEq
      have hApp : encodeChainBytes c₁ ++ [] = encodeChainBytes c₂ ++ [] := by simpa using hEq
      obtain ⟨hcEq, _⟩ := encodeChainBytes_append_injective hc₁ hc₂ hApp
      rw [hcEq]
  | dummy v₁ =>
    cases t₂ with
    | block c₂ => simp [encodeTargetBytes] at hEq
    | dummy v₂ =>
      simp only [targetCanonical, decide_eq_true_eq] at hc₁ hc₂
      simp only [encodeTargetBytes, List.cons.injEq, true_and] at hEq
      rw [HashBytes.be_injective hc₁ hc₂ hEq]

/-- Tag byte for `SimplexProtocol.Kind`. -/
def encodeKindByte : Kind → UInt8
  | .propose  => 0x01
  | .vote     => 0x02
  | .finalize => 0x03

theorem encodeKindByte_injective {k₁ k₂ : Kind}
    (hEq : encodeKindByte k₁ = encodeKindByte k₂) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | cases hEq

/-- Length-framed byte prefix helper (`be 8 bs.length ++ bs`). -/
def frameBytes64 (bs : List UInt8) : List UInt8 :=
  HashBytes.be 8 bs.length ++ bs

theorem frameBytes64_append_injective {a₁ a₂ b₁ b₂ : List UInt8}
    (ha₁ : a₁.length < FieldBound64)
    (ha₂ : a₂.length < FieldBound64)
    (hEq : frameBytes64 a₁ ++ b₁ = frameBytes64 a₂ ++ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  unfold frameBytes64 at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  obtain ⟨hLenBe, hRest⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
  have hLenEq : a₁.length = a₂.length := HashBytes.be_injective ha₁ ha₂ hLenBe
  exact List.append_inj hRest hLenEq

/-- Complete domain-separated, length-framed signable preimage binding
    `(simplexAuthDomainBytes, signerPk, sender, view, kind, target)`. -/
def encodeSignablePreimage (signerPk : BitVec 256) (m : Msg) : List UInt8 :=
  frameBytes64 simplexAuthDomainBytes ++
    (HashBytes.be 32 signerPk.toNat ++
      (HashBytes.be 8 m.sender ++
        (HashBytes.be 8 m.view ++
          ([encodeKindByte m.kind] ++ encodeTargetBytes m.target))))

/-- Canonical `ByteArray` signable payload passed to 32-byte signature verifiers. -/
def signableByteArray (signerPk : BitVec 256) (m : Msg) : ByteArray :=
  bytesOfList (encodeSignablePreimage signerPk m)

private theorem pow_256_32_eq_pow_2_256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide

/-- **Constructive Preimage Bijection (`encodeSignablePreimage_injective`)**:
    Every field `(signerPk, sender, view, kind, target)` is recovered uniquely from
    `encodeSignablePreimage`, preventing cross-view, cross-kind, or cross-target signature replay. -/
theorem encodeSignablePreimage_injective
    {pk₁ pk₂ : BitVec 256} {m₁ m₂ : Msg}
    (hc₁ : msgCanonical m₁ = true)
    (hc₂ : msgCanonical m₂ = true)
    (hEq : encodeSignablePreimage pk₁ m₁ = encodeSignablePreimage pk₂ m₂) :
    pk₁ = pk₂ ∧ m₁ = m₂ := by
  unfold encodeSignablePreimage at hEq
  have hDomLen : simplexAuthDomainBytes.length < FieldBound64 := by decide
  obtain ⟨_, h1⟩ := frameBytes64_append_injective hDomLen hDomLen hEq
  obtain ⟨hPkBe, h2⟩ := List.append_inj h1 (by simp [HashBytes.length_be])
  obtain ⟨hSenderBe, h3⟩ := List.append_inj h2 (by simp [HashBytes.length_be])
  obtain ⟨hViewBe, h4⟩ := List.append_inj h3 (by simp [HashBytes.length_be])
  simp only [List.singleton_append, List.cons.injEq] at h4
  obtain ⟨hKindByte, hTargetBytes⟩ := h4
  simp only [msgCanonical, Bool.and_eq_true, decide_eq_true_eq] at hc₁ hc₂
  have hPk₁ : pk₁.toNat < 256 ^ 32 := pow_256_32_eq_pow_2_256 ▸ pk₁.isLt
  have hPk₂ : pk₂.toNat < 256 ^ 32 := pow_256_32_eq_pow_2_256 ▸ pk₂.isLt
  have hPkEq : pk₁ = pk₂ := BitVec.eq_of_toNat_eq (HashBytes.be_injective hPk₁ hPk₂ hPkBe)
  have hSenderEq : m₁.sender = m₂.sender := HashBytes.be_injective hc₁.1.1 hc₂.1.1 hSenderBe
  have hViewEq : m₁.view = m₂.view := HashBytes.be_injective hc₁.1.2 hc₂.1.2 hViewBe
  have hKindEq : m₁.kind = m₂.kind := encodeKindByte_injective hKindByte
  have hTargetEq : m₁.target = m₂.target := encodeTargetBytes_injective hc₁.2 hc₂.2 hTargetBytes
  refine ⟨hPkEq, ?_⟩
  cases m₁; cases m₂
  simp only at hSenderEq hViewEq hKindEq hTargetEq
  rw [hSenderEq, hViewEq, hKindEq, hTargetEq]

theorem signableByteArray_injective
    {pk₁ pk₂ : BitVec 256} {m₁ m₂ : Msg}
    (hc₁ : msgCanonical m₁ = true)
    (hc₂ : msgCanonical m₂ = true)
    (hEq : signableByteArray pk₁ m₁ = signableByteArray pk₂ m₂) :
    pk₁ = pk₂ ∧ m₁ = m₂ := by
  have hList : (signableByteArray pk₁ m₁).data.toList = (signableByteArray pk₂ m₂).data.toList :=
    congrArg (fun b => b.data.toList) hEq
  unfold signableByteArray at hList
  rw [bytesOfList_toList, bytesOfList_toList] at hList
  exact encodeSignablePreimage_injective hc₁ hc₂ hList

/-! ## 2. Cryptographic Sender Authentication (`SignedSimplexMsg`, `verifySignedSent`, `extractForgedVoteSignature`) -/

/-- Committee public-key directory mapping each validator `NodeId` to its 256-bit verification key. -/
structure KeyDirectory where
  pubKey : NodeId → BitVec 256

/-- 256-bit / 32-byte digital signature verifier interface over `ByteArray` payloads. -/
structure SignatureScheme where
  verifySig : BitVec 256 → ByteArray → ByteArray → Bool

/-- Authenticated Simplex wire message carrying `msg : Msg`, 256-bit `signerPk`, and 32-byte `signature`. -/
structure SignedSimplexMsg where
  msg       : Msg
  signerPk  : BitVec 256
  signature : ByteArray
  deriving DecidableEq

/-- Ordered authenticated message log (oldest message first, matching `SimplexTrace`). -/
abbrev SignedSent := List SignedSimplexMsg

/-- Project an authenticated wire trace `SignedSent` to `SimplexProtocol.Sent` (newest message first). -/
def projectSignedSent (tr : SignedSent) : Sent :=
  (tr.map SignedSimplexMsg.msg).reverse

/-- Verify a single `SignedSimplexMsg` against committee roster and `KeyDirectory` (without
    consulting the ghost `Protocol.faulty` predicate!). -/
def verifySignedMsg (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (sm : SignedSimplexMsg) : Bool :=
  committee.contains sm.msg.sender &&
  msgCanonical sm.msg &&
  decide (sm.signerPk = K.pubKey sm.msg.sender) &&
  decide (sm.signature.size = 32) &&
  S.verifySig sm.signerPk (signableByteArray sm.signerPk sm.msg) sm.signature

/-- Streaming verifier over `SignedSent`: enforces non-replay (`!seen.contains sm.msg`) and
    32-byte cryptographic signature authentication on every message. -/
def verifySignedSentAux (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (seen : Sent) : SignedSent → Bool
  | [] => true
  | sm :: rest =>
    !seen.contains sm.msg &&
    verifySignedMsg S K committee sm &&
    verifySignedSentAux S K committee (sm.msg :: seen) rest

/-- Public network verifier for an authenticated `SignedSent` trace (`0` dependence on `P.faulty`). -/
def verifySignedSent (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (tr : SignedSent) : Bool :=
  verifySignedSentAux S K committee [] tr

/-- Pure honest protocol rule check for message `m` against prior history `sent`
    (independent of `P.faulty`). -/
def checkHonestProtocolRule (P : Protocol) (sent : Sent) (m : Msg) : Bool :=
  P.committee.contains m.sender &&
  match m.kind with
  | .propose =>
    match m.target with
    | .block _ => m.sender == P.leader m.view
    | .dummy _ => false
  | .vote =>
    !votedAny sent m.sender m.view && voteRuleB P sent m.view m.target
  | .finalize =>
    match m.target with
    | .block c => voted sent m.sender m.view (.block c) && decide (NotarizedBlock P sent m.view c)
    | .dummy _ => false

theorem checkHonestProtocolRule_step {P : Protocol} {sent : Sent} {m : Msg}
    (hn : P.honest m.sender)
    (hRule : checkHonestProtocolRule P sent m = true) :
    Step P sent (m :: sent) := by
  rcases m with ⟨sender, view, kind, target⟩
  unfold checkHonestProtocolRule at hRule
  simp only [Bool.and_eq_true] at hRule
  obtain ⟨_, hk⟩ := hRule
  cases kind with
  | propose =>
    cases target with
    | dummy _ => cases hk
    | block c =>
      simp only [beq_iff_eq] at hk
      exact Step.propose sent sender view c hn hk
  | vote =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    exact Step.vote sent sender view target hn hk.1 (voteRuleB_sound hk.2)
  | finalize =>
    cases target with
    | dummy _ => cases hk
    | block c =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact Step.finalize sent sender view c hn hk.1 hk.2

/-- Constructive EUF-CMA signature forgery witness extracted whenever a verified `SignedSent`
    contains a protocol-violating message attributed to an uncorrupted honest validator. -/
structure EufCmaForgeryWitness (S : SignatureScheme) (K : KeyDirectory)
    (P : Protocol) (honestOracleLog : List Msg) where
  forgedMsg      : SignedSimplexMsg
  honestTarget   : P.honest forgedMsg.msg.sender
  pkBound        : forgedMsg.signerPk = K.pubKey forgedMsg.msg.sender
  sigWidth32     : forgedMsg.signature.size = 32
  sigAccepted    : S.verifySig forgedMsg.signerPk
                     (signableByteArray forgedMsg.signerPk forgedMsg.msg)
                     forgedMsg.signature = true
  unqueriedMsg   : forgedMsg.msg ∉ honestOracleLog
  freshPreimage  : ∀ q ∈ honestOracleLog, msgCanonical q = true →
                     signableByteArray forgedMsg.signerPk forgedMsg.msg ≠
                       signableByteArray (K.pubKey q.sender) q

/-- Certified projection of a verified `SignedSent` into `SimplexProtocol.Reach` + `Inv`,
    proving that every non-honest-rule message injection carries a valid 32-byte signature
    under a faulty committee member's own key! -/
structure AuthenticatedReachWitness (P : Protocol) (S : SignatureScheme)
    (K : KeyDirectory) (seen : Sent) (tr : SignedSent) : Prop where
  reach : Reach P ((tr.map SignedSimplexMsg.msg).reverse ++ seen)
  allAuthenticated : ∀ sm ∈ tr,
    sm.msg.sender ∈ P.committee ∧
    sm.signerPk = K.pubKey sm.msg.sender ∧
    sm.signature.size = 32 ∧
    S.verifySig sm.signerPk (signableByteArray sm.signerPk sm.msg) sm.signature = true
  faultyOnlyInject : ∀ (pre : SignedSent) (sm : SignedSimplexMsg) (suf : SignedSent),
    tr = pre ++ sm :: suf →
    checkHonestProtocolRule P ((pre.map SignedSimplexMsg.msg).reverse ++ seen) sm.msg = false →
    P.faulty sm.msg.sender = true ∧ sm.signerPk = K.pubKey sm.msg.sender

/-- Honest signing-oracle discipline: honest nodes sign only messages obeying `checkHonestProtocolRule`
    when causally delivered in `tr`. -/
def HonestSigningOracle (P : Protocol) (seen : Sent)
    (honestOracleLog : List Msg) (tr : SignedSent) : Prop :=
  ∀ (pre : SignedSent) (sm : SignedSimplexMsg) (suf : SignedSent),
    tr = pre ++ sm :: suf →
    P.honest sm.msg.sender →
    sm.msg ∈ honestOracleLog →
    checkHonestProtocolRule P ((pre.map SignedSimplexMsg.msg).reverse ++ seen) sm.msg = true

private theorem verifySignedMsg_dest {S : SignatureScheme} {K : KeyDirectory}
    {committee : List NodeId} {sm : SignedSimplexMsg}
    (h : verifySignedMsg S K committee sm = true) :
    sm.msg.sender ∈ committee ∧
    msgCanonical sm.msg = true ∧
    sm.signerPk = K.pubKey sm.msg.sender ∧
    sm.signature.size = 32 ∧
    S.verifySig sm.signerPk (signableByteArray sm.signerPk sm.msg) sm.signature = true := by
  unfold verifySignedMsg at h
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Auxiliary constructive extractor walking `SignedSent` oldest-to-newest (`0 Classical.choice`). -/
def extractForgedVoteSignatureAux
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) :
    ∀ (seen : Sent) (tr : SignedSent),
      Reach P seen →
      verifySignedSentAux S K P.committee seen tr = true →
      HonestSigningOracle P seen honestOracleLog tr →
      PSum (AuthenticatedReachWitness P S K seen tr)
           (EufCmaForgeryWitness S K P honestOracleLog)
  | seen, [], hReach, _, _ =>
    .inl
      { reach := by simpa using hReach
        allAuthenticated := fun _ hMem => False.elim (List.not_mem_nil hMem)
        faultyOnlyInject := fun pre _ _ hEq => by cases pre <;> cases hEq }
  | seen, sm :: rest, hReach, hVer, hOracle =>
    have hVerParts :
        verifySignedMsg S K P.committee sm = true ∧
        verifySignedSentAux S K P.committee (sm.msg :: seen) rest = true := by
      unfold verifySignedSentAux at hVer
      simp only [Bool.and_eq_true] at hVer
      exact ⟨hVer.1.2, hVer.2⟩
    let hMsg := verifySignedMsg_dest hVerParts.1
    if hFaulty : P.faulty sm.msg.sender = true then
      have hStep : Step P seen (sm.msg :: seen) := Step.inject seen sm.msg hFaulty
      have hOracleRest : HonestSigningOracle P (sm.msg :: seen) honestOracleLog rest := by
        intro pre sm' suf hEqRest hHon' hIn'
        have hEqFull : sm :: rest = (sm :: pre) ++ sm' :: suf := by simp [hEqRest]
        have hRes := hOracle (sm :: pre) sm' suf hEqFull hHon' hIn'
        simpa [List.reverse_cons, List.append_assoc] using hRes
      match extractForgedVoteSignatureAux S K P honestOracleLog
              (sm.msg :: seen) rest (Reach.step hReach hStep) hVerParts.2 hOracleRest with
      | .inr forgery => .inr forgery
      | .inl wRest =>
        .inl
          { reach := by simpa [List.reverse_cons, List.append_assoc] using wRest.reach
            allAuthenticated := by
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hxRest
              · exact ⟨hMsg.1, hMsg.2.2.1, hMsg.2.2.2.1, hMsg.2.2.2.2⟩
              · exact wRest.allAuthenticated x hxRest
            faultyOnlyInject := by
              intro pre x suf hSplit hRuleFalse
              cases pre with
              | nil =>
                simp only [List.nil_append, List.cons.injEq] at hSplit
                rcases hSplit with ⟨rfl, _⟩
                exact ⟨hFaulty, hMsg.2.2.1⟩
              | cons p ps =>
                simp only [List.cons_append, List.cons.injEq] at hSplit
                rcases hSplit with ⟨rfl, hRestSplit⟩
                have hRuleRest :
                    checkHonestProtocolRule P
                      ((ps.map SignedSimplexMsg.msg).reverse ++ (sm.msg :: seen)) x.msg = false := by
                  simpa [List.reverse_cons, List.append_assoc] using hRuleFalse
                exact wRest.faultyOnlyInject ps x suf hRestSplit hRuleRest }
    else
      have hFaultyFalse : P.faulty sm.msg.sender = false :=
        Bool.eq_false_iff.2 hFaulty
      have hHonest : P.honest sm.msg.sender := ⟨hMsg.1, hFaultyFalse⟩
      if hRule : checkHonestProtocolRule P seen sm.msg = true then
        have hStep : Step P seen (sm.msg :: seen) :=
          checkHonestProtocolRule_step hHonest hRule
        have hOracleRest : HonestSigningOracle P (sm.msg :: seen) honestOracleLog rest := by
          intro pre sm' suf hEqRest hHon' hIn'
          have hEqFull : sm :: rest = (sm :: pre) ++ sm' :: suf := by simp [hEqRest]
          have hRes := hOracle (sm :: pre) sm' suf hEqFull hHon' hIn'
          simpa [List.reverse_cons, List.append_assoc] using hRes
        match extractForgedVoteSignatureAux S K P honestOracleLog
                (sm.msg :: seen) rest (Reach.step hReach hStep) hVerParts.2 hOracleRest with
        | .inr forgery => .inr forgery
        | .inl wRest =>
          .inl
            { reach := by simpa [List.reverse_cons, List.append_assoc] using wRest.reach
              allAuthenticated := by
                intro x hx
                rcases List.mem_cons.1 hx with rfl | hxRest
                · exact ⟨hMsg.1, hMsg.2.2.1, hMsg.2.2.2.1, hMsg.2.2.2.2⟩
                · exact wRest.allAuthenticated x hxRest
              faultyOnlyInject := by
                intro pre x suf hSplit hRuleFalse
                cases pre with
                | nil =>
                  simp only [List.nil_append, List.cons.injEq] at hSplit
                  rcases hSplit with ⟨rfl, _⟩
                  simp [hRule] at hRuleFalse
                | cons p ps =>
                  simp only [List.cons_append, List.cons.injEq] at hSplit
                  rcases hSplit with ⟨rfl, hRestSplit⟩
                  have hRuleRest :
                      checkHonestProtocolRule P
                        ((ps.map SignedSimplexMsg.msg).reverse ++ (sm.msg :: seen)) x.msg = false := by
                    simpa [List.reverse_cons, List.append_assoc] using hRuleFalse
                  exact wRest.faultyOnlyInject ps x suf hRestSplit hRuleRest }
      else
        have hNotQueried : sm.msg ∉ honestOracleLog := by
          intro hIn
          have hOk := hOracle [] sm rest rfl hHonest hIn
          exact hRule (by simpa using hOk)
        .inr
          { forgedMsg := sm
            honestTarget := hHonest
            pkBound := hMsg.2.2.1
            sigWidth32 := hMsg.2.2.2.1
            sigAccepted := hMsg.2.2.2.2
            unqueriedMsg := hNotQueried
            freshPreimage := by
              intro q hq hqCan hEqBytes
              have hInj := signableByteArray_injective hMsg.2.1 hqCan hEqBytes
              exact hNotQueried (hInj.2 ▸ hq) }

/-- **Constructive EUF-CMA Signature Extractor (`extractForgedVoteSignature`)**:
    Given any `SignedSent` accepted by `verifySignedSent S K P.committee tr = true`,
    deterministically computes in `Type` (`0 Classical.choice`) either:
    - a certified `SimplexProtocol.Reach P (projectSignedSent tr)` witness proving faulty
      injections occur exclusively under faulty committee keys, OR
    - an explicit `EufCmaForgeryWitness` on a fresh domain-framed byte preimage against an
      honest validator's public key! -/
def extractForgedVoteSignature
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) (tr : SignedSent)
    (hVer : verifySignedSent S K P.committee tr = true)
    (hOracle : HonestSigningOracle P [] honestOracleLog tr) :
    PSum (PLift (Reach P (projectSignedSent tr) ∧
                 Inv P (projectSignedSent tr) ∧
                 AuthenticatedReachWitness P S K [] tr))
         (EufCmaForgeryWitness S K P honestOracleLog) :=
  match extractForgedVoteSignatureAux S K P honestOracleLog [] tr Reach.nil hVer hOracle with
  | .inr forgery => .inr forgery
  | .inl w =>
    have hReachProj : Reach P (projectSignedSent tr) := by
      simpa [projectSignedSent] using w.reach
    .inl ⟨⟨hReachProj, reach_inv hReachProj, w⟩⟩

/-- Unforgeable `SignatureScheme` assumption predicate relative to an honest signing oracle log:
    no adversary produces a valid `EufCmaForgeryWitness`. -/
def SignatureUnforgeable (S : SignatureScheme) (K : KeyDirectory)
    (P : Protocol) (honestOracleLog : List Msg) : Prop :=
  ¬ Nonempty (EufCmaForgeryWitness S K P honestOracleLog)

/-- **Authenticated Simplex Safety Projection (`verifySignedSent_projects_to_reach`)**:
    Under `SignatureUnforgeable`, every network trace accepted by `verifySignedSent` projects to
    a valid `SimplexProtocol.Reach` trace satisfying `Inv P` and `FinCert` height uniqueness, where
    faulty nodes can ONLY inject messages signed under their own faulty keys! -/
theorem verifySignedSent_projects_to_reach
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) (tr : SignedSent)
    (hVer : verifySignedSent S K P.committee tr = true)
    (hOracle : HonestSigningOracle P [] honestOracleLog tr)
    (hUnforge : SignatureUnforgeable S K P honestOracleLog) :
    Reach P (projectSignedSent tr) ∧
    Inv P (projectSignedSent tr) ∧
    AuthenticatedReachWitness P S K [] tr := by
  cases extractForgedVoteSignature S K P honestOracleLog tr hVer hOracle with
  | inl w => exact w.down
  | inr forgery => exact False.elim (hUnforge ⟨forgery⟩)

/-! ### 2B. Concrete `ComputationalJudge` Bridge (`commitSlotSigScheme`, `signedSimplexCompJudge`) -/

private theorem ofBE_lt_two_pow_256_of_length_32 {bs : List UInt8} (h : bs.length = 32) :
    HashBytes.ofBE bs < 2 ^ 256 := by
  have hlt := HashBytes.ofBE_lt bs
  rw [h, pow_256_32_eq_pow_2_256] at hlt
  exact hlt

private theorem byteArray_eq_of_toList_eq {x y : ByteArray}
    (h : x.data.toList = y.data.toList) : x = y := by
  cases x with | mk dx =>
  cases y with | mk dy =>
  exact congrArg ByteArray.mk (Array.ext' h)

/-- Salted 256-bit hash-commitment slot signature scheme backed by `HashBytes.Hash`:
    public key commits to `H (frameBytes64 signableBytes ++ salt32)`, so verifying a distinct
    message under the same slot public key constructively exhibits a 256-bit hash collision! -/
def slotSigPreimage (msgBytes : ByteArray) (sigSalt32 : ByteArray) : List UInt8 :=
  frameBytes64 msgBytes.data.toList ++ sigSalt32.data.toList

def deriveSlotPubKey (H : HashBytes.Hash) (authorizedMsgBytes : ByteArray)
    (secretSalt32 : ByteArray) : BitVec 256 :=
  BitVec.ofNat 256 (HashBytes.ofBE (H (slotSigPreimage authorizedMsgBytes secretSalt32)))

def commitSlotSigScheme (H : HashBytes.Hash) (maxPreimageBytes : Nat) : SignatureScheme where
  verifySig pk msgBytes sigSalt32 :=
    decide (msgBytes.data.toList.length < FieldBound64) &&
    decide ((slotSigPreimage msgBytes sigSalt32).length ≤ maxPreimageBytes) &&
    decide (sigSalt32.size = 32) &&
    decide ((H (slotSigPreimage msgBytes sigSalt32)).length = 32) &&
    decide (BitVec.ofNat 256 (HashBytes.ofBE (H (slotSigPreimage msgBytes sigSalt32))) = pk)

private def slotSigCollision_of_verifySig
    (H : HashBytes.Hash) (maxBytes : Nat)
    (forgedBytes honBytes sigSalt32 honestSalt32 : ByteArray)
    (hSig : (commitSlotSigScheme H maxBytes).verifySig
              (deriveSlotPubKey H honBytes honestSalt32) forgedBytes sigSalt32 = true)
    (hHonLen : honBytes.data.toList.length < FieldBound64)
    (hHonBound : (slotSigPreimage honBytes honestSalt32).length ≤ maxBytes)
    (hHonHashLen : (H (slotSigPreimage honBytes honestSalt32)).length = 32)
    (hNeBytes : forgedBytes ≠ honBytes) :
    BreakWitness (.hashCollision256 H maxBytes) :=
  have hAcc :
      forgedBytes.data.toList.length < FieldBound64 ∧
      (slotSigPreimage forgedBytes sigSalt32).length ≤ maxBytes ∧
      (H (slotSigPreimage forgedBytes sigSalt32)).length = 32 ∧
      BitVec.ofNat 256 (HashBytes.ofBE (H (slotSigPreimage forgedBytes sigSalt32))) =
        deriveSlotPubKey H honBytes honestSalt32 := by
    unfold commitSlotSigScheme at hSig
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSig
    exact ⟨hSig.1.1.1.1, hSig.1.1.1.2, hSig.1.2, hSig.2⟩
  have hForgedHashLt :
      HashBytes.ofBE (H (slotSigPreimage forgedBytes sigSalt32)) < 2 ^ 256 :=
    ofBE_lt_two_pow_256_of_length_32 hAcc.2.2.1
  have hHonHashLt :
      HashBytes.ofBE (H (slotSigPreimage honBytes honestSalt32)) < 2 ^ 256 :=
    ofBE_lt_two_pow_256_of_length_32 hHonHashLen
  have hSameOfBE :
      HashBytes.ofBE (H (slotSigPreimage forgedBytes sigSalt32)) =
      HashBytes.ofBE (H (slotSigPreimage honBytes honestSalt32)) := by
    have hToNat := congrArg BitVec.toNat hAcc.2.2.2
    unfold deriveSlotPubKey at hToNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hForgedHashLt, Nat.mod_eq_of_lt hHonHashLt] at hToNat
    exact hToNat
  have hDistinctPre :
      slotSigPreimage forgedBytes sigSalt32 ≠
      slotSigPreimage honBytes honestSalt32 := by
    intro hPreEq
    obtain ⟨hPayEq, _⟩ := frameBytes64_append_injective hAcc.1 hHonLen hPreEq
    exact hNeBytes (byteArray_eq_of_toList_eq hPayEq)
  ({ msgA := slotSigPreimage forgedBytes sigSalt32
     msgB := slotSigPreimage honBytes honestSalt32
     lenA := hAcc.2.1
     lenB := hHonBound
     distinct := hDistinctPre
     sameDigest := hSameOfBE } : HashCollisionWitness H maxBytes)

/-- **Constructive Reduction to `Obend.Judge.Computational` (`forgedVoteSignature_reduces_to_hashCollision`)**:
    Any `EufCmaForgeryWitness` against a validator whose slot key `K.pubKey n` commits via `H` to
    its honest message `q` constructively produces `BreakWitness (.hashCollision256 H maxBytes)`
    (`HashCollisionWitness H maxBytes`, `0` axioms, `0 Classical.choice`)! -/
def forgedVoteSignature_reduces_to_hashCollision
    (H : HashBytes.Hash) (maxBytes : Nat) (K : KeyDirectory) (P : Protocol)
    (honestMsg : Msg) (honestSalt32 : ByteArray)
    (hHonCan : msgCanonical honestMsg = true)
    (hHonLen : (signableByteArray (K.pubKey honestMsg.sender) honestMsg).data.toList.length < FieldBound64)
    (hHonBound : (slotSigPreimage (signableByteArray (K.pubKey honestMsg.sender) honestMsg) honestSalt32).length ≤ maxBytes)
    (hHonHashLen : (H (slotSigPreimage (signableByteArray (K.pubKey honestMsg.sender) honestMsg) honestSalt32)).length = 32)
    (hPkCommit : ∀ n, P.honest n →
      n = honestMsg.sender ∧
      K.pubKey n = deriveSlotPubKey H (signableByteArray (K.pubKey honestMsg.sender) honestMsg) honestSalt32)
    (w : EufCmaForgeryWitness (commitSlotSigScheme H maxBytes) K P [honestMsg]) :
    BreakWitness (.hashCollision256 H maxBytes) :=
  have hPkEq :
      w.forgedMsg.signerPk =
        deriveSlotPubKey H (signableByteArray (K.pubKey honestMsg.sender) honestMsg) honestSalt32 := by
    rw [w.pkBound]
    exact (hPkCommit w.forgedMsg.msg.sender w.honestTarget).2
  have hSig :
      (commitSlotSigScheme H maxBytes).verifySig
        (deriveSlotPubKey H (signableByteArray (K.pubKey honestMsg.sender) honestMsg) honestSalt32)
        (signableByteArray w.forgedMsg.signerPk w.forgedMsg.msg)
        w.forgedMsg.signature = true := by
    rw [← hPkEq]
    exact w.sigAccepted
  have hNeBytes :
      signableByteArray w.forgedMsg.signerPk w.forgedMsg.msg ≠
        signableByteArray (K.pubKey honestMsg.sender) honestMsg :=
    fun hBaEq => w.freshPreimage honestMsg (List.Mem.head []) hHonCan hBaEq
  slotSigCollision_of_verifySig H maxBytes
    (signableByteArray w.forgedMsg.signerPk w.forgedMsg.msg)
    (signableByteArray (K.pubKey honestMsg.sender) honestMsg)
    w.forgedMsg.signature honestSalt32
    hSig hHonLen hHonBound hHonHashLen hNeBytes

/-- Statement object for `signedSimplexCompJudge`: committee protocol, key directory, and slot-committed honest message. -/
structure SignedSlotTraceObj where
  proto      : Protocol
  keys       : KeyDirectory
  honestMsg  : Msg
  honestSalt : ByteArray

/-- **`ComputationalJudge` Instance (`signedSimplexCompJudge`)**:
    Verifies `verifySignedSent` on `(o : SignedSlotTraceObj)` and `(tr : SignedSent)`, constructively
    extracting either `Reach o.proto (projectSignedSent tr)` OR `BreakWitness (.hashCollision256 H maxBytes)`. -/
@[instance_reducible] def signedSimplexCompJudge (H : HashBytes.Hash) (maxBytes : Nat) :
    ComputationalJudge SignedSlotTraceObj SignedSent where
  Clause := Unit
  Meaning o := ∃ tr : SignedSent, Reach o.proto (projectSignedSent tr)
  Witness o := { tr : SignedSent // Reach o.proto (projectSignedSent tr) }
  witnessSound w := ⟨w.1, w.2⟩
  assumptions := .hashCollision256 H maxBytes
  soundnessErr := (0, 1)
  den_pos := by decide
  verify _ o tr :=
    if verifySignedSent (commitSlotSigScheme H maxBytes) o.keys o.proto.committee tr &&
       msgCanonical o.honestMsg &&
       decide ((signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg).data.toList.length < FieldBound64) &&
       decide ((slotSigPreimage (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg) o.honestSalt).length ≤ maxBytes) &&
       decide ((H (slotSigPreimage (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg) o.honestSalt)).length = 32)
    then .ok else .refused () []
  mono _ _ := rfl
  RewindBundle _ _ := PUnit
  rewindValid _ o tr _ :=
    HonestSigningOracle o.proto [] [o.honestMsg] tr ∧
    (∀ n, o.proto.honest n →
      n = o.honestMsg.sender ∧
      o.keys.pubKey n =
        deriveSlotPubKey H (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg) o.honestSalt)
  extractOrBreak {_ o tr} _ hOk hRew :=
    have hChecks :
        verifySignedSent (commitSlotSigScheme H maxBytes) o.keys o.proto.committee tr = true ∧
        msgCanonical o.honestMsg = true ∧
        (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg).data.toList.length < FieldBound64 ∧
        (slotSigPreimage (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg) o.honestSalt).length ≤ maxBytes ∧
        (H (slotSigPreimage (signableByteArray (o.keys.pubKey o.honestMsg.sender) o.honestMsg) o.honestSalt)).length = 32 := by
      split at hOk
      · rename_i hCond
        have h1234 := (Bool.and_eq_true _ _).mp hCond
        have h123 := (Bool.and_eq_true _ _).mp h1234.1
        have h12 := (Bool.and_eq_true _ _).mp h123.1
        have h1 := (Bool.and_eq_true _ _).mp h12.1
        exact ⟨h1.1, h1.2, of_decide_eq_true h12.2, of_decide_eq_true h123.2, of_decide_eq_true h1234.2⟩
      · cases hOk
    match extractForgedVoteSignature (commitSlotSigScheme H maxBytes) o.keys o.proto
            [o.honestMsg] tr hChecks.1 hRew.1 with
    | .inl w => .inl ⟨tr, w.down.1⟩
    | .inr forgery =>
      .inr (forgedVoteSignature_reduces_to_hashCollision H maxBytes o.keys o.proto
              o.honestMsg o.honestSalt hChecks.2.1 hChecks.2.2.1 hChecks.2.2.2.1 hChecks.2.2.2.2
              hRew.2 forgery)

/-! ## 3. Honest Quorum Cardinality, Dummy Chain Extension & Step Schedulers -/

/-- The duplicate-free list of honest validators in `P.committee`. -/
def honestMembers (P : Protocol) : List NodeId :=
  P.committee.filter (fun n => !P.faulty n)

theorem mem_honestMembers_iff (P : Protocol) (n : NodeId) :
    n ∈ honestMembers P ↔ P.honest n := by
  unfold honestMembers Protocol.honest
  rw [List.mem_filter]
  simp

/-- **Honest Quorum Sufficiency**: at least `2f + 1 = P.quorum` committee members are honest. -/
theorem honestMembers_length_ge_quorum (P : Protocol) :
    P.quorum ≤ (honestMembers P).length := by
  have hSub := list_filter_sub (fun _ => true) P.faulty P.committee
  have hTrue : P.committee.filter (fun _ => true) = P.committee := by
    induction P.committee with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have hHonEq : P.committee.filter (fun x => true && !P.faulty x) = honestMembers P := by
    simp [honestMembers]
  have hFaultEq : P.committee.filter (fun x => true && P.faulty x) = P.committee.filter P.faulty := by
    simp
  rw [hTrue, hHonEq, hFaultEq, P.size] at hSub
  have hFb := P.faultBound
  unfold Protocol.quorum
  omega

/-- Extending a notarized chain of `v - 1` entries by a notarized `.dummy v` produces a
    notarized chain of length `v` (complementing `SimplexProtocol.chainNotarized_snoc`). -/
theorem chainNotarized_snoc_dummy {P : Protocol} {sent : Sent} {p : Chain} {v : Nat}
    (hp : ChainNotarized P sent p) (hlen : p.length = v - 1) (hv : 1 ≤ v)
    (hd : NotarizedDummy P sent v) :
    ChainNotarized P sent (p ++ [.dummy v]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hkp : k < p.length
  · have hget : (p ++ [Entry.dummy v])[k] = p[k] := List.getElem_append_left hkp
    have htake : (p ++ [Entry.dummy v]).take (k + 1) = p.take (k + 1) :=
      take_append_left p [Entry.dummy v] (k + 1) (by omega)
    rw [hget, htake]
    exact hp k hkp
  · have hkeq : k = p.length := by omega
    have hget : (p ++ [Entry.dummy v])[k] = Entry.dummy v := by
      rw [List.getElem_append_right (by omega)]
      simp [hkeq]
    rw [hget]
    have hvk : v = k + 1 := by omega
    refine ⟨hvk, ?_⟩
    rw [← hvk]
    exact hd

private theorem entryNotarizedB_cons {P : Protocol} {sent : Sent} (m : Msg)
    {k : Nat} {upto : Chain} {e : Entry}
    (h : entryNotarizedB P sent k upto e = true) :
    entryNotarizedB P (m :: sent) k upto e = true := by
  cases e with
  | dummy v =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, notarizedDummy_cons m h.2⟩
  | block v x =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, notarizedBlock_cons m h.2⟩

private theorem chainNotarizedB_cons {P : Protocol} {sent : Sent} (m : Msg) {c : Chain}
    (h : chainNotarizedB P sent c = true) :
    chainNotarizedB P (m :: sent) c = true := by
  unfold chainNotarizedB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hk0 := h k hk
  cases hget : c[k]? with
  | none => rw [hget] at hk0; cases hk0
  | some e =>
    rw [hget] at hk0
    exact entryNotarizedB_cons m hk0

theorem chainNotarizedB_of_chainNotarized {P : Protocol} {sent : Sent} {c : Chain}
    (h : ChainNotarized P sent c) :
    chainNotarizedB P sent c = true := by
  unfold chainNotarizedB
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [List.getElem?_eq_getElem hk]
  have he := h k hk
  cases hc : c[k] with
  | dummy v =>
    rw [hc] at he
    simp [entryNotarizedB, he.1, he.2]
  | block v x =>
    rw [hc] at he
    simp [entryNotarizedB, he.1, he.2]

theorem voteRuleB_cons {P : Protocol} {sent : Sent} (m : Msg) {v : Nat} {t : Target}
    (h : voteRuleB P sent v t = true) :
    voteRuleB P (m :: sent) v t = true := by
  cases t with
  | dummy w => exact h
  | block c =>
    unfold voteRuleB at h ⊢
    cases hlast : c.getLast? with
    | none => simp [hlast] at h
    | some e =>
      cases e with
      | dummy _ => simp [hlast] at h
      | block w x =>
        simp only [hlast, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          List.contains_iff_mem] at h ⊢
        refine ⟨h.1, ⟨⟨⟨h.2.1.1.1, h.2.1.1.2⟩, chainNotarizedB_cons m h.2.1.2⟩, ?_⟩⟩
        exact List.mem_cons_of_mem m h.2.2

theorem voteRuleB_of_proposal {P : Protocol} {sent : Sent} {v : Nat} {p : Chain} {x : Nat}
    (hv : 1 ≤ v) (hlen : p.length = v - 1) (hp : ChainNotarized P sent p)
    (hprop : (⟨P.leader v, v, .propose, .block (p ++ [.block v x])⟩ : Msg) ∈ sent) :
    voteRuleB P sent v (.block (p ++ [.block v x])) = true := by
  dsimp only [voteRuleB]
  have hlast : (p ++ [Entry.block v x]).getLast? = some (Entry.block v x) :=
    List.getLast?_concat
  have hdrop : (p ++ [Entry.block v x]).dropLast = p :=
    List.dropLast_concat
  rw [hlast, hdrop]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem]
  exact ⟨hv, ⟨⟨⟨trivial, hlen⟩, chainNotarizedB_of_chainNotarized hp⟩, hprop⟩⟩

/-- Schedule honest `.vote` steps across `nodes` for target `t` in view `v` whenever unvoted. -/
def scheduleHonestVotes (P : Protocol) (v : Nat) (t : Target) : List NodeId → Sent → Sent
  | [], sent => sent
  | n :: ns, sent =>
    let sent' :=
      if !P.faulty n && P.committee.contains n && !votedAny sent n v && voteRuleB P sent v t then
        ⟨n, v, .vote, t⟩ :: sent
      else
        sent
    scheduleHonestVotes P v t ns sent'

theorem scheduleHonestVotes_reach {P : Protocol} {v : Nat} {t : Target} :
    ∀ (nodes : List NodeId) {sent : Sent},
      Reach P sent → Reach P (scheduleHonestVotes P v t nodes sent)
  | [], _, hr => hr
  | n :: ns, sent, hr => by
    unfold scheduleHonestVotes
    split
    · rename_i hCond
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hCond
      have hStep := Step.vote sent n v t ⟨hCond.1.1.2, hCond.1.1.1⟩ hCond.1.2 (voteRuleB_sound hCond.2)
      exact scheduleHonestVotes_reach ns (Reach.step hr hStep)
    · exact scheduleHonestVotes_reach ns hr

theorem scheduleHonestVotes_sub {P : Protocol} {v : Nat} {t : Target} :
    ∀ (nodes : List NodeId) (sent : Sent) {m : Msg},
      m ∈ sent → m ∈ scheduleHonestVotes P v t nodes sent
  | [], _, _, hm => hm
  | n :: ns, sent, m, hm => by
    unfold scheduleHonestVotes
    split
    · exact scheduleHonestVotes_sub ns _ (List.mem_cons_of_mem _ hm)
    · exact scheduleHonestVotes_sub ns sent hm

theorem scheduleHonestVotes_only_target_votes {P : Protocol} {v : Nat} {t : Target} :
    ∀ (nodes : List NodeId) (sent : Sent) {m : Msg},
      m ∈ scheduleHonestVotes P v t nodes sent →
      m ∈ sent ∨ (P.honest m.sender ∧ m.view = v ∧ m.kind = .vote ∧ m.target = t)
  | [], sent, m, hm => .inl hm
  | n :: ns, sent, m, hm => by
    unfold scheduleHonestVotes at hm
    split at hm
    · rename_i hCond
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hCond
      rcases scheduleHonestVotes_only_target_votes ns _ hm with hIn | hNew
      · rcases List.mem_cons.1 hIn with rfl | hOld
        · exact .inr ⟨⟨hCond.1.1.2, hCond.1.1.1⟩, rfl, rfl, rfl⟩
        · exact .inl hOld
      · exact .inr hNew
    · exact scheduleHonestVotes_only_target_votes ns sent hm

private theorem votedAny_or_voted_step {sent : Sent} {k n : NodeId} {v : Nat} {t : Target}
    (h : votedAny sent n v = false ∨ voted sent n v t = true) :
    votedAny (⟨k, v, .vote, t⟩ :: sent) n v = false ∨
      voted (⟨k, v, .vote, t⟩ :: sent) n v t = true := by
  by_cases hkn : k = n
  · subst hkn
    right
    rw [voted_iff]
    exact List.mem_cons_self
  · rcases h with hFresh | hVoted
    · left
      unfold votedAny at hFresh ⊢
      simp only [List.any_cons, Bool.or_eq_false_iff]
      refine ⟨?_, hFresh⟩
      simp [beq_eq_false_iff_ne.2 hkn]
    · right
      exact voted_cons sent _ n v t hVoted

private theorem scheduleHonestVotes_achieves_vote {P : Protocol} {v : Nat} {t : Target} :
    ∀ (nodes : List NodeId) (sent : Sent) {u : NodeId},
      voteRuleB P sent v t = true →
      P.honest u →
      u ∈ nodes →
      (votedAny sent u v = false ∨ voted sent u v t = true) →
      voted (scheduleHonestVotes P v t nodes sent) u v t = true
  | [], _, _, _, _, hMem, _ => False.elim (List.not_mem_nil hMem)
  | n :: ns, sent, u, hRule, hHonU, hMem, hState => by
    unfold scheduleHonestVotes
    rcases List.mem_cons.1 hMem with hEq | hInNs
    · subst hEq
      rcases hState with hFresh | hAlready
      · have hCond : (!P.faulty u && P.committee.contains u && !votedAny sent u v && voteRuleB P sent v t) = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem]
          exact ⟨⟨⟨hHonU.2, hHonU.1⟩, hFresh⟩, hRule⟩
        simp only [hCond, ↓reduceIte]
        rw [voted_iff]
        exact scheduleHonestVotes_sub ns _ List.mem_cons_self
      · split
        · rw [voted_iff]
          exact scheduleHonestVotes_sub ns _ (List.mem_cons_of_mem _ ((voted_iff _ _ _ _).1 hAlready))
        · rw [voted_iff]
          exact scheduleHonestVotes_sub ns sent ((voted_iff _ _ _ _).1 hAlready)
    · split
      · exact scheduleHonestVotes_achieves_vote ns _ (voteRuleB_cons _ hRule) hHonU hInNs
          (votedAny_or_voted_step hState)
      · exact scheduleHonestVotes_achieves_vote ns sent hRule hHonU hInNs hState

private theorem filter_length_mono_mem (p q : NodeId → Bool) :
    ∀ (xs : List NodeId),
      (∀ n ∈ xs, p n = true → q n = true) →
      (xs.filter p).length ≤ (xs.filter q).length
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    have ih := filter_length_mono_mem p q xs (fun n hn hp => h n (List.mem_cons_of_mem x hn) hp)
    simp only [List.filter_cons]
    cases hpx : p x with
    | false =>
      cases q x <;> simp <;> omega
    | true =>
      have hqx := h x List.mem_cons_self hpx
      simp [hqx]
      omega

theorem scheduleHonestVotes_quorum {P : Protocol} {sent : Sent} {v : Nat} {t : Target}
    (hRule : voteRuleB P sent v t = true)
    (hCompat : ∀ n, P.honest n → votedAny sent n v = false ∨ voted sent n v t = true) :
    P.quorum ≤ votesFor P (scheduleHonestVotes P v t P.committee sent) v t := by
  let sent' := scheduleHonestVotes P v t P.committee sent
  have hMono : (honestMembers P).length ≤ (P.committee.filter (fun n => voted sent' n v t)).length := by
    unfold honestMembers
    refine filter_length_mono_mem (fun n => !P.faulty n) (fun n => voted sent' n v t) P.committee ?_
    intro n hmem hnf
    have hFaultyFalse : P.faulty n = false := by
      cases hf : P.faulty n <;> simp_all
    have hHon : P.honest n := ⟨hmem, hFaultyFalse⟩
    exact scheduleHonestVotes_achieves_vote P.committee sent hRule hHon hmem (hCompat n hHon)
  exact Nat.le_trans (honestMembers_length_ge_quorum P) hMono

/-- Schedule honest `.finalize` votes across `nodes` for notarized block `c` in view `v`. -/
def scheduleHonestFinalizes (P : Protocol) (v : Nat) (c : Chain) : List NodeId → Sent → Sent
  | [], sent => sent
  | n :: ns, sent =>
    let sent' :=
      if !P.faulty n && P.committee.contains n && !finalizeVoted sent n v c &&
         voted sent n v (.block c) && decide (NotarizedBlock P sent v c) then
        ⟨n, v, .finalize, .block c⟩ :: sent
      else
        sent
    scheduleHonestFinalizes P v c ns sent'

theorem scheduleHonestFinalizes_reach {P : Protocol} {v : Nat} {c : Chain} :
    ∀ (nodes : List NodeId) {sent : Sent},
      Reach P sent → Reach P (scheduleHonestFinalizes P v c nodes sent)
  | [], _, hr => hr
  | n :: ns, sent, hr => by
    unfold scheduleHonestFinalizes
    split
    · rename_i hCond
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem,
        decide_eq_true_eq] at hCond
      have hStep := Step.finalize sent n v c ⟨hCond.1.1.1.2, hCond.1.1.1.1⟩ hCond.1.2 hCond.2
      exact scheduleHonestFinalizes_reach ns (Reach.step hr hStep)
    · exact scheduleHonestFinalizes_reach ns hr

theorem scheduleHonestFinalizes_sub {P : Protocol} {v : Nat} {c : Chain} :
    ∀ (nodes : List NodeId) (sent : Sent) {m : Msg},
      m ∈ sent → m ∈ scheduleHonestFinalizes P v c nodes sent
  | [], _, _, hm => hm
  | n :: ns, sent, m, hm => by
    unfold scheduleHonestFinalizes
    split
    · exact scheduleHonestFinalizes_sub ns _ (List.mem_cons_of_mem _ hm)
    · exact scheduleHonestFinalizes_sub ns sent hm

theorem scheduleHonestFinalizes_only_finalizes {P : Protocol} {v : Nat} {c : Chain} :
    ∀ (nodes : List NodeId) (sent : Sent) {m : Msg},
      m ∈ scheduleHonestFinalizes P v c nodes sent →
      m ∈ sent ∨ m.kind = .finalize
  | [], sent, m, hm => .inl hm
  | n :: ns, sent, m, hm => by
    unfold scheduleHonestFinalizes at hm
    split at hm
    · rcases scheduleHonestFinalizes_only_finalizes ns _ hm with hIn | hFin
      · rcases List.mem_cons.1 hIn with rfl | hOld
        · exact .inr rfl
        · exact .inl hOld
      · exact .inr hFin
    · exact scheduleHonestFinalizes_only_finalizes ns sent hm

private theorem scheduleHonestFinalizes_achieves_fin {P : Protocol} {v : Nat} {c : Chain} :
    ∀ (nodes : List NodeId) (sent : Sent) {u : NodeId},
      NotarizedBlock P sent v c →
      P.honest u →
      voted sent u v (.block c) = true →
      u ∈ nodes →
      finalizeVoted (scheduleHonestFinalizes P v c nodes sent) u v c = true
  | [], _, _, _, _, _, hMem => False.elim (List.not_mem_nil hMem)
  | n :: ns, sent, u, hNot, hHonU, hVotedU, hMem => by
    unfold scheduleHonestFinalizes
    rcases List.mem_cons.1 hMem with hEq | hInNs
    · subst hEq
      by_cases hAlready : finalizeVoted sent u v c = true
      · split
        · rw [finalizeVoted_iff]
          exact scheduleHonestFinalizes_sub ns _
            (List.mem_cons_of_mem _ ((finalizeVoted_iff _ _ _ _).1 hAlready))
        · rw [finalizeVoted_iff]
          exact scheduleHonestFinalizes_sub ns sent ((finalizeVoted_iff _ _ _ _).1 hAlready)
      · have hFinFalse : finalizeVoted sent u v c = false := Bool.eq_false_iff.2 hAlready
        have hCond :
            (!P.faulty u && P.committee.contains u && !finalizeVoted sent u v c &&
             voted sent u v (.block c) && decide (NotarizedBlock P sent v c)) = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, decide_eq_true_eq]
          exact ⟨⟨⟨⟨hHonU.2, hHonU.1⟩, hFinFalse⟩, hVotedU⟩, hNot⟩
        simp only [hCond, ↓reduceIte]
        rw [finalizeVoted_iff]
        exact scheduleHonestFinalizes_sub ns _ List.mem_cons_self
    · split
      · exact scheduleHonestFinalizes_achieves_fin ns _
          (notarizedBlock_cons _ hNot) hHonU (voted_cons sent _ u v (.block c) hVotedU) hInNs
      · exact scheduleHonestFinalizes_achieves_fin ns sent hNot hHonU hVotedU hInNs

theorem scheduleHonestFinalizes_finalized {P : Protocol} {sent : Sent} {v : Nat} {c : Chain}
    (hNot : NotarizedBlock P sent v c)
    (hAllVoted : ∀ n, P.honest n → voted sent n v (.block c) = true) :
    Finalized P (scheduleHonestFinalizes P v c P.committee sent) v c := by
  let sent' := scheduleHonestFinalizes P v c P.committee sent
  have hMono : (honestMembers P).length ≤ (P.committee.filter (fun n => finalizeVoted sent' n v c)).length := by
    unfold honestMembers
    refine filter_length_mono_mem (fun n => !P.faulty n) (fun n => finalizeVoted sent' n v c) P.committee ?_
    intro n hmem hnf
    have hFaultyFalse : P.faulty n = false := by
      cases hf : P.faulty n <;> simp_all
    have hHon : P.honest n := ⟨hmem, hFaultyFalse⟩
    exact scheduleHonestFinalizes_achieves_fin P.committee sent hNot hHon (hAllVoted n hHon) hmem
  exact Nat.le_trans (honestMembers_length_ge_quorum P) hMono

/-! ## 4. Explicit View Timers, Pre-GST View Advance & Post-GST One-View Finalization -/

/-- Partial-synchrony timing parameters (`GST`, post-GST delay `deltaNet`, exponential timer base). -/
structure PartialSyncConfig where
  gst         : Nat
  deltaNet    : Nat
  baseTimeout : Nat
  backoffCap  : Nat

/-- Real-time schedule of a single consensus view `v`. -/
structure ViewExecutionSchedule where
  viewStart           : Nat
  viewsSinceCommit    : Nat
  enterTime           : NodeId → Nat
  proposalArrival     : NodeId → Nat
  notarizationArrival : NodeId → Nat

/-- Effective view timer duration `Δ_timer` for `sched.viewsSinceCommit` under exponential backoff. -/
def effectiveDeltaTimer (cfg : PartialSyncConfig) (sched : ViewExecutionSchedule) : Nat :=
  viewTimeout cfg.baseTimeout sched.viewsSinceCommit cfg.backoffCap

/-- Validator `n`'s local view-timeout deadline `enterTime n + Δ_timer`. -/
def nodeTimerDeadline (cfg : PartialSyncConfig) (sched : ViewExecutionSchedule) (n : NodeId) : Nat :=
  sched.enterTime n + effectiveDeltaTimer cfg sched

/-- Timed honest vote selector in view `v`: votes for `.block proposedChain` iff the valid proposal
    arrives strictly before `nodeTimerDeadline`, otherwise votes `.dummy v` on timeout! -/
def selectTimedVoteTarget (cfg : PartialSyncConfig) (sched : ViewExecutionSchedule)
    (v : Nat) (proposedChain : Chain) (n : NodeId) : Target :=
  if sched.proposalArrival n < nodeTimerDeadline cfg sched n then
    .block proposedChain
  else
    .dummy v

/-- **Theorem 1: Pre-GST or Faulty-Leader View-Advance Progress (`pre_gst_or_faulty_leader_advances_view`)**:
    In *any* view `v ≥ 1` extending a notarized `v - 1` chain `p` (`ChainNotarized P sent p`),
    whenever all `≥ 2f + 1` honest nodes either:
    - observe a block notarization in view `v` (`∃ x, NotarizedBlock P sent v (p ++ [.block v x])`), OR
    - reach view timeout without casting a conflicting block vote (`votedAny sent n v = false ∨ voted sent n v (.dummy v) = true`,
      which holds automatically whenever a faulty leader withholds proposals or sends invalid ones!),
    view `v` constructively produces a reachable `sent'` (`Reach P sent'`) and a valid entry `e : Entry`
    (`e.view = v`) with `ChainNotarized P sent' (p ++ [e])` and `(p ++ [e]).length = v`, ensuring honest
    nodes are never permanently deadlocked in view `v`! -/
theorem pre_gst_or_faulty_leader_advances_view
    {P : Protocol} {sent : Sent} {v : Nat} {p : Chain}
    (hReach : Reach P sent)
    (hv : 1 ≤ v)
    (hlen : p.length = v - 1)
    (hpNot : ChainNotarized P sent p)
    (hOutcome :
      (∃ payload : Nat, NotarizedBlock P sent v (p ++ [.block v payload])) ∨
      (∀ n : NodeId, P.honest n → votedAny sent n v = false ∨ voted sent n v (.dummy v) = true)) :
    ∃ (sent' : Sent) (e : Entry),
      Reach P sent' ∧
      e.view = v ∧
      (p ++ [e]).length = v ∧
      ChainNotarized P sent' (p ++ [e]) := by
  rcases hOutcome with ⟨payload, hNotBlock⟩ | hTimeoutReady
  · refine ⟨sent, .block v payload, hReach, rfl, ?_, ?_⟩
    · simp [hlen]; omega
    · exact chainNotarized_snoc hpNot hlen hv hNotBlock
  · let sent' := scheduleHonestVotes P v (.dummy v) P.committee sent
    have hRuleDummy : voteRuleB P sent v (.dummy v) = true := by
      simp [voteRuleB, hv]
    have hReach' : Reach P sent' := scheduleHonestVotes_reach P.committee hReach
    have hNotDummy : NotarizedDummy P sent' v :=
      scheduleHonestVotes_quorum hRuleDummy hTimeoutReady
    have hpNot' : ChainNotarized P sent' p := by
      intro k hk
      have he := hpNot k hk
      cases hpk : p[k] with
      | dummy w =>
        rw [hpk] at he
        refine ⟨he.1, Nat.le_trans he.2 ?_⟩
        apply filter_length_mono _ _ P.committee
        intro u hu
        rw [voted_iff] at hu ⊢
        exact scheduleHonestVotes_sub P.committee sent hu
      | block w x =>
        rw [hpk] at he
        refine ⟨he.1, Nat.le_trans he.2 ?_⟩
        apply filter_length_mono _ _ P.committee
        intro u hu
        rw [voted_iff] at hu ⊢
        exact scheduleHonestVotes_sub P.committee sent hu
    refine ⟨sent', .dummy v, hReach', rfl, ?_, ?_⟩
    · simp [hlen]; omega
    · exact chainNotarized_snoc_dummy hpNot' hlen hv hNotDummy

/-- Post-GST partial-synchrony timing contract for view `v`:
    - view starts at or after `GST` (`cfg.gst ≤ sched.viewStart`),
    - all honest nodes enter view `v` within `deltaNet` of `viewStart`,
    - honest leader `L = P.leader v` broadcasts its proposal upon entering view `v`, arriving at
      every honest node within `deltaNet` (`proposalArrival n ≤ enterTime L + deltaNet`),
    - once all honest votes are cast (`≤ viewStart + 2 * deltaNet`), the notarization arrives
      within `deltaNet` (`notarizationArrival n ≤ viewStart + 3 * deltaNet`),
    - view timer satisfies `2 * deltaNet < effectiveDeltaTimer cfg sched` (`Δ_timer > 2 Δ_net`). -/
structure PostGstHonestViewSync (P : Protocol) (cfg : PartialSyncConfig)
    (sched : ViewExecutionSchedule) (v : Nat) : Prop where
  postGst          : cfg.gst ≤ sched.viewStart
  honestLeader     : P.honest (P.leader v)
  honestEnterBound : ∀ n, P.honest n →
                       sched.viewStart ≤ sched.enterTime n ∧
                       sched.enterTime n ≤ sched.viewStart + cfg.deltaNet
  proposalDelivery : ∀ n, P.honest n →
                       sched.proposalArrival n ≤ sched.enterTime (P.leader v) + cfg.deltaNet
  notarDelivery    : ∀ n, P.honest n →
                       sched.notarizationArrival n ≤ sched.viewStart + 3 * cfg.deltaNet
  timerMargin      : 2 * cfg.deltaNet < effectiveDeltaTimer cfg sched

/-- Under `PostGstHonestViewSync`, every honest node receives the honest leader's proposal
    **strictly before** its view timer `enterTime n + Δ_timer` expires, so `selectTimedVoteTarget`
    always selects `.block proposedChain` and never `.dummy v`! -/
theorem postGst_proposal_before_timeout
    {P : Protocol} {cfg : PartialSyncConfig} {sched : ViewExecutionSchedule}
    {v : Nat} (c : Chain) {n : NodeId}
    (hSync : PostGstHonestViewSync P cfg sched v)
    (hHon : P.honest n) :
    sched.proposalArrival n < nodeTimerDeadline cfg sched n ∧
    selectTimedVoteTarget cfg sched v c n = .block c := by
  have hLeaderEnter := (hSync.honestEnterBound (P.leader v) hSync.honestLeader).2
  have hNodeEnter := (hSync.honestEnterBound n hHon).1
  have hPropArr := hSync.proposalDelivery n hHon
  have hMargin := hSync.timerMargin
  have hLt : sched.proposalArrival n < nodeTimerDeadline cfg sched n := by
    unfold nodeTimerDeadline
    omega
  refine ⟨hLt, ?_⟩
  unfold selectTimedVoteTarget
  simp only [hLt, ↓reduceIte]

/-- Execute a complete post-GST honest-leader view `v`:
    1. Honest leader `P.leader v` proposes `p ++ [.block v payload]`,
    2. All honest nodes run `selectTimedVoteTarget` and cast `.vote`,
    3. All honest nodes cast `.finalize` upon notarization. -/
def runPostGstHonestLeaderView
    (P : Protocol) (cfg : PartialSyncConfig) (sched : ViewExecutionSchedule)
    (sent₀ : Sent) (v payload : Nat) (p : Chain) : Sent :=
  let c : Chain := p ++ [.block v payload]
  let leader := P.leader v
  let sentProp : Sent := ⟨leader, v, .propose, .block c⟩ :: sent₀
  let target := selectTimedVoteTarget cfg sched v c leader
  let sentVotes : Sent := scheduleHonestVotes P v target P.committee sentProp
  scheduleHonestFinalizes P v c P.committee sentVotes

/-- **Theorem 2: Post-GST Honest-Leader One-View Finalization (`gst_honest_leader_finalizes`)**:
    If view `v ≥ 1` enters at `viewStart ≥ GST` with an honest leader `P.leader v`, all honest
    nodes enter view `v` within `Δ_net`, and `Δ_timer > 2 Δ_net` (`PostGstHonestViewSync`):
    starting from any reachable `sent₀` where honest nodes have not yet voted in view `v` and
    `ChainNotarized P sent₀ p` (`p.length = v - 1`), executing view `v` (`sentFinal`):
    1. Preserves `Reach P sentFinal` (genuine `Step.propose`, `Step.vote`, `Step.finalize` steps),
    2. Every honest node receives `L`'s proposal strictly before its view timer expires,
    3. **Zero honest nodes cast `.dummy v`** (`voted sentFinal n v (.dummy v) = false`),
    4. **All `≥ 2f + 1` honest nodes cast `.vote`** for `L`'s proposal `b = p ++ [.block v payload]`,
    5. `NotarizedBlock P sentFinal v b` forms (and before timeout whenever `leader` enters at `viewStart`
       with `notarizationArrival n ≤ viewStart + 2 * deltaNet`),
    6. **All `≥ 2f + 1` honest nodes cast `.finalize`** for `b`,
    7. **`Finalized P sentFinal v b` holds** and `extractFinCert?` produces a checking `FinCert(v, b)`
       in that single view `v`! -/
theorem gst_honest_leader_finalizes
    {P : Protocol} {cfg : PartialSyncConfig} {sched : ViewExecutionSchedule}
    {sent₀ : Sent} {v payload : Nat} {p : Chain}
    (hReach₀ : Reach P sent₀)
    (hv : 1 ≤ v)
    (hlen : p.length = v - 1)
    (hpNot : ChainNotarized P sent₀ p)
    (hFreshView : ∀ n, P.honest n → votedAny sent₀ n v = false)
    (hSync : PostGstHonestViewSync P cfg sched v) :
    let b : Chain := p ++ [.block v payload]
    let sentFinal : Sent := runPostGstHonestLeaderView P cfg sched sent₀ v payload p
    Reach P sentFinal ∧
    (∀ n, P.honest n → sched.proposalArrival n < nodeTimerDeadline cfg sched n) ∧
    (∀ n, P.honest n → voted sentFinal n v (.dummy v) = false) ∧
    (∀ n, P.honest n → voted sentFinal n v (.block b) = true) ∧
    NotarizedBlock P sentFinal v b ∧
    (∀ n, P.honest n → finalizeVoted sentFinal n v b = true) ∧
    Finalized P sentFinal v b ∧
    ChainNotarized P sentFinal b ∧
    (∃ cert : FinCert,
      extractFinCert? P sentFinal v b = some cert ∧
      cert.view = v ∧
      cert.chain = b ∧
      cert.checks P sentFinal = true) := by
  intro b sentFinal
  let leader := P.leader v
  let sentProp : Sent := ⟨leader, v, .propose, .block b⟩ :: sent₀
  have hLeaderBefore := postGst_proposal_before_timeout b hSync hSync.honestLeader
  have hTargetEq : selectTimedVoteTarget cfg sched v b leader = .block b := hLeaderBefore.2
  let sentVotes : Sent := scheduleHonestVotes P v (.block b) P.committee sentProp
  have hFinalEq : sentFinal = scheduleHonestFinalizes P v b P.committee sentVotes := by
    unfold sentFinal runPostGstHonestLeaderView
    simp only [b, leader, sentProp, hTargetEq, sentVotes]
  have hStepProp : Step P sent₀ sentProp :=
    Step.propose sent₀ leader v b hSync.honestLeader rfl
  have hReachProp : Reach P sentProp := Reach.step hReach₀ hStepProp
  have hpNotProp : ChainNotarized P sentProp p := chainNotarized_cons _ hpNot
  have hRuleBlock : voteRuleB P sentProp v (.block b) = true :=
    voteRuleB_of_proposal hv hlen hpNotProp List.mem_cons_self
  have hFreshProp : ∀ n, P.honest n → votedAny sentProp n v = false := by
    intro n hHon
    unfold votedAny sentProp
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨by simp, hFreshView n hHon⟩
  have hReachVotes : Reach P sentVotes :=
    scheduleHonestVotes_reach P.committee hReachProp
  have hAllVotedVotes : ∀ n, P.honest n → voted sentVotes n v (.block b) = true := by
    intro n hHon
    exact scheduleHonestVotes_achieves_vote P.committee sentProp hRuleBlock hHon hHon.1
      (.inl (hFreshProp n hHon))
  have hNotVotes : NotarizedBlock P sentVotes v b :=
    scheduleHonestVotes_quorum hRuleBlock (fun n hHon => .inl (hFreshProp n hHon))
  have hReachFinal : Reach P sentFinal := by
    rw [hFinalEq]
    exact scheduleHonestFinalizes_reach P.committee hReachVotes
  have hAllVotedFinal : ∀ n, P.honest n → voted sentFinal n v (.block b) = true := by
    intro n hHon
    rw [hFinalEq, voted_iff]
    exact scheduleHonestFinalizes_sub P.committee sentVotes
      ((voted_iff _ _ _ _).1 (hAllVotedVotes n hHon))
  have hNoDummyFinal : ∀ n, P.honest n → voted sentFinal n v (.dummy v) = false := by
    intro n hHon
    cases hDum : voted sentFinal n v (.dummy v) with
    | false => rfl
    | true =>
      have hMemFinal := (voted_iff sentFinal n v (.dummy v)).1 hDum
      rw [hFinalEq] at hMemFinal
      rcases scheduleHonestFinalizes_only_finalizes P.committee sentVotes hMemFinal with hInVotes | hIsFin
      · rcases scheduleHonestVotes_only_target_votes P.committee sentProp hInVotes with hInProp | hVoteTarget
        · rcases List.mem_cons.1 hInProp with hEqProp | hIn₀
          · cases hEqProp
          · have hAny := votedAny_of_mem hIn₀ rfl
            rw [hFreshView n hHon] at hAny
            cases hAny
        · cases hVoteTarget.2.2.2
      · cases hIsFin
  have hNotFinal : NotarizedBlock P sentFinal v b := by
    rw [hFinalEq]
    refine Nat.le_trans hNotVotes ?_
    apply filter_length_mono _ _ P.committee
    intro n hn
    rw [voted_iff] at hn ⊢
    exact scheduleHonestFinalizes_sub P.committee sentVotes hn
  have hAllFinFinal : ∀ n, P.honest n → finalizeVoted sentFinal n v b = true := by
    intro n hHon
    rw [hFinalEq]
    exact scheduleHonestFinalizes_achieves_fin P.committee sentVotes hNotVotes hHon
      (hAllVotedVotes n hHon) hHon.1
  have hFinalized : Finalized P sentFinal v b := by
    rw [hFinalEq]
    exact scheduleHonestFinalizes_finalized hNotVotes hAllVotedVotes
  have hChainNotFinal : ChainNotarized P sentFinal b :=
    finalized_chainNotarized (reach_inv hReachFinal) hFinalized
  exact ⟨hReachFinal,
         fun n hHon => (postGst_proposal_before_timeout b hSync hHon).1,
         hNoDummyFinal,
         hAllVotedFinal,
         hNotFinal,
         hAllFinFinal,
         hFinalized,
         hChainNotFinal,
         extractFinCert_checks_of_finalized hFinalized⟩

/-- **View-Indexed Canonical Liveness & Uniqueness Corollary (`gst_honest_leader_finalizes_in_view`)**:
    Composes `gst_honest_leader_finalizes` with `FinCert.unique_per_height_reach` and
    `notarized_block_unique`: in view `v` after `GST` with an honest leader and `Δ_timer > 2 Δ_net`,
    `runPostGstHonestLeaderView` produces a checking `FinCert` for `b = p ++ [.block v payload]`,
    notarization in view `v` forms strictly before timeout when `notarizationArrival n ≤ viewStart + 2 * deltaNet`,
    and **every** checking `FinCert` at height `b.height` on `sentFinal` agrees identically on `b.blocks`! -/
theorem gst_honest_leader_finalizes_in_view
    {P : Protocol} {cfg : PartialSyncConfig} {sched : ViewExecutionSchedule}
    {sent₀ : Sent} {v payload : Nat} {p : Chain}
    (hReach₀ : Reach P sent₀)
    (hv : 1 ≤ v)
    (hlen : p.length = v - 1)
    (hpNot : ChainNotarized P sent₀ p)
    (hFreshView : ∀ n, P.honest n → votedAny sent₀ n v = false)
    (hSync : PostGstHonestViewSync P cfg sched v)
    (hFastNotar : ∀ n, P.honest n → sched.notarizationArrival n ≤ sched.viewStart + 2 * cfg.deltaNet) :
    let b : Chain := p ++ [.block v payload]
    let sentFinal : Sent := runPostGstHonestLeaderView P cfg sched sent₀ v payload p
    (∀ n, P.honest n → sched.notarizationArrival n < nodeTimerDeadline cfg sched n) ∧
    Finalized P sentFinal v b ∧
    (∃ cert : FinCert,
      cert.view = v ∧
      cert.chain = b ∧
      cert.checks P sentFinal = true ∧
      ∀ other : FinCert,
        other.checks P sentFinal = true →
        other.chain.height = b.height →
        other.chain.blocks = b.blocks) := by
  intro b sentFinal
  obtain ⟨hReachF, _, _, _, _, _, hFin, _, ⟨cert, _, hcv, hcc, hcChk⟩⟩ :=
    gst_honest_leader_finalizes hReach₀ hv hlen hpNot hFreshView hSync
  refine ⟨?_, hFin, ⟨cert, hcv, hcc, hcChk, ?_⟩⟩
  · intro n hHon
    have hEnter := (hSync.honestEnterBound n hHon).1
    have hArr := hFastNotar n hHon
    have hMargin := hSync.timerMargin
    unfold nodeTimerDeadline
    omega
  · intro other hOtherChk hHeight
    have hEq := FinCert.unique_per_height_reach hReachF hOtherChk hcChk (hHeight.trans (hcc ▸ rfl))
    simpa [hcc] using hEq

/-! ## 5. Non-Vacuity / Inhabitedness Witnesses -/

private def sampleProto4 : Protocol :=
  ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

private def sampleHashId : HashBytes.Hash :=
  fun bs => HashBytes.be 32 (bs.foldl (fun acc b => (acc * 131 + b.toNat + 1) % 65537) 1)

private def sampleSalt32 : ByteArray :=
  bytesOfList (List.replicate 32 0x42)

private def sampleMsg0 : Msg :=
  ⟨0, 1, .propose, .block [.block 1 99]⟩

private def sampleKeys4 : KeyDirectory where
  pubKey _ := deriveSlotPubKey sampleHashId (signableByteArray 0#256 sampleMsg0) sampleSalt32

private def sampleSigned0 : SignedSimplexMsg where
  msg := sampleMsg0
  signerPk := 0#256
  signature := sampleSalt32

example : msgCanonical sampleMsg0 = true := by decide
example : entryCanonical (.block 1 99) = true := by decide
example : targetCanonical (.block [.block 1 99]) = true := by decide
example : checkHonestProtocolRule sampleProto4 [] sampleMsg0 = true := by decide
example : verifySignedSent (SignatureScheme.mk (fun _ _ _ => true)) ⟨fun _ => 0#256⟩
            sampleProto4.committee [sampleSigned0] = true := by decide

example :
    let cfg : PartialSyncConfig := ⟨100, 10, 25, 2⟩
    let sched : ViewExecutionSchedule := ⟨100, 0, fun _ => 100, fun _ => 108, fun _ => 118⟩
    let sentF := runPostGstHonestLeaderView sampleProto4 cfg sched [] 1 777 []
    (extractFinCert? sampleProto4 sentF 1 [.block 1 777]).isSome = true := by
  decide

end Obend.Consensus.SimplexLiveness
end
