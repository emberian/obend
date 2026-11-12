module
/-
# Obend.Vault.IrreversibleOutbox — Pillar 6: `seL4` Copy-Before-Verify SPSC & 3-Class Effect Settlement

Implements Obend Pillar 6 (`Firmament` microkernel irreversible outbox settlement):
1. **3-Class External Effect Taxonomy (`EffectClass`)**:
   - `.idempotentRead`: side-effect-free external read/telemetry query, permitted pre-finality.
   - `.compensatableEscrow`: optimistic external reservation permitted pre-finality only when
     backed by a funded rollback compensation bond (`0 < rollbackCost ≤ fundedDeposit`), with
     deterministic settlement/compensation reconciliation (`reconcileEscrowsAgainstFinalized`) when
     competing unfinalized branches are superseded by a canonical finalized chain.
   - `.irreversibleActuation`: physical hardware actuation, external wire transfer, or RF TX —
     **strictly gated** on:
     (a) `seL4` Microkit partition isolation (`checkMicrokitIsolation part = true`) and bounded SPSC
         IPC channel confinement,
     (b) **Copy-Before-Verify SPSC Isolation (`copyRingToPrivateSlot`)**: the untrusted shared
         ring slot is copied into PD-private memory before verification, and the copy is what is
         verified and dispatched. What the shared ring holds afterwards is not an input; the
         guarantee is stated over the finalized state (`dispatched_payload_bound_to_finalized_commit`):
         any bytes whose commitment is the finalized block's payload are the dispatched bytes, or a
         cSHAKE256 collision,
     (c) Verified `SimplexProtocol.FinCert` (`cert.checks P sent = true`) whose finalized block at
         `cert.view` commits via 256-bit SP 800-185 cSHAKE256 (`effectCommitNat`, below `2 ^ 256`
         by `effectCommitNat_lt`, so the block is wire-canonical: `outboxBlock_canonical`) to the
         exact `(nullifierId, .irreversibleActuation, privateCopy)` preimage,
     (d) Strictly monotonic outbox nullifier (`st.highWaterNullifier < req.nullifierId`).
2. **Multi-Turn / Multi-View Outbox Safety (`firmament_sel4_copy_before_verify_and_irreversible_outbox_safe`)**:
   - Proves across arbitrary multi-turn `ValidOutboxTrace` runs interleaved with open-world
     Byzantine `SimplexProtocol.Step` transitions (`Step.inject`, `.dummy` view skips, competing
     unfinalized branches) and arbitrary shared-ring DMA TOCTOU mutations:
     - `Sel4CapDlNonInterfering` Microkit isolation,
     - Dispatched payloads bound to the finalized 256-bit commitment (no TOCTOU), and spent
       nullifiers refused for good (`dispatched_nullifier_never_replays`),
     - Canonical finality (`Finalized P sentF`), prefix consistency (`finalized_consistent`),
       per-height block uniqueness (`fin_cert_unique_per_height`), and zero rollback / zero orphan
       actuations (`irreversible_at_most_once_and_never_rolled_back`),
     - Strict at-most-once nullifier uniqueness (`Nodup`),
     - Exact escrow vault balance conservation and bidirectional open-world step completeness
       (`outboxStep_skip_implies_violation`, `outboxStep_complete`).
-/

public import Obend.Consensus.SimplexProtocol
public import Obend.Consensus.Finality
public import Obend.Trailblaze.Polis
public import Obend.Digest.Cshake256.Seam
public import Obend.Digest.HashBytes

public section
namespace Obend.Vault.IrreversibleOutbox

open Obend.Consensus.SimplexProtocol
open Obend.Trailblaze.Polis (SeL4MicrokitPartition IpcChannel checkMicrokitIsolation
  refuseMicrokitIsolation Sel4CapDlNonInterfering checkMicrokitIsolation_implies_capDlNonInterfering)
open Obend.Digest
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList cshake256Kernel)

set_option autoImplicit false

/-! ## 1. The 3-Class External Effect Taxonomy & Domain-Framed 256-Bit Commitments -/

/-- Three-class taxonomy of external cyber-physical and financial effects. -/
inductive EffectClass where
  | idempotentRead
  | compensatableEscrow
  | irreversibleActuation
  deriving DecidableEq, Repr, Inhabited

/-- Domain tag for 256-bit outbox effect commitments (`"OBEND-OUTBOX-EFFECT-V1"`, 22 bytes). -/
def outboxEffectDomain : ByteArray :=
  bytesOfList
    [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x4F, 0x55, 0x54, 0x42, 0x4F,
     0x58, 0x2D, 0x45, 0x46, 0x46, 0x45, 0x43, 0x54, 0x2D, 0x56, 0x31]

/-- Domain tag for 256-bit outbox nullifier digests (`"OBEND-OUTBOX-NULLIFIER-V1"`, 25 bytes). -/
def outboxNullifierDomain : ByteArray :=
  bytesOfList
    [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x4F, 0x55, 0x54, 0x42, 0x4F, 0x58, 0x2D,
     0x4E, 0x55, 0x4C, 0x4C, 0x49, 0x46, 0x49, 0x45, 0x52, 0x2D, 0x56, 0x31]

/-- Canonical 64-bit scalar bound (`256 ^ 8 = 2 ^ 64`) for 8-byte big-endian framing. -/
@[expose] def OutboxBound64 : Nat := 256 ^ 8

/-- Encode `EffectClass` as a single canonical tag byte. -/
def encodeEffectClassByte : EffectClass → UInt8
  | .idempotentRead        => 0x01
  | .compensatableEscrow   => 0x02
  | .irreversibleActuation => 0x03

theorem encodeEffectClassByte_injective {c₁ c₂ : EffectClass}
    (h : encodeEffectClassByte c₁ = encodeEffectClassByte c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | rfl | cases h

/-- Length-framed canonical byte preimage binding `(nullifierId, effectClass, payloadBytes)`. -/
def encodeEffectPreimage (nullifierId : Nat) (cls : EffectClass) (payload : ByteArray) : List UInt8 :=
  HashBytes.be 8 nullifierId ++
    ([encodeEffectClassByte cls] ++
      (HashBytes.be 8 payload.data.toList.length ++ payload.data.toList))

/-- Constructive preimage injectivity (`0 Classical`): distinct `(nullifierId, cls, payload)`
    triples under `< 2^64` bounds map to distinct byte preimages. -/
theorem encodeEffectPreimage_injective
    {id₁ id₂ : Nat} {cls₁ cls₂ : EffectClass} {p₁ p₂ : ByteArray}
    (hid₁ : id₁ < OutboxBound64) (hid₂ : id₂ < OutboxBound64)
    (hp₁ : p₁.data.toList.length < OutboxBound64)
    (hp₂ : p₂.data.toList.length < OutboxBound64)
    (hEq : encodeEffectPreimage id₁ cls₁ p₁ = encodeEffectPreimage id₂ cls₂ p₂) :
    id₁ = id₂ ∧ cls₁ = cls₂ ∧ p₁ = p₂ := by
  unfold encodeEffectPreimage at hEq
  obtain ⟨hIdBe, h1⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
  simp only [List.singleton_append, List.cons.injEq] at h1
  obtain ⟨hClsByte, h2⟩ := h1
  obtain ⟨hLenBe, hPayList⟩ := List.append_inj h2 (by simp [HashBytes.length_be])
  have hIdEq := HashBytes.be_injective hid₁ hid₂ hIdBe
  have hClsEq := encodeEffectClassByte_injective hClsByte
  have _ := HashBytes.be_injective hp₁ hp₂ hLenBe
  have hPayEq : p₁ = p₂ := by
    cases p₁ with | mk d₁ =>
    cases p₂ with | mk d₂ =>
    have hd : d₁ = d₂ := Array.ext' hPayList
    rw [hd]
  exact ⟨hIdEq, hClsEq, hPayEq⟩

/-- Full 256-bit SP 800-185 cSHAKE256 digest of `(nullifierId, cls, payload)` as a 32-byte `ByteArray`. -/
def effectCommitBytes (nullifierId : Nat) (cls : EffectClass) (payload : ByteArray) : ByteArray :=
  cshake256Kernel outboxEffectDomain (bytesOfList (encodeEffectPreimage nullifierId cls payload))

/-- Full 256-bit commitment read as a `Nat` (`< 2^256`) stored in `SimplexProtocol.Entry.block view payload`. -/
def effectCommitNat (nullifierId : Nat) (cls : EffectClass) (payload : ByteArray) : Nat :=
  HashBytes.ofBE (effectCommitBytes nullifierId cls payload).data.toList

/-- Full 256-bit domain-separated cryptographic nullifier tag (`BitVec 256`) for `nullifierId`. -/
def deriveOutboxNullifier256 (gatekeeperPd : Nat) (nullifierId : Nat) : BitVec 256 :=
  let raw := cshake256Kernel outboxNullifierDomain
    (bytesOfList (HashBytes.be 8 gatekeeperPd ++ HashBytes.be 8 nullifierId))
  BitVec.ofNat 256 (HashBytes.ofBE raw.data.toList)

theorem effectCommitBytes_eq_spec (nullifierId : Nat) (cls : EffectClass) (payload : ByteArray) :
    (effectCommitBytes nullifierId cls payload).data.toList =
      cshake256Bytes outboxEffectDomain.data.toList (encodeEffectPreimage nullifierId cls payload) := by
  unfold effectCommitBytes cshake256Kernel
  rw [bytesOfList_toList, bytesOfList_toList, Cshake256.Fast.cshake256Fast_eq]

/-- The commitment is a 256-bit number: it fits a block payload's 32 wire bytes with nothing cut. -/
theorem effectCommitNat_lt (nullifierId : Nat) (cls : EffectClass) (payload : ByteArray) :
    effectCommitNat nullifierId cls payload < 256 ^ 32 := by
  unfold effectCommitNat
  rw [effectCommitBytes_eq_spec]
  have h := HashBytes.ofBE_lt
    (cshake256Bytes outboxEffectDomain.data.toList (encodeEffectPreimage nullifierId cls payload))
  rw [Cshake256.cshake256Bytes_length] at h
  exact h

/-- A block carrying an outbox commitment is canonical on the Simplex wire (`Entry.encode`), at
    any view that fits 8 bytes. -/
theorem outboxBlock_canonical {view : Nat} (hv : view < 256 ^ 8) (nullifierId : Nat)
    (cls : EffectClass) (payload : ByteArray) :
    (Entry.block view (effectCommitNat nullifierId cls payload)).canonical = true :=
  Entry.canonical_block.2 ⟨hv, effectCommitNat_lt nullifierId cls payload⟩

/-- Constructive 256-bit cSHAKE256 commitment binding (`0 Classical.choice`):
    equal `effectCommitNat` values either come from identical `(nullifierId, cls, payload)` triples
    or exhibit an explicit SP 800-185 cSHAKE256 `HashBytes.Collision`! -/
theorem effectCommitNat_binding
    {id₁ id₂ : Nat} {cls₁ cls₂ : EffectClass} {p₁ p₂ : ByteArray}
    (hid₁ : id₁ < OutboxBound64) (hid₂ : id₂ < OutboxBound64)
    (hp₁ : p₁.data.toList.length < OutboxBound64)
    (hp₂ : p₂.data.toList.length < OutboxBound64)
    (hCommitEq : effectCommitNat id₁ cls₁ p₁ = effectCommitNat id₂ cls₂ p₂) :
    (id₁ = id₂ ∧ cls₁ = cls₂ ∧ p₁ = p₂) ∨
      HashBytes.Collision (cshake256Bytes outboxEffectDomain.data.toList) := by
  if hPre : encodeEffectPreimage id₁ cls₁ p₁ = encodeEffectPreimage id₂ cls₂ p₂ then
    exact .inl (encodeEffectPreimage_injective hid₁ hid₂ hp₁ hp₂ hPre)
  else
    refine .inr ⟨_, _, hPre, ?_⟩
    unfold effectCommitNat at hCommitEq
    rw [effectCommitBytes_eq_spec, effectCommitBytes_eq_spec] at hCommitEq
    exact hCommitEq

/-! ## 2. `seL4` Microkit SPSC Copy-Before-Verify Ring & Escrow Compensation Carriers -/

/-- An untrusted SPSC shared-memory ring transfer into the `seL4` outbox gatekeeper PD:
    `sharedRingBeforeCopy` is the shared ring slot at the instant the gatekeeper copies it into
    private RAM. Later contents of the ring are no part of a request: the gatekeeper never reads
    them, and `dispatched_payload_bound_to_finalized_commit` says what any other bytes would have
    to satisfy to stand in for the dispatched ones. -/
structure SpscRingTransfer where
  channelId             : Nat
  sharedRingBeforeCopy  : ByteArray
  deriving DecidableEq

/-- Copy-Before-Verify: snapshot `sharedRingBeforeCopy` into PD-private memory unmapped from
    untrusted producer PDs and peripheral DMA. The snapshot is verified and the snapshot is
    dispatched. -/
def copyRingToPrivateSlot (spsc : SpscRingTransfer) : ByteArray :=
  spsc.sharedRingBeforeCopy

/-- Compensatable escrow bond backing an optimistic pre-finality `.compensatableEscrow` effect. -/
structure EscrowCompensationBond where
  fundedDeposit : Nat
  rollbackCost  : Nat
  deriving DecidableEq, Repr

/-- Active optimistic `.compensatableEscrow` reservation awaiting canonical finality or rollback. -/
structure PendingOptimisticEscrow where
  nullifierId   : Nat
  targetView    : Nat
  optimisticTip : Chain
  payload       : ByteArray
  bond          : EscrowCompensationBond
  deriving DecidableEq

/-- Record of a permanently dispatched `.irreversibleActuation` effect. -/
structure DispatchedActuation where
  nullifierId       : Nat
  nullifierDigest   : BitVec 256
  view              : Nat
  chain             : Chain
  finCert           : FinCert
  dispatchedPayload : ByteArray
  deriving DecidableEq

/-- Persistent multi-turn outbox state inside the `seL4` gatekeeper Protection Domain. -/
structure OutboxState where
  gatekeeperPd          : Nat
  highWaterNullifier    : Nat
  escrowVaultBalance    : Nat
  readAuditCount        : Nat
  activeEscrows         : List PendingOptimisticEscrow
  settledEscrowTotal    : Nat
  dispatchedActuations  : List DispatchedActuation
  deriving DecidableEq

/-- Sum of deposits currently locked across `activeEscrows`. -/
def lockedEscrowDeposits : List PendingOptimisticEscrow → Nat
  | [] => 0
  | e :: es => e.bond.fundedDeposit + lockedEscrowDeposits es

/-- External effect request submitted across an `seL4` Microkit SPSC channel. -/
structure OutboxEffectReq where
  nullifierId   : Nat
  effectClass   : EffectClass
  targetView    : Nat
  proposedChain : Chain
  finCert?      : Option FinCert
  escrowBond?   : Option EscrowCompensationBond
  spsc          : SpscRingTransfer
  deriving DecidableEq

/-- Named constructive refusal clauses for `stepOutbox`. -/
inductive OutboxRefusal where
  | microkitIsolationFailed (reason : String)
  | invalidSpscChannel (channelId : Nat)
  | payloadExceedsChannelSlot (size maxBytes : Nat)
  | nonCanonicalNullifierWidth (nullifierId : Nat)
  | staleOrDuplicateNullifier (nullifierId highWater : Nat)
  | missingEscrowBond (nullifierId : Nat)
  | underfundedEscrowBond (funded rollback vaultBal : Nat)
  | missingFinalityCert (nullifierId : Nat)
  | invalidFinalityCert (nullifierId view : Nat)
  | unfinalizedOrMismatchedBlockCommit (nullifierId view : Nat)
  deriving DecidableEq, Repr

/-- Verify that `channelId` is a valid SPSC channel in `part` terminating at `gatekeeperPd`
    whose `maxPayloadBytes` accommodates `payloadSize`, and that the payload length fits the 8-byte
    length frame of `encodeEffectPreimage` (so its commitment binds it). -/
def checkSpscChannelToGatekeeper (part : SeL4MicrokitPartition) (gatekeeperPd : Nat)
    (channelId : Nat) (payloadSize : Nat) : Except OutboxRefusal Unit :=
  match part.channels.find? (fun ch => ch.channelId == channelId && ch.dstPd == gatekeeperPd) with
  | none => .error (.invalidSpscChannel channelId)
  | some ch =>
    if payloadSize ≤ ch.maxPayloadBytes && decide (payloadSize < OutboxBound64) then
      .ok ()
    else
      .error (.payloadExceedsChannelSlot payloadSize ch.maxPayloadBytes)

theorem checkSpscChannelToGatekeeper_bound {part : SeL4MicrokitPartition} {gatekeeperPd : Nat}
    {channelId payloadSize : Nat}
    (h : checkSpscChannelToGatekeeper part gatekeeperPd channelId payloadSize = .ok ()) :
    payloadSize < OutboxBound64 := by
  unfold checkSpscChannelToGatekeeper at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.2
    · cases h

/-- Check whether `chain` ends with `.block view expectedPayload`. -/
def checkChainTipCommit (chain : Chain) (view : Nat) (expectedPayload : Nat) : Bool :=
  match chain.getLast? with
  | some (.block v p) => decide (v = view) && decide (p = expectedPayload)
  | _ => false

theorem checkChainTipCommit_sound {chain : Chain} {view expectedPayload : Nat}
    (h : checkChainTipCommit chain view expectedPayload = true) :
    chain.getLast? = some (.block view expectedPayload) := by
  unfold checkChainTipCommit at h
  cases hLast : chain.getLast? with
  | none => rw [hLast] at h; cases h
  | some ent =>
    rw [hLast] at h
    cases ent with
    | dummy _ => cases h
    | block v p =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, h.2]

/-- Complete constructive auditor for a single outbox request against `(P, part, sent, st)`.
    Copies `req.spsc` to `privateCopy` **before** any verification and binds commitments strictly
    to `privateCopy`. -/
def auditOutboxStep (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent)
    (st : OutboxState) (req : OutboxEffectReq) : Except OutboxRefusal OutboxState :=
  if !checkMicrokitIsolation part then
    .error (.microkitIsolationFailed ((refuseMicrokitIsolation part).getD "refused: microkit-isolation"))
  else
    let privateCopy : ByteArray := copyRingToPrivateSlot req.spsc
    match checkSpscChannelToGatekeeper part st.gatekeeperPd req.spsc.channelId privateCopy.data.toList.length with
    | .error e => .error e
    | .ok () =>
      if !decide (req.nullifierId < OutboxBound64) then
        .error (.nonCanonicalNullifierWidth req.nullifierId)
      else
        match req.effectClass with
        | .idempotentRead =>
          .ok { st with readAuditCount := st.readAuditCount + 1 }
        | .compensatableEscrow =>
          if !decide (st.highWaterNullifier < req.nullifierId) then
            .error (.staleOrDuplicateNullifier req.nullifierId st.highWaterNullifier)
          else
            match req.escrowBond? with
            | none => .error (.missingEscrowBond req.nullifierId)
            | some bond =>
              if decide (0 < bond.rollbackCost ∧
                         bond.rollbackCost ≤ bond.fundedDeposit ∧
                         bond.fundedDeposit ≤ st.escrowVaultBalance) then
                let pending : PendingOptimisticEscrow :=
                  { nullifierId   := req.nullifierId
                    targetView    := req.targetView
                    optimisticTip := req.proposedChain
                    payload       := privateCopy
                    bond          := bond }
                .ok
                  { st with
                    highWaterNullifier := req.nullifierId
                    escrowVaultBalance := st.escrowVaultBalance - bond.fundedDeposit
                    activeEscrows      := pending :: st.activeEscrows }
              else
                .error (.underfundedEscrowBond bond.fundedDeposit bond.rollbackCost st.escrowVaultBalance)
        | .irreversibleActuation =>
          if !decide (st.highWaterNullifier < req.nullifierId) then
            .error (.staleOrDuplicateNullifier req.nullifierId st.highWaterNullifier)
          else
            match req.finCert? with
            | none => .error (.missingFinalityCert req.nullifierId)
            | some cert =>
              if !(cert.checks P sent &&
                   decide (cert.view = req.targetView) &&
                   decide (cert.chain = req.proposedChain)) then
                .error (.invalidFinalityCert req.nullifierId req.targetView)
              else
                let expectedCommit := effectCommitNat req.nullifierId .irreversibleActuation privateCopy
                if !checkChainTipCommit cert.chain cert.view expectedCommit then
                  .error (.unfinalizedOrMismatchedBlockCommit req.nullifierId cert.view)
                else
                  let act : DispatchedActuation :=
                    { nullifierId       := req.nullifierId
                      nullifierDigest   := deriveOutboxNullifier256 st.gatekeeperPd req.nullifierId
                      view              := cert.view
                      chain             := cert.chain
                      finCert           := cert
                      dispatchedPayload := privateCopy }
                  .ok
                    { st with
                      highWaterNullifier   := req.nullifierId
                      dispatchedActuations := act :: st.dispatchedActuations }

/-- Option-valued state transition wrapper for `auditOutboxStep`. -/
def stepOutbox (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent)
    (st : OutboxState) (req : OutboxEffectReq) : Option OutboxState :=
  match auditOutboxStep P part sent st req with
  | .ok st' => some st'
  | .error _ => none

/-! ## 3. Optimistic Escrow Rollback / Settlement Against Canonical Finality -/

/-- Reconcile pending `.compensatableEscrow` reservations when a canonical chain `canonChain` is
    finalized at view `canonView`:
    - Reservations at `targetView ≤ canonView` whose `optimisticTip` is a prefix of `canonChain`
      settle forward (`settledEscrowTotal` increases by `fundedDeposit`).
    - Reservations at `targetView ≤ canonView` whose `optimisticTip` was orphaned by view-skipping
      or a competing branch (`¬ optimisticTip <+: canonChain`) execute rollback compensation of
      `rollbackCost` (`settledEscrowTotal` absorbs `rollbackCost`) and refund `fundedDeposit - rollbackCost`
      back into `escrowVaultBalance`! -/
def reconcileEscrowList (canonView : Nat) (canonChain : Chain) :
    List PendingOptimisticEscrow → (List PendingOptimisticEscrow × Nat × Nat)
  | [] => ([], 0, 0)
  | e :: rest =>
    let (remRest, refundRest, settledRest) := reconcileEscrowList canonView canonChain rest
    if e.targetView ≤ canonView then
      if decide (e.optimisticTip <+: canonChain) then
        (remRest, refundRest, e.bond.fundedDeposit + settledRest)
      else
        let refund := e.bond.fundedDeposit - e.bond.rollbackCost
        let compPaid := e.bond.fundedDeposit - refund
        (remRest, refund + refundRest, compPaid + settledRest)
    else
      (e :: remRest, refundRest, settledRest)

theorem reconcileEscrowList_conserves (canonView : Nat) (canonChain : Chain) :
    ∀ (es : List PendingOptimisticEscrow),
      let (rem, refunded, settledOrComp) := reconcileEscrowList canonView canonChain es
      lockedEscrowDeposits rem + refunded + settledOrComp = lockedEscrowDeposits es
  | [] => rfl
  | e :: rest => by
    have ih := reconcileEscrowList_conserves canonView canonChain rest
    unfold reconcileEscrowList
    rcases hRec : reconcileEscrowList canonView canonChain rest with ⟨remRest, refundRest, settledRest⟩
    rw [hRec] at ih
    dsimp only at ih ⊢
    simp only [lockedEscrowDeposits]
    split
    · split
      · dsimp only; omega
      · dsimp only; omega
    · dsimp only [lockedEscrowDeposits]
      omega

/-- Reconcile `st.activeEscrows` against a verified `FinCert` on `sent`. -/
def reconcileEscrowsWithCert (P : Protocol) (sent : Sent) (cert : FinCert)
    (st : OutboxState) : Option OutboxState :=
  if cert.checks P sent then
    let (rem, refunded, settledOrComp) := reconcileEscrowList cert.view cert.chain st.activeEscrows
    some
      { st with
        escrowVaultBalance := st.escrowVaultBalance + refunded
        activeEscrows      := rem
        settledEscrowTotal := st.settledEscrowTotal + settledOrComp }
  else
    none

theorem reconcileEscrowsWithCert_conserves {P : Protocol} {sent : Sent} {cert : FinCert}
    {st st' : OutboxState}
    (h : reconcileEscrowsWithCert P sent cert st = some st') :
    Finalized P sent cert.view cert.chain ∧
    st'.escrowVaultBalance + lockedEscrowDeposits st'.activeEscrows + st'.settledEscrowTotal =
      st.escrowVaultBalance + lockedEscrowDeposits st.activeEscrows + st.settledEscrowTotal ∧
    st'.dispatchedActuations = st.dispatchedActuations ∧
    st'.highWaterNullifier = st.highWaterNullifier := by
  unfold reconcileEscrowsWithCert at h
  split at h
  · rename_i hChk
    injection h with hEq
    subst hEq
    have hCons := reconcileEscrowList_conserves cert.view cert.chain st.activeEscrows
    refine ⟨FinCert.checks_implies_finalized hChk, ?_, rfl, rfl⟩
    dsimp only at hCons ⊢
    omega
  · cases h

/-! ## 4. Open-World Environment Anti-Narrowing Completeness -/

/-- **Environment Anti-Narrowing Completeness (`outboxStep_skip_implies_violation`)**:
    Whenever `stepOutbox P part sent st req = none`, `auditOutboxStep` emits an explicit named
    `OutboxRefusal` AND at least one concrete safety precondition is genuinely violated! -/
theorem outboxStep_skip_implies_violation
    (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent)
    (st : OutboxState) (req : OutboxEffectReq)
    (hSkip : stepOutbox P part sent st req = none) :
    (∃ r : OutboxRefusal, auditOutboxStep P part sent st req = .error r) ∧
    (checkMicrokitIsolation part = false ∨
     (checkSpscChannelToGatekeeper part st.gatekeeperPd req.spsc.channelId
        (copyRingToPrivateSlot req.spsc).data.toList.length).isOk = false ∨
     OutboxBound64 ≤ req.nullifierId ∨
     (req.effectClass ≠ .idempotentRead ∧ req.nullifierId ≤ st.highWaterNullifier) ∨
     (req.effectClass = .compensatableEscrow ∧
       (req.escrowBond?.isNone = true ∨
        ∃ b, req.escrowBond? = some b ∧
          ¬ (0 < b.rollbackCost ∧ b.rollbackCost ≤ b.fundedDeposit ∧ b.fundedDeposit ≤ st.escrowVaultBalance))) ∨
     (req.effectClass = .irreversibleActuation ∧
       (req.finCert?.isNone = true ∨
        ∃ cert, req.finCert? = some cert ∧
          (cert.checks P sent = false ∨
           cert.view ≠ req.targetView ∨
           cert.chain ≠ req.proposedChain ∨
           checkChainTipCommit cert.chain cert.view
             (effectCommitNat req.nullifierId .irreversibleActuation (copyRingToPrivateSlot req.spsc)) = false)))) := by
  unfold stepOutbox at hSkip
  cases hAud : auditOutboxStep P part sent st req with
  | ok st' =>
    rw [hAud] at hSkip; cases hSkip
  | error r =>
    refine ⟨⟨r, rfl⟩, ?_⟩
    unfold auditOutboxStep at hAud
    cases hIso : checkMicrokitIsolation part with
    | false =>
      exact .inl rfl
    | true =>
      rw [hIso] at hAud
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
      cases hCh : checkSpscChannelToGatekeeper part st.gatekeeperPd req.spsc.channelId
          (copyRingToPrivateSlot req.spsc).data.toList.length with
      | error e =>
        right; left
        rfl
      | ok u =>
        cases u
        rw [hCh] at hAud
        dsimp only at hAud
        by_cases hBound : req.nullifierId < OutboxBound64
        · simp only [decide_eq_true hBound, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
          cases hCls : req.effectClass with
          | idempotentRead =>
            rw [hCls] at hAud; cases hAud
          | compensatableEscrow =>
            rw [hCls] at hAud
            dsimp only at hAud
            by_cases hMono : st.highWaterNullifier < req.nullifierId
            · simp only [decide_eq_true hMono, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
              cases hBond : req.escrowBond? with
              | none =>
                right; right; right; right; left
                exact ⟨rfl, .inl rfl⟩
              | some b =>
                rw [hBond] at hAud
                dsimp only at hAud
                split at hAud
                · cases hAud
                · rename_i hBadBond
                  right; right; right; right; left
                  exact ⟨rfl, .inr ⟨b, rfl, fun hOk => hBadBond (decide_eq_true hOk)⟩⟩
            · right; right; right; left
              exact ⟨by decide, by omega⟩
          | irreversibleActuation =>
            rw [hCls] at hAud
            dsimp only at hAud
            by_cases hMono : st.highWaterNullifier < req.nullifierId
            · simp only [decide_eq_true hMono, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
              cases hCert : req.finCert? with
              | none =>
                right; right; right; right; right
                exact ⟨rfl, .inl rfl⟩
              | some cert =>
                rw [hCert] at hAud
                dsimp only at hAud
                by_cases hCertOk :
                    (cert.checks P sent && decide (cert.view = req.targetView) &&
                     decide (cert.chain = req.proposedChain)) = true
                · rw [hCertOk] at hAud
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
                  cases hTip : checkChainTipCommit cert.chain cert.view
                      (effectCommitNat req.nullifierId .irreversibleActuation (copyRingToPrivateSlot req.spsc)) with
                  | true =>
                    rw [hTip] at hAud; cases hAud
                  | false =>
                    right; right; right; right; right
                    exact ⟨rfl, .inr ⟨cert, rfl, .inr (.inr (.inr hTip))⟩⟩
                · right; right; right; right; right
                  refine ⟨rfl, .inr ⟨cert, rfl, ?_⟩⟩
                  cases hChk : cert.checks P sent with
                  | false => exact .inl rfl
                  | true =>
                    by_cases hv : cert.view = req.targetView
                    · by_cases hc : cert.chain = req.proposedChain
                      · exfalso
                        apply hCertOk
                        simp [hChk, hv, hc]
                      · exact .inr (.inr (.inl hc))
                    · exact .inr (.inl hv)
            · right; right; right; left
              exact ⟨by decide, by omega⟩
        · right; right; left
          omega

/-- **Converse Step Completeness (`outboxStep_complete`)**:
    Every `.irreversibleActuation` request with an isolated `SeL4MicrokitPartition`, valid SPSC
    channel, fresh monotonic nullifier `< 2^64`, and valid `FinCert` committing to `privateCopy`
    is deterministically admitted by `stepOutbox`! -/
theorem outboxStep_complete
    (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent)
    (st : OutboxState) (req : OutboxEffectReq) (cert : FinCert)
    (hCls : req.effectClass = .irreversibleActuation)
    (hIso : checkMicrokitIsolation part = true)
    (hChan : checkSpscChannelToGatekeeper part st.gatekeeperPd req.spsc.channelId
              (copyRingToPrivateSlot req.spsc).data.toList.length = .ok ())
    (hWidth : req.nullifierId < OutboxBound64)
    (hFresh : st.highWaterNullifier < req.nullifierId)
    (hCertSome : req.finCert? = some cert)
    (hCertChk : cert.checks P sent = true)
    (hView : cert.view = req.targetView)
    (hChain : cert.chain = req.proposedChain)
    (hTip : checkChainTipCommit cert.chain cert.view
              (effectCommitNat req.nullifierId .irreversibleActuation (copyRingToPrivateSlot req.spsc)) = true) :
    ∃ st' : OutboxState, stepOutbox P part sent st req = some st' := by
  unfold stepOutbox auditOutboxStep
  rw [hIso]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hChan]
  dsimp only
  simp only [decide_eq_true hWidth, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCls,
    decide_eq_true hFresh, hCertSome, hCertChk, decide_eq_true hView, decide_eq_true hChain,
    Bool.and_self, hTip]
  exact ⟨_, rfl⟩

/-! ## 5. Multi-Turn / Multi-View Trace Model (`ValidOutboxTrace`) & Safety Metatheorems -/

/-- Reflexive-transitive closure of `SimplexProtocol.Step P` from `sent₁` to `sent₂`, modeling
    arbitrary multi-message Byzantine network evolution (including `Step.inject`, `.dummy` view
    skips, and competing unfinalized branches) between outbox turns! -/
inductive SentSteps (P : Protocol) : Sent → Sent → Prop
  | refl (s : Sent) : SentSteps P s s
  | step {s₁ s₂ s₃ : Sent} (h₁₂ : SentSteps P s₁ s₂) (hs : Step P s₂ s₃) : SentSteps P s₁ s₃

theorem sentSteps_reach {P : Protocol} {s₁ s₂ : Sent}
    (hr : Reach P s₁) (hSteps : SentSteps P s₁ s₂) : Reach P s₂ := by
  induction hSteps with
  | refl => exact hr
  | step _ hs ih => exact Reach.step ih hs

theorem sentSteps_trans {P : Protocol} {s₁ s₂ s₃ : Sent}
    (h₁₂ : SentSteps P s₁ s₂) (h₂₃ : SentSteps P s₂ s₃) : SentSteps P s₁ s₃ := by
  induction h₂₃ with
  | refl => exact h₁₂
  | step _ hs ih => exact SentSteps.step ih hs

private theorem step_preserves_mem {P : Protocol} {s₁ s₂ : Sent} (hs : Step P s₁ s₂) :
    ∀ m ∈ s₁, m ∈ s₂ := by
  cases hs <;> intro m hm <;> exact List.mem_cons_of_mem _ hm

theorem sentSteps_preserves_mem {P : Protocol} {s₁ s₂ : Sent} (hSteps : SentSteps P s₁ s₂) :
    ∀ m ∈ s₁, m ∈ s₂ := by
  induction hSteps with
  | refl => intro _ hm; exact hm
  | step _ hs ih => intro m hm; exact step_preserves_mem hs m (ih m hm)

/-- Monotonicity of `SimplexProtocol.Finalized` across arbitrary `SentSteps`. -/
theorem finalized_mono_sentSteps {P : Protocol} {s₁ s₂ : Sent}
    (hSteps : SentSteps P s₁ s₂) {v : Nat} {c : Chain}
    (hf : Finalized P s₁ v c) : Finalized P s₂ v c :=
  finalized_mono (sentSteps_preserves_mem hSteps) hf

/-- One turn of a multi-view outbox execution: consensus advances from the previous `Sent` to
    `nextSent` via `SentSteps`, and the outbox processes `req` (optionally followed by escrow
    reconciliation against an optional `reconcileCert?`). -/
structure OutboxTurn where
  nextSent       : Sent
  req            : OutboxEffectReq
  reconcileCert? : Option FinCert := none

/-- Multi-turn / multi-view outbox execution predicate (`ValidOutboxTrace`):
    starting from `(sent₀, st₀)` with `Reach P sent₀`, each turn advances `sent` via valid
    `SentSteps P` (allowing arbitrary faulty injections and competing unfinalized branches) and
    transitions `st` via `stepOutbox` (plus optional `reconcileEscrowsWithCert`). -/
def ValidOutboxTrace (P : Protocol) (part : SeL4MicrokitPartition) :
    Sent → OutboxState → List OutboxTurn → Sent → OutboxState → Prop
  | sent₀, st₀, [], sentF, stF =>
    sentF = sent₀ ∧
    stF = st₀ ∧
    Reach P sent₀ ∧
    checkMicrokitIsolation part = true
  | sent₀, st₀, turn :: rest, sentF, stF =>
    Reach P sent₀ ∧
    SentSteps P sent₀ turn.nextSent ∧
    ∃ (stMid st₁ : OutboxState),
      stepOutbox P part turn.nextSent st₀ turn.req = some stMid ∧
      (match turn.reconcileCert? with
       | none => st₁ = stMid
       | some cert => reconcileEscrowsWithCert P turn.nextSent cert stMid = some st₁) ∧
      ValidOutboxTrace P part turn.nextSent st₁ rest sentF stF

theorem validOutboxTrace_nil {P : Protocol} {part : SeL4MicrokitPartition} {sent₀ sentF : Sent}
    {st₀ stF : OutboxState} :
    ValidOutboxTrace P part sent₀ st₀ [] sentF stF ↔
      sentF = sent₀ ∧ stF = st₀ ∧ Reach P sent₀ ∧ checkMicrokitIsolation part = true :=
  ⟨fun h => h, fun h => h⟩

theorem validOutboxTrace_cons {P : Protocol} {part : SeL4MicrokitPartition} {sent₀ sentF : Sent}
    {st₀ stF : OutboxState} {turn : OutboxTurn} {rest : List OutboxTurn} :
    ValidOutboxTrace P part sent₀ st₀ (turn :: rest) sentF stF ↔
      Reach P sent₀ ∧ SentSteps P sent₀ turn.nextSent ∧
      ∃ (stMid st₁ : OutboxState),
        stepOutbox P part turn.nextSent st₀ turn.req = some stMid ∧
        (match turn.reconcileCert? with
         | none => st₁ = stMid
         | some cert => reconcileEscrowsWithCert P turn.nextSent cert stMid = some st₁) ∧
        ValidOutboxTrace P part turn.nextSent st₁ rest sentF stF :=
  ⟨fun h => h, fun h => h⟩

private theorem stepOutbox_invariants
    {P : Protocol} {part : SeL4MicrokitPartition} {sent : Sent}
    {st st' : OutboxState} {req : OutboxEffectReq}
    (hStep : stepOutbox P part sent st req = some st') :
    (checkMicrokitIsolation part = true ∧
      (req.effectClass ≠ .idempotentRead → st.highWaterNullifier < req.nullifierId)) ∧
    st.highWaterNullifier ≤ st'.highWaterNullifier ∧
    st'.escrowVaultBalance + lockedEscrowDeposits st'.activeEscrows + st'.settledEscrowTotal =
      st.escrowVaultBalance + lockedEscrowDeposits st.activeEscrows + st.settledEscrowTotal ∧
    (∀ e ∈ st'.activeEscrows, e ∈ st.activeEscrows ∨
      (req.effectClass = .compensatableEscrow ∧
       0 < e.bond.rollbackCost ∧
       e.bond.rollbackCost ≤ e.bond.fundedDeposit ∧
       e.payload = req.spsc.sharedRingBeforeCopy)) ∧
    ((st'.dispatchedActuations = st.dispatchedActuations) ∨
     (∃ act : DispatchedActuation,
       req.effectClass = .irreversibleActuation ∧
       st'.dispatchedActuations = act :: st.dispatchedActuations ∧
       st.highWaterNullifier < act.nullifierId ∧
       st'.highWaterNullifier = act.nullifierId ∧
       act.nullifierId = req.nullifierId ∧
       (act.nullifierId < OutboxBound64 ∧
         act.dispatchedPayload.data.toList.length < OutboxBound64) ∧
       act.dispatchedPayload = req.spsc.sharedRingBeforeCopy ∧
       act.finCert.checks P sent = true ∧
       Finalized P sent act.view act.chain ∧
       act.view = act.finCert.view ∧
       act.chain = act.finCert.chain ∧
       act.chain.getLast? = some (.block act.view
         (effectCommitNat act.nullifierId .irreversibleActuation act.dispatchedPayload)))) := by
  unfold stepOutbox at hStep
  cases hAud : auditOutboxStep P part sent st req with
  | error _ => rw [hAud] at hStep; cases hStep
  | ok out =>
    rw [hAud] at hStep
    injection hStep with hOutEq
    subst hOutEq
    unfold auditOutboxStep at hAud
    cases hIso : checkMicrokitIsolation part with
    | false =>
      rw [hIso] at hAud; simp at hAud
    | true =>
      rw [hIso] at hAud
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
      cases hCh : checkSpscChannelToGatekeeper part st.gatekeeperPd req.spsc.channelId
          (copyRingToPrivateSlot req.spsc).data.toList.length with
      | error _ => rw [hCh] at hAud; cases hAud
      | ok u =>
        cases u
        rw [hCh] at hAud; dsimp only at hAud
        split at hAud
        · cases hAud
        · rename_i hWidthNeg
          have hWidth : req.nullifierId < OutboxBound64 := by
            cases hw : decide (req.nullifierId < OutboxBound64) with
            | false => rw [hw] at hWidthNeg; simp at hWidthNeg
            | true => exact of_decide_eq_true hw
          cases hCls : req.effectClass with
          | idempotentRead =>
            rw [hCls] at hAud
            injection hAud with hSt
            subst hSt
            exact ⟨⟨rfl, fun h => absurd rfl h⟩, Nat.le_refl _, rfl, fun _ h => .inl h, .inl rfl⟩
          | compensatableEscrow =>
            rw [hCls] at hAud; dsimp only at hAud
            split at hAud
            · cases hAud
            · rename_i hMonoNeg
              have hMono : st.highWaterNullifier < req.nullifierId := by
                cases hm : decide (st.highWaterNullifier < req.nullifierId) with
                | false => rw [hm] at hMonoNeg; simp at hMonoNeg
                | true => exact of_decide_eq_true hm
              cases hBond : req.escrowBond? with
              | none => rw [hBond] at hAud; cases hAud
              | some bond =>
                rw [hBond] at hAud; dsimp only at hAud
                split at hAud
                · rename_i hBondOkDec
                  have hBondOk := of_decide_eq_true hBondOkDec
                  injection hAud with hSt
                  subst hSt
                  refine ⟨⟨rfl, fun _ => hMono⟩, by dsimp; omega, ?_, ?_, .inl rfl⟩
                  · dsimp [lockedEscrowDeposits]; omega
                  · intro e he
                    rcases List.mem_cons.1 he with rfl | hOld
                    · exact .inr ⟨rfl, hBondOk.1, hBondOk.2.1, rfl⟩
                    · exact .inl hOld
                · cases hAud
          | irreversibleActuation =>
            rw [hCls] at hAud; dsimp only at hAud
            split at hAud
            · cases hAud
            · rename_i hMonoNeg
              have hMono : st.highWaterNullifier < req.nullifierId := by
                cases hm : decide (st.highWaterNullifier < req.nullifierId) with
                | false => rw [hm] at hMonoNeg; simp at hMonoNeg
                | true => exact of_decide_eq_true hm
              cases hCert : req.finCert? with
              | none => rw [hCert] at hAud; cases hAud
              | some cert =>
                rw [hCert] at hAud; dsimp only at hAud
                split at hAud
                · cases hAud
                · rename_i hCertNeg
                  have hCertOk :
                      cert.checks P sent = true ∧
                      cert.view = req.targetView ∧
                      cert.chain = req.proposedChain := by
                    cases hc : (cert.checks P sent && decide (cert.view = req.targetView) &&
                                decide (cert.chain = req.proposedChain)) with
                    | false => rw [hc] at hCertNeg; simp at hCertNeg
                    | true =>
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                      exact ⟨hc.1.1, hc.1.2, hc.2⟩
                  split at hAud
                  · cases hAud
                  · rename_i hTipNeg
                    have hTipOk :
                        checkChainTipCommit cert.chain cert.view
                          (effectCommitNat req.nullifierId .irreversibleActuation
                            (copyRingToPrivateSlot req.spsc)) = true := by
                      cases ht : checkChainTipCommit cert.chain cert.view
                          (effectCommitNat req.nullifierId .irreversibleActuation
                            (copyRingToPrivateSlot req.spsc)) with
                      | false => rw [ht] at hTipNeg; simp at hTipNeg
                      | true => rfl
                    injection hAud with hSt
                    subst hSt
                    refine ⟨⟨rfl, fun _ => hMono⟩, by dsimp; omega, rfl, fun _ h => .inl h, .inr ?_⟩
                    refine ⟨_, rfl, rfl, hMono, rfl, rfl,
                      ⟨hWidth, checkSpscChannelToGatekeeper_bound hCh⟩, rfl, hCertOk.1,
                      FinCert.checks_implies_finalized hCertOk.1, rfl, rfl, ?_⟩
                    exact checkChainTipCommit_sound hTipOk

private theorem reconcileEscrowList_mem_sub (canonView : Nat) (canonChain : Chain) :
    ∀ (es : List PendingOptimisticEscrow) {x : PendingOptimisticEscrow},
      x ∈ (reconcileEscrowList canonView canonChain es).1 → x ∈ es
  | [], _, hx => hx
  | hd :: tl, x, hx => by
    unfold reconcileEscrowList at hx
    rcases hRec : reconcileEscrowList canonView canonChain tl with ⟨remRest, refundRest, settledRest⟩
    rw [hRec] at hx
    dsimp only at hx
    split at hx
    · split at hx
      · exact List.mem_cons_of_mem hd (reconcileEscrowList_mem_sub canonView canonChain tl (by simpa [hRec] using hx))
      · exact List.mem_cons_of_mem hd (reconcileEscrowList_mem_sub canonView canonChain tl (by simpa [hRec] using hx))
    · rcases List.mem_cons.1 hx with rfl | hTl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem hd (reconcileEscrowList_mem_sub canonView canonChain tl (by simpa [hRec] using hTl))

private theorem reconcileOpt_preserves
    {P : Protocol} {sent : Sent} {stMid st₁ : OutboxState} {rec? : Option FinCert}
    (hRec : match rec? with
            | none => st₁ = stMid
            | some cert => reconcileEscrowsWithCert P sent cert stMid = some st₁) :
    st₁.escrowVaultBalance + lockedEscrowDeposits st₁.activeEscrows + st₁.settledEscrowTotal =
      stMid.escrowVaultBalance + lockedEscrowDeposits stMid.activeEscrows + stMid.settledEscrowTotal ∧
    st₁.dispatchedActuations = stMid.dispatchedActuations ∧
    st₁.highWaterNullifier = stMid.highWaterNullifier ∧
    (∀ e ∈ st₁.activeEscrows, e ∈ stMid.activeEscrows) := by
  cases rec? with
  | none =>
    dsimp only at hRec
    subst hRec
    exact ⟨rfl, rfl, rfl, fun _ h => h⟩
  | some cert =>
    dsimp only at hRec
    have hCons := reconcileEscrowsWithCert_conserves hRec
    refine ⟨hCons.2.1, hCons.2.2.1, hCons.2.2.2, ?_⟩
    unfold reconcileEscrowsWithCert at hRec
    cases hChk : cert.checks P sent with
    | false =>
      rw [hChk] at hRec
      simp at hRec
    | true =>
      rw [hChk] at hRec
      simp only [↓reduceIte] at hRec
      rcases hList : reconcileEscrowList cert.view cert.chain stMid.activeEscrows with ⟨rem, refunded, settledOrComp⟩
      rw [hList] at hRec
      injection hRec with hEq
      subst hEq
      intro e he
      exact reconcileEscrowList_mem_sub cert.view cert.chain stMid.activeEscrows (by simpa [hList] using he)

/-- Core inductive trace invariant for `ValidOutboxTrace`. -/
private theorem validOutboxTrace_core
    {P : Protocol} {part : SeL4MicrokitPartition}
    {sentF : Sent} {stF : OutboxState} :
    ∀ (turns : List OutboxTurn) {sent₀ : Sent} {st₀ : OutboxState},
      ValidOutboxTrace P part sent₀ st₀ turns sentF stF →
      (∀ a ∈ st₀.dispatchedActuations,
        a.nullifierId ≤ st₀.highWaterNullifier ∧ Finalized P sent₀ a.view a.chain) →
      (st₀.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup →
      Reach P sentF ∧
      SentSteps P sent₀ sentF ∧
      checkMicrokitIsolation part = true ∧
      st₀.highWaterNullifier ≤ stF.highWaterNullifier ∧
      stF.escrowVaultBalance + lockedEscrowDeposits stF.activeEscrows + stF.settledEscrowTotal =
        st₀.escrowVaultBalance + lockedEscrowDeposits st₀.activeEscrows + st₀.settledEscrowTotal ∧
      (stF.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
      (∀ a ∈ stF.dispatchedActuations,
        a.nullifierId ≤ stF.highWaterNullifier ∧
        Finalized P sentF a.view a.chain ∧
        (a ∈ st₀.dispatchedActuations ∨
         (st₀.highWaterNullifier < a.nullifierId ∧
          (a.nullifierId < OutboxBound64 ∧
            a.dispatchedPayload.data.toList.length < OutboxBound64) ∧
          a.chain.getLast? = some (.block a.view
            (effectCommitNat a.nullifierId .irreversibleActuation a.dispatchedPayload)) ∧
          ∃ t ∈ turns,
            t.req.effectClass = .irreversibleActuation ∧
            a.nullifierId = t.req.nullifierId ∧
            a.dispatchedPayload = t.req.spsc.sharedRingBeforeCopy)))
  | [], sent₀, st₀, hTrace, hInitBounded, hInitNodup => by
    rcases hTrace with ⟨rfl, rfl, hReach₀, hIso⟩
    refine ⟨hReach₀, SentSteps.refl _, hIso, Nat.le_refl _, rfl, hInitNodup, ?_⟩
    intro a ha
    obtain ⟨hLe, hFin⟩ := hInitBounded a ha
    exact ⟨hLe, hFin, .inl ha⟩
  | turn :: rest, sent₀, st₀, hTrace, hInitBounded, hInitNodup => by
    rcases hTrace with ⟨_, hNet, stMid, st₁, hStep, hRec, hRest⟩
    let sent₁ := turn.nextSent
    obtain ⟨hIso, hHwStep, hEscStep, _, hActStep⟩ := stepOutbox_invariants hStep
    obtain ⟨hEscRec, hActRec, hHwRec, _⟩ := reconcileOpt_preserves hRec
    have hMidBounded : ∀ a ∈ st₁.dispatchedActuations,
        a.nullifierId ≤ st₁.highWaterNullifier ∧ Finalized P sent₁ a.view a.chain := by
      rw [hActRec, hHwRec]
      rcases hActStep with hSame | ⟨act, _, hConsEq, _, hHwEq, _, _, _, _, hFinAct, _, _, _⟩
      · rw [hSame]
        intro a ha
        obtain ⟨hLe₀, hFin₀⟩ := hInitBounded a ha
        exact ⟨Nat.le_trans hLe₀ hHwStep, finalized_mono_sentSteps hNet hFin₀⟩
      · rw [hConsEq, hHwEq]
        intro a ha
        rcases List.mem_cons.1 ha with rfl | haOld
        · exact ⟨Nat.le_refl _, hFinAct⟩
        · obtain ⟨hLe₀, hFin₀⟩ := hInitBounded a haOld
          exact ⟨by omega, finalized_mono_sentSteps hNet hFin₀⟩
    have hMidNodup : (st₁.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup := by
      rw [hActRec]
      rcases hActStep with hSame | ⟨act, _, hConsEq, hStrict, _, _, _, _, _, _, _, _, _⟩
      · rw [hSame]; exact hInitNodup
      · rw [hConsEq]
        simp only [List.map_cons]
        refine List.Pairwise.cons ?_ hInitNodup
        intro x hx hEqX
        obtain ⟨oldAct, hOldMem, rfl⟩ := List.mem_map.1 hx
        have hOldLe := (hInitBounded oldAct hOldMem).1
        omega
    obtain ⟨hReachF, hNetRest, _, hHwRest, hEscRest, hNodupF, hActsF⟩ :=
      validOutboxTrace_core rest hRest hMidBounded hMidNodup
    have hNetFull : SentSteps P sent₀ sentF := sentSteps_trans hNet hNetRest
    refine ⟨hReachF, hNetFull, hIso.1, ?_, ?_, hNodupF, ?_⟩
    · omega
    · omega
    · intro a haF
      obtain ⟨hLeF, hFinF, hOrigin⟩ := hActsF a haF
      refine ⟨hLeF, hFinF, ?_⟩
      rcases hOrigin with haIn₁ | ⟨hGt₁, hW, hTip, t, htInRest, hClsT, hIdT, hPayT⟩
      · rw [hActRec] at haIn₁
        rcases hActStep with hSame | ⟨act, hClsTurn, hConsEq, hStrict, _, hIdTurn, hWTurn, hPayTurn, _, _, _, _, hTipTurn⟩
        · rw [hSame] at haIn₁
          exact .inl haIn₁
        · rw [hConsEq] at haIn₁
          rcases List.mem_cons.1 haIn₁ with rfl | haOld
          · exact .inr ⟨hStrict, hWTurn, hTipTurn, turn, List.mem_cons_self, hClsTurn, hIdTurn, hPayTurn⟩
          · exact .inl haOld
      · refine .inr ⟨?_, hW, hTip, t, List.mem_cons_of_mem turn htInRest, hClsT, hIdT, hPayT⟩
        omega

/-- **Theorem 1: At-Most-Once Irreversibility & Zero Rollback (`irreversible_at_most_once_and_never_rolled_back`)**:
    Across any multi-turn / multi-view `ValidOutboxTrace` starting from clean initial outbox state
    (`st₀.dispatchedActuations = []`):
    1. **At-Most-Once Nullifier Discipline**: `(stF.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup` —
       no irreversible `nullifierId` can ever fire twice!
    2. **Canonical ChainConsistency**: every two dispatched actuations `a₁, a₂` lie on prefix-consistent
       finalized chains (`a₁.chain <+: a₂.chain ∨ a₂.chain <+: a₁.chain`) and agree identically per block height.
    3. **Never Rolled Back / Never Orphaned**: for *any* canonical chain `cCanon` finalized in any later or
       concurrent view `vCanon ≥ a.view` in `sentF`, `a.chain <+: cCanon` — no competing branch or Byzantine
       view-skip can ever orphan or roll back a dispatched `.irreversibleActuation`! -/
theorem irreversible_at_most_once_and_never_rolled_back
    {P : Protocol} {part : SeL4MicrokitPartition}
    {sent₀ sentF : Sent} {st₀ stF : OutboxState} {turns : List OutboxTurn}
    (hClean : st₀.dispatchedActuations = [])
    (hTrace : ValidOutboxTrace P part sent₀ st₀ turns sentF stF) :
    (stF.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    (∀ a₁ ∈ stF.dispatchedActuations, ∀ a₂ ∈ stF.dispatchedActuations,
      a₁.chain <+: a₂.chain ∨ a₂.chain <+: a₁.chain) ∧
    (∀ a ∈ stF.dispatchedActuations, ∀ (vCanon : Nat) (cCanon : Chain),
      Finalized P sentF vCanon cCanon →
      a.view ≤ vCanon →
      a.chain <+: cCanon) := by
  have hInitB : ∀ a ∈ st₀.dispatchedActuations,
      a.nullifierId ≤ st₀.highWaterNullifier ∧ Finalized P sent₀ a.view a.chain := by
    rw [hClean]; intro _ h; cases h
  have hInitNd : (st₀.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup := by
    rw [hClean]; exact List.Pairwise.nil
  obtain ⟨hReachF, _, _, _, _, hNodupF, hActsF⟩ := validOutboxTrace_core turns hTrace hInitB hInitNd
  have hInvF : Inv P sentF := reach_inv hReachF
  refine ⟨hNodupF, ?_, ?_⟩
  · intro a₁ ha₁ a₂ ha₂
    exact finalized_consistent hInvF (hActsF a₁ ha₁).2.1 (hActsF a₂ ha₂).2.1
  · intro a ha vCanon cCanon hFinCanon hViewLe
    have hLenCanon : cCanon.length = vCanon := finalized_length hInvF hFinCanon
    have hNotCanon : ChainNotarized P sentF cCanon := finalized_chainNotarized hInvF hFinCanon
    exact finalized_prefix_of_notarized hInvF (hActsF a ha).2.1 hNotCanon (by omega)

/-- A request that is not a read and whose nullifier is at or below the high-water mark is
    refused, against any message list. -/
theorem stepOutbox_refuses_spent_nullifier (P : Protocol) (part : SeL4MicrokitPartition)
    (sent : Sent) (st : OutboxState) (req : OutboxEffectReq)
    (hCls : req.effectClass ≠ .idempotentRead)
    (hSpent : req.nullifierId ≤ st.highWaterNullifier) :
    stepOutbox P part sent st req = none := by
  cases h : stepOutbox P part sent st req with
  | none => rfl
  | some st' => exact absurd ((stepOutbox_invariants h).1.2 hCls) (by omega)

/-- **A dispatched nullifier never fires again.** After any `ValidOutboxTrace` from a clean
    outbox, a further non-read request under the nullifier of any dispatched actuation is refused,
    whatever message list and certificate it brings. The outbox state is the whole of what this
    rests on, so it holds across anything that preserves that state (a crash and recovery of a
    host that journals it: `UnifiedDeos.durable_outbox_dispatch_once_across_crashes`). -/
theorem dispatched_nullifier_never_replays
    {P : Protocol} {part : SeL4MicrokitPartition}
    {sent₀ sentF : Sent} {st₀ stF : OutboxState} {turns : List OutboxTurn}
    (hClean : st₀.dispatchedActuations = [])
    (hTrace : ValidOutboxTrace P part sent₀ st₀ turns sentF stF) :
    ∀ a ∈ stF.dispatchedActuations, ∀ (P' : Protocol) (sent : Sent) (req : OutboxEffectReq),
      req.effectClass ≠ .idempotentRead → req.nullifierId = a.nullifierId →
      stepOutbox P' part sent stF req = none := by
  have hInitB : ∀ a ∈ st₀.dispatchedActuations,
      a.nullifierId ≤ st₀.highWaterNullifier ∧ Finalized P sent₀ a.view a.chain := by
    rw [hClean]; intro _ h; cases h
  have hInitNd : (st₀.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup := by
    rw [hClean]; exact List.Pairwise.nil
  obtain ⟨_, _, _, _, _, _, hActsF⟩ := validOutboxTrace_core turns hTrace hInitB hInitNd
  intro a ha P' sent req hCls hId
  exact stepOutbox_refuses_spent_nullifier P' part sent stF req hCls (hId ▸ (hActsF a ha).1)

/-- **No TOCTOU, stated over the finalized state.** After any `ValidOutboxTrace` from a clean
    outbox, take a dispatched actuation `a` and any other byte string of framed length (what a
    producer or DMA wrote to the shared ring after verification, for one). If that string's
    commitment under `a`'s nullifier is the payload of `a`'s finalized block, it is the dispatched
    payload, or the two are an explicit cSHAKE256 collision. No bytes but the dispatched ones are
    consistent with what consensus finalized. -/
theorem dispatched_payload_bound_to_finalized_commit
    {P : Protocol} {part : SeL4MicrokitPartition}
    {sent₀ sentF : Sent} {st₀ stF : OutboxState} {turns : List OutboxTurn}
    (hClean : st₀.dispatchedActuations = [])
    (hTrace : ValidOutboxTrace P part sent₀ st₀ turns sentF stF) :
    ∀ a ∈ stF.dispatchedActuations, ∀ other : ByteArray,
      other.data.toList.length < OutboxBound64 →
      a.chain.getLast? = some (.block a.view
        (effectCommitNat a.nullifierId .irreversibleActuation other)) →
      other = a.dispatchedPayload ∨
        HashBytes.Collision (cshake256Bytes outboxEffectDomain.data.toList) := by
  have hInitB : ∀ a ∈ st₀.dispatchedActuations,
      a.nullifierId ≤ st₀.highWaterNullifier ∧ Finalized P sent₀ a.view a.chain := by
    rw [hClean]; intro _ h; cases h
  have hInitNd : (st₀.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup := by
    rw [hClean]; exact List.Pairwise.nil
  obtain ⟨_, _, _, _, _, _, hActsF⟩ := validOutboxTrace_core turns hTrace hInitB hInitNd
  intro a ha other hLen hTipOther
  rcases (hActsF a ha).2.2 with haOld | ⟨_, hW, hTip, _⟩
  · rw [hClean] at haOld; cases haOld
  · rw [hTip] at hTipOther
    injection hTipOther with hEntry
    injection hEntry with _ hCommit
    rcases effectCommitNat_binding hW.1 hW.1 hW.2 hLen hCommit with ⟨_, _, hEq⟩ | hCol
    · exact .inl hEq.symm
    · exact .inr hCol

/-- **Pillar 6 Apex Theorem (`firmament_sel4_copy_before_verify_and_irreversible_outbox_safe`)**:
    End-to-end multi-turn / multi-view safety of `seL4` Microkit Copy-Before-Verify SPSC isolation
    and 3-class irreversible outbox settlement over `SimplexProtocol`:
    1. **`seL4` Microkit capDL Non-Interference**: `Sel4CapDlNonInterfering part` holds (disjoint
       writable MMIO, exclusive hardware watchdog confinement, bounded SPSC channels);
    2. **SPSC Copy-Before-Verify**: every dispatched `.irreversibleActuation`
       `a ∈ stF.dispatchedActuations` dispatches the private-snapshot bytes
       `a.dispatchedPayload = t.req.spsc.sharedRingBeforeCopy`, whose 256-bit cSHAKE256
       `effectCommitNat` is the committed payload of the finalized non-dummy block tip
       `a.chain.getLast? = some (.block a.view (...))` (and by
       `dispatched_payload_bound_to_finalized_commit` no other bytes fit that commitment);
    3. **Canonical `SimplexProtocol` Finality, Uniqueness & Zero Orphan/Replay**:
       - `(stF.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup`,
       - Every `a ∈ stF.dispatchedActuations` satisfies `Finalized P sentF a.view a.chain`,
       - Equal-height actuations certify identical block sequences (`a₁.chain.blocks = a₂.chain.blocks`),
       - Every later canonical finalized chain `cCanon` (`vCanon ≥ a.view`) contains `a.chain` as an
         immutable prefix (`a.chain <+: cCanon`);
    4. **Exact Escrow Vault Conservation**: `stF.escrowVaultBalance + lockedEscrowDeposits stF.activeEscrows +
       stF.settledEscrowTotal = st₀.escrowVaultBalance + lockedEscrowDeposits st₀.activeEscrows + st₀.settledEscrowTotal`. -/
theorem firmament_sel4_copy_before_verify_and_irreversible_outbox_safe
    {P : Protocol} {part : SeL4MicrokitPartition}
    {sent₀ sentF : Sent} {st₀ stF : OutboxState} {turns : List OutboxTurn}
    (hClean : st₀.dispatchedActuations = [])
    (hTrace : ValidOutboxTrace P part sent₀ st₀ turns sentF stF) :
    Sel4CapDlNonInterfering part ∧
    Reach P sentF ∧
    (stF.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    stF.escrowVaultBalance + lockedEscrowDeposits stF.activeEscrows + stF.settledEscrowTotal =
      st₀.escrowVaultBalance + lockedEscrowDeposits st₀.activeEscrows + st₀.settledEscrowTotal ∧
    (∀ a ∈ stF.dispatchedActuations,
      st₀.highWaterNullifier < a.nullifierId ∧
      Finalized P sentF a.view a.chain ∧
      a.chain.getLast? = some (.block a.view
        (effectCommitNat a.nullifierId .irreversibleActuation a.dispatchedPayload)) ∧
      (∃ t ∈ turns,
        t.req.effectClass = .irreversibleActuation ∧
        a.nullifierId = t.req.nullifierId ∧
        a.dispatchedPayload = t.req.spsc.sharedRingBeforeCopy) ∧
      (∀ (vCanon : Nat) (cCanon : Chain),
        Finalized P sentF vCanon cCanon → a.view ≤ vCanon → a.chain <+: cCanon)) ∧
    (∀ a₁ ∈ stF.dispatchedActuations, ∀ a₂ ∈ stF.dispatchedActuations,
      a₁.chain.height = a₂.chain.height → a₁.chain.blocks = a₂.chain.blocks) := by
  have hInitB : ∀ a ∈ st₀.dispatchedActuations,
      a.nullifierId ≤ st₀.highWaterNullifier ∧ Finalized P sent₀ a.view a.chain := by
    rw [hClean]; intro _ h; cases h
  have hInitNd : (st₀.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup := by
    rw [hClean]; exact List.Pairwise.nil
  obtain ⟨hReachF, _, hIso, _, hEscCons, hNodupF, hActsF⟩ :=
    validOutboxTrace_core turns hTrace hInitB hInitNd
  have hInvF : Inv P sentF := reach_inv hReachF
  refine ⟨checkMicrokitIsolation_implies_capDlNonInterfering part hIso,
          hReachF,
          hNodupF,
          hEscCons,
          ?_,
          ?_⟩
  · intro a ha
    obtain ⟨_, hFinA, hOrigin⟩ := hActsF a ha
    rcases hOrigin with haOld | ⟨hFreshA, _, hTipA, t, htMem, hClsT, hIdT, hPayT⟩
    · rw [hClean] at haOld; cases haOld
    · refine ⟨hFreshA, hFinA, hTipA, ⟨t, htMem, hClsT, hIdT, hPayT⟩, ?_⟩
      intro vCanon cCanon hFinCanon hViewLe
      have hLenCanon : cCanon.length = vCanon := finalized_length hInvF hFinCanon
      have hNotCanon : ChainNotarized P sentF cCanon := finalized_chainNotarized hInvF hFinCanon
      exact finalized_prefix_of_notarized hInvF hFinA hNotCanon (by omega)
  · intro a₁ ha₁ a₂ ha₂ hHeight
    exact fin_cert_unique_per_height hInvF (hActsF a₁ ha₁).2.1 (hActsF a₂ ha₂).2.1 hHeight

/-! ## 6. Non-Vacuity / Inhabitedness Witnesses -/

private def sampleOutboxPart : SeL4MicrokitPartition where
  watchdogPdId := 4
  domains :=
    [ { pdId := 1
      , name := "ariadne-nic-pd"
      , mappedMmio := [⟨10, 0x4000_0000, 0x1000, true, false⟩]
      , untypedCapChildren := [3, 4] }
    , { pdId := 3
      , name := "lean-executor-pd"
      , mappedMmio := [⟨11, 0x4001_0000, 0x1000, true, false⟩]
      , untypedCapChildren := [4] }
    , { pdId := 4
      , name := "simplex-watchdog-pd"
      , mappedMmio := [⟨12, 0x5000_0000, 0x1000, true, true⟩]
      , untypedCapChildren := [] } ]
  channels :=
    [ ⟨0, 1, 3, 2048⟩
    , ⟨1, 3, 4, 512⟩ ]

private def sampleOutboxInit : OutboxState where
  gatekeeperPd         := 3
  highWaterNullifier   := 0
  escrowVaultBalance   := 500
  readAuditCount       := 0
  activeEscrows        := []
  settledEscrowTotal   := 0
  dispatchedActuations := []

private def sampleReadReq : OutboxEffectReq where
  nullifierId   := 1
  effectClass   := .idempotentRead
  targetView    := 1
  proposedChain := []
  finCert?      := none
  escrowBond?   := none
  spsc          := ⟨0, bytesOfList [0xAA, 0xBB]⟩

private def sampleEscrowReq : OutboxEffectReq where
  nullifierId   := 2
  effectClass   := .compensatableEscrow
  targetView    := 1
  proposedChain := [.block 1 42]
  finCert?      := none
  escrowBond?   := some ⟨100, 25⟩
  spsc          := ⟨0, bytesOfList [0x10, 0x20]⟩

private def sampleOutboxProto : Protocol :=
  ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

example : (checkSpscChannelToGatekeeper sampleOutboxPart 3 0 2).isOk = true := by decide
example : checkChainTipCommit [.block 1 42] 1 42 = true := by decide
example :
    let pending : PendingOptimisticEscrow :=
      ⟨2, 1, [.block 1 99], bytesOfList [0x10], ⟨100, 25⟩⟩
    reconcileEscrowList 1 [.block 1 42] [pending] = ([], 75, 25) := by decide

example (hIso : checkMicrokitIsolation sampleOutboxPart = true) :
    (stepOutbox sampleOutboxProto sampleOutboxPart [] sampleOutboxInit sampleReadReq).isSome = true := by
  have hCh : checkSpscChannelToGatekeeper sampleOutboxPart sampleOutboxInit.gatekeeperPd
      sampleReadReq.spsc.channelId (copyRingToPrivateSlot sampleReadReq.spsc).data.toList.length = .ok () := by
    have hLen : (copyRingToPrivateSlot sampleReadReq.spsc).data.toList.length = 2 := by
      simp [copyRingToPrivateSlot, sampleReadReq, bytesOfList_toList]
    change checkSpscChannelToGatekeeper sampleOutboxPart 3 0
      (copyRingToPrivateSlot sampleReadReq.spsc).data.toList.length = .ok ()
    rw [hLen]; rfl
  have hW : sampleReadReq.nullifierId < OutboxBound64 := by
    change 1 < OutboxBound64; decide
  have hCls : sampleReadReq.effectClass = .idempotentRead := rfl
  unfold stepOutbox auditOutboxStep
  rw [hIso, Bool.not_true]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hCh]
  dsimp only
  rw [decide_eq_true hW, Bool.not_true]
  simp only [Bool.false_eq_true, ↓reduceIte, hCls]
  rfl

example (hIso : checkMicrokitIsolation sampleOutboxPart = true) :
    (stepOutbox sampleOutboxProto sampleOutboxPart [] sampleOutboxInit sampleEscrowReq).isSome = true := by
  have hCh : checkSpscChannelToGatekeeper sampleOutboxPart sampleOutboxInit.gatekeeperPd
      sampleEscrowReq.spsc.channelId (copyRingToPrivateSlot sampleEscrowReq.spsc).data.toList.length = .ok () := by
    have hLen : (copyRingToPrivateSlot sampleEscrowReq.spsc).data.toList.length = 2 := by
      simp [copyRingToPrivateSlot, sampleEscrowReq, bytesOfList_toList]
    change checkSpscChannelToGatekeeper sampleOutboxPart 3 0
      (copyRingToPrivateSlot sampleEscrowReq.spsc).data.toList.length = .ok ()
    rw [hLen]; rfl
  have hW : sampleEscrowReq.nullifierId < OutboxBound64 := by
    change 2 < OutboxBound64; decide
  have hMono : sampleOutboxInit.highWaterNullifier < sampleEscrowReq.nullifierId := by
    change 0 < 2; decide
  have hCls : sampleEscrowReq.effectClass = .compensatableEscrow := rfl
  have hBond : sampleEscrowReq.escrowBond? = some ⟨100, 25⟩ := rfl
  have hBondOk : 0 < 25 ∧ 25 ≤ 100 ∧ 100 ≤ sampleOutboxInit.escrowVaultBalance := by
    change 0 < 25 ∧ 25 ≤ 100 ∧ 100 ≤ 500; decide
  unfold stepOutbox auditOutboxStep
  rw [hIso, Bool.not_true]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hCh]
  dsimp only
  rw [decide_eq_true hW, Bool.not_true]
  simp only [Bool.false_eq_true, ↓reduceIte, hCls, decide_eq_true hMono, Bool.not_true, hBond]
  rw [decide_eq_true hBondOk]
  simp only [↓reduceIte]
  rfl

end Obend.Vault.IrreversibleOutbox
end
