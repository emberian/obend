module
public import Obend.Vault.SurviveFirePor
import all Obend.Vault.SurviveFirePor
public import Obend.Vault.Mandate
public import Obend.Vault.Escrow
public import Obend.Polis.CapTP
public import Obend.Codec.DetCbor

public section
/-!
Lossless migration of the complete world and serializable capability/escrow state.
Portable mandates interpret finite method allowlists as ordinary vault mandates. The member
tag is keyed cSHAKE authentication. One-shot authority depends on the shared linearized registry;
this module proves its state machine, not a distributed consensus implementation.
CBOR's finite length range is explicit in `HomeArchiveFits`. Accepted migration histories
preserve the source home, or identify an actual collision of its archive commitment.
-/
namespace Obend.Vault.PortableContinuation
set_option autoImplicit false
open SurviveFirePor ChunkedWorld Obend.Codec.DetCbor

/-- The portable fragment of a mandate: method filters are finite allowlists.
Its interpretation is an ordinary vault mandate, with the same allowance and authority. -/
structure PortableMandate where
  id : Nat
  grant : Mandate.Grant
  principal : Mandate.Principal
  target : String
  rights : List Mandate.Auth
  budget : Nat
  cells : List Nat
  expiresAt : Nat
  methods : List Nat
  deriving DecidableEq

def PortableMandate.toMandate (m : PortableMandate) : Mandate.Mandate :=
  ⟨m.id, m.grant, m.principal, m.target, m.rights, m.budget, m.cells, m.expiresAt,
    ⟨fun method => m.methods.contains method⟩⟩

structure SturdyMembraneEntry where
  swissNum : UInt64
  mandate : PortableMandate
  expectedNonce : UInt64
  expiresAt : Nat
  revoked : Bool
  deriving DecidableEq

def SturdyMembraneEntry.toSturdyEntry (e : SturdyMembraneEntry) : Obend.Polis.CapTP.SturdyEntry :=
  ⟨e.swissNum, e.mandate.toMandate, e.expectedNonce, e.expiresAt, e.revoked⟩

/-- Both escrow legs are serializable; natural-valued amounts cannot be negative. -/
structure EscrowSnapshot where
  statusA : Escrow.LegStatus
  statusB : Escrow.LegStatus
  amountA : Nat
  amountB : Nat
  recvA : Nat
  recvB : Nat
  paidA : Nat
  paidB : Nat
  deriving DecidableEq

def EscrowSnapshot.toEscrowState (e : EscrowSnapshot) : Escrow.EscrowState where
  status := fun s => match s with | .A => e.statusA | .B => e.statusB
  amount := fun s => match s with | .A => e.amountA | .B => e.amountB
  recv := fun s => match s with | .A => e.recvA | .B => e.recvB
  paid := fun s => match s with | .A => e.paidA | .B => e.paidB

structure ReceiptLink where
  previous : Digest256
  payload : List UInt8
  next : Digest256
  deriving DecidableEq

structure SovereignHome where
  world : World
  membranes : List SturdyMembraneEntry
  mandates : List PortableMandate
  escrows : List EscrowSnapshot
  receiptGenesis : Digest256
  receipts : List ReceiptLink
  receiptChainHead : Digest256
  deriving DecidableEq

structure HomeArchive where
  memberId : Nat
  sourceHostId : Nat
  targetHostId : Nat
  migrationEpoch : Nat
  transferNonce : Digest256
  home : SovereignHome
  deriving DecidableEq

def cU64 : FastCodec UInt64 :=
  cMap UInt64.toNat (fun n => some (UInt64.ofNat n)) (by intro n; simp) cNat

def cPrincipal : FastCodec Mandate.Principal :=
  cMap (fun p => (p.name, p.id)) (fun (n, i) => some ⟨n, i⟩)
    (by intro p; cases p; rfl) (cPair cString cNat)

def cGrant : FastCodec Mandate.Grant :=
  cMap (fun g => match g with | .root p t => Sum.inl (p, t) | .under n => Sum.inr n)
    (fun g => some (match g with | .inl (p, t) => .root p t | .inr n => .under n))
    (by intro g; cases g <;> rfl) (cSum (cPair cPrincipal cString) cNat)

def authCode : Mandate.Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

def decodeAuth : Nat → Option Mandate.Auth
  | 0 => some .read | 1 => some .write | 2 => some .grant | 3 => some .call
  | 4 => some .reply | 5 => some .reset | 6 => some .control | 7 => some .notify | _ => none

def cMandateAuth : FastCodec Mandate.Auth :=
  cMap authCode decodeAuth (by intro a; cases a <;> rfl) cNat

def cPortableMandate : FastCodec PortableMandate :=
  cMap (fun m => (m.id, m.grant, m.principal, m.target, m.rights, m.budget,
      m.cells, m.expiresAt, m.methods))
    (fun (i, g, p, t, r, b, c, e, m) => some ⟨i, g, p, t, r, b, c, e, m⟩)
    (by intro m; cases m; rfl)
    (cPair cNat (cPair cGrant (cPair cPrincipal (cPair cString (cPair (cList cMandateAuth)
      (cPair cNat (cPair (cList cNat) (cPair cNat (cList cNat)))))))))

def cSturdyMembraneEntry : FastCodec SturdyMembraneEntry :=
  cMap (fun e => (e.swissNum, e.mandate, e.expectedNonce, e.expiresAt, e.revoked))
    (fun (s, m, n, e, r) => some ⟨s, m, n, e, r⟩) (by intro e; cases e; rfl)
    (cPair cU64 (cPair cPortableMandate (cPair cU64 (cPair cNat cBool))))

def cLegStatus : FastCodec Escrow.LegStatus :=
  cMap (fun s => match s with | .empty => 0 | .deposited => 1 | .consumed => 2)
    (fun n => match n with | 0 => some .empty | 1 => some .deposited | 2 => some .consumed | _ => none)
    (by intro s; cases s <;> rfl) cNat

def cEscrowSnapshot : FastCodec EscrowSnapshot :=
  cMap (fun e => (e.statusA, e.statusB, e.amountA, e.amountB, e.recvA, e.recvB, e.paidA, e.paidB))
    (fun (a, b, c, d, e, f, g, h) => some ⟨a, b, c, d, e, f, g, h⟩)
    (by intro e; cases e; rfl)
    (cPair cLegStatus (cPair cLegStatus (cPair cNat (cPair cNat (cPair cNat
      (cPair cNat (cPair cNat cNat)))))))

def cReceiptLink : FastCodec ReceiptLink :=
  cMap (fun r => (r.previous, r.payload, r.next)) (fun (p, b, n) => some ⟨p, b, n⟩)
    (by intro r; cases r; rfl) (cPair cDigest256 (cPair cBytes cDigest256))

def cHome : FastCodec SovereignHome :=
  cMap (fun h => (h.world, h.membranes, h.mandates, h.escrows, h.receiptGenesis,
      h.receipts, h.receiptChainHead))
    (fun (w, m, a, e, g, r, h) => some ⟨w, m, a, e, g, r, h⟩)
    (by intro h; cases h; rfl)
    (cPair cWorld (cPair (cList cSturdyMembraneEntry) (cPair (cList cPortableMandate)
      (cPair (cList cEscrowSnapshot) (cPair cDigest256 (cPair (cList cReceiptLink) cDigest256))))))

def cArchive : FastCodec HomeArchive :=
  cMap (fun a => (a.memberId, a.sourceHostId, a.targetHostId, a.migrationEpoch, a.transferNonce, a.home))
    (fun (m, s, t, e, n, h) => some ⟨m, s, t, e, n, h⟩) (by intro a; cases a; rfl)
    (cPair cNat (cPair cNat (cPair cNat (cPair cNat (cPair cDigest256 cHome)))))

/-- Versioned deterministic CBOR framing around the prefix-free fast world/home codec. -/
def archiveCbor (a : HomeArchive) : CborVal :=
  .array [.uint 1, .bytes (cArchive.encodeArray a)]

def encodeHomeArchiveCbor (a : HomeArchive) : ByteArray := encodeDetCbor (archiveCbor a)

def decodeHomeArchiveCbor (bytes : ByteArray) : Option HomeArchive := do
  let .array [.uint 1, .bytes payload] ← decodeDetCbor bytes | none
  let a ← cArchive.decodeExactArray payload
  if encodeHomeArchiveCbor a = bytes then some a else none

/-- CBOR's 64-bit byte-string length limit is an explicit wire-format bound. -/
def HomeArchiveFits (a : HomeArchive) : Prop := CanonicalCbor (archiveCbor a) = true

instance (a : HomeArchive) : Decidable (HomeArchiveFits a) :=
  inferInstanceAs (Decidable (CanonicalCbor (archiveCbor a) = true))

theorem decodeHomeArchiveCbor_encode (a : HomeArchive) (h : HomeArchiveFits a) :
    decodeHomeArchiveCbor (encodeHomeArchiveCbor a) = some a := by
  have hc := decodeDetCbor_encodeDetCbor (archiveCbor a) h
  have hr : cArchive.decodeExactArray (cArchive.encodeArray a) = some a := by
    rw [FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc]
  unfold decodeHomeArchiveCbor
  change ((decodeDetCbor (encodeDetCbor (archiveCbor a))).bind _) = some a
  rw [hc]
  simp only [archiveCbor, hr, bind, Option.bind, ite_true]

theorem encodeHomeArchiveCbor_injective (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b)
    (he : encodeHomeArchiveCbor a = encodeHomeArchiveCbor b) : a = b := by
  have h := congrArg decodeHomeArchiveCbor he
  rw [decodeHomeArchiveCbor_encode a ha, decodeHomeArchiveCbor_encode b hb] at h
  exact Option.some.inj h

def archiveDigest (a : HomeArchive) : Digest256 :=
  hash256 "obend.home.archive.v1" (encodeHomeArchiveCbor a)

/-- A shared-secret member authentication tag, not a public-key signature. -/
def memberAuthenticationTag (key : Digest256) (a : HomeArchive) : Digest256 :=
  hash256 "obend.home.member.v1" ((cPair cDigest256 cBytes).encodeArray
    (key, (encodeHomeArchiveCbor a).data.toList))

structure SignedHomeArchive where
  archive : HomeArchive
  digest : Digest256
  memberTag : Digest256
  deriving DecidableEq

def signHomeArchive (key : Digest256) (a : HomeArchive) : SignedHomeArchive :=
  ⟨a, archiveDigest a, memberAuthenticationTag key a⟩

def receiptLinkDigest (r : ReceiptLink) : Digest256 :=
  hash256 "obend.home.receipt.v1" ((cPair cDigest256 cBytes).encodeArray (r.previous, r.payload))

def checkReceiptChain : Digest256 → List ReceiptLink → Digest256 → Bool
  | head, [], expected => decide (head = expected)
  | head, r :: rs, expected => decide (r.previous = head) &&
      decide (r.next = receiptLinkDigest r) && checkReceiptChain r.next rs expected

def checkHome (h : SovereignHome) : Bool :=
  checkReceiptChain h.receiptGenesis h.receipts h.receiptChainHead &&
    h.escrows.all (fun e => decide (Escrow.enteredTotal e.toEscrowState =
      Escrow.lockedTotal e.toEscrowState + Escrow.paidTotal e.toEscrowState))

structure LiveHome where
  hostId : Nat
  genesis : Digest256
  height : Nat
  home : SovereignHome
  deriving DecidableEq

structure TransferPermit where
  source : Nat
  target : Nat
  epoch : Nat
  nonce : Digest256
  digest : Digest256
  deriving DecidableEq

/-- One member's linearized authority registry. Hosts must consult this shared state
before admission; disconnected copies do not provide one-shot authority. -/
structure MigrationRegistry where
  memberId : Nat
  latestCommittedEpoch : Nat
  active : Option LiveHome
  pending : Option TransferPermit
  consumed : List Digest256
  tombstones : List (Nat × Nat)
  deriving DecidableEq

inductive MigrationRefusal where
  | noActiveSource | transferPending | staleEpoch | nonceConsumed | sameHost
  | noPermit | wrongContext | badAuthentication | malformedHome | tombstoned
  deriving DecidableEq, Repr

def exportHomeArchive (key : Digest256) (r : MigrationRegistry) (target epoch : Nat)
    (nonce : Digest256) : Except MigrationRefusal (SignedHomeArchive × MigrationRegistry) :=
  match r.active with
  | none => .error .noActiveSource
  | some live =>
    if r.pending.isSome then .error .transferPending
    else if epoch ≤ r.latestCommittedEpoch then .error .staleEpoch
    else if nonce ∈ r.consumed then .error .nonceConsumed
    else if target = live.hostId then .error .sameHost
    else
      let a : HomeArchive := ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩
      if !decide (HomeArchiveFits a) then .error .malformedHome
      else .ok (signHomeArchive key a, { r with
        active := none
        pending := some ⟨live.hostId, target, epoch, nonce, archiveDigest a⟩
        tombstones := (live.hostId, epoch) :: r.tombstones })

def importHomeArchive (key genesis : Digest256) (host : Nat) (r : MigrationRegistry)
    (s : SignedHomeArchive) : Except MigrationRefusal MigrationRegistry :=
  if s.archive.transferNonce ∈ r.consumed then .error .nonceConsumed
  else if s.archive.migrationEpoch ≤ r.latestCommittedEpoch then .error .staleEpoch
  else match r.pending with
  | none => .error .noPermit
  | some permit =>
    if r.active.isSome || s.archive.memberId != r.memberId || s.archive.targetHostId != host ||
        s.archive.sourceHostId != permit.source || s.archive.targetHostId != permit.target ||
        s.archive.migrationEpoch != permit.epoch || s.archive.transferNonce != permit.nonce
      then .error .wrongContext
    else if s.digest != permit.digest || s.digest != archiveDigest s.archive ||
        s.memberTag != memberAuthenticationTag key s.archive then .error .badAuthentication
    else if !decide (HomeArchiveFits s.archive) || !checkHome s.archive.home then .error .malformedHome
    else .ok { r with
      latestCommittedEpoch := s.archive.migrationEpoch
      active := some ⟨host, genesis, 0, s.archive.home⟩
      pending := none
      consumed := s.archive.transferNonce :: r.consumed }

/-- A write must hold the current registry slot. An export clears that slot atomically. -/
def admitHomeMutation (host expectedEpoch : Nat) (r : MigrationRegistry) (home : SovereignHome) :
    Except MigrationRefusal MigrationRegistry :=
  match r.active with
  | none => .error .tombstoned
  | some live => if live.hostId = host ∧ r.latestCommittedEpoch = expectedEpoch then
      .ok { r with active := some { live with home := home, height := live.height + 1 } }
    else .error .tombstoned

/-- The destination installs the full decoded payload, changing only host-local wrappers. -/
theorem importHomeArchive_effect (key genesis : Digest256) (host : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    out.active = some ⟨host, genesis, 0, s.archive.home⟩ ∧
    out.latestCommittedEpoch = s.archive.migrationEpoch ∧
    out.pending = none ∧ out.consumed = s.archive.transferNonce :: r.consumed := by
  simp only [importHomeArchive] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem double_import_or_stale_epoch_refused (key genesis : Digest256) (host : Nat)
    (r : MigrationRegistry) (s : SignedHomeArchive)
    (h : s.archive.transferNonce ∈ r.consumed ∨
      s.archive.migrationEpoch ≤ r.latestCommittedEpoch) :
    importHomeArchive key genesis host r s = .error .nonceConsumed ∨
    importHomeArchive key genesis host r s = .error .staleEpoch := by
  by_cases hn : s.archive.transferNonce ∈ r.consumed
  · left; simp [importHomeArchive, hn]
  · right
    have he := h.resolve_left hn
    simp [importHomeArchive, hn, he]

theorem import_replay_refused (key genesis : Digest256) (host otherHost : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    importHomeArchive key genesis otherHost out s = .error .nonceConsumed := by
  have hc := (importHomeArchive_effect key genesis host r out s h).2.2.2
  simp [importHomeArchive, hc]

theorem tombstoned_source_refused (host expectedEpoch : Nat) (r : MigrationRegistry) (home : SovereignHome)
    (h : r.active = none) : admitHomeMutation host expectedEpoch r home = .error .tombstoned := by
  simp only [admitHomeMutation, h]

/-- Digest binding returns the concrete cSHAKE preimages that collided. -/
def archiveCollision (a b : HomeArchive) (ha : HomeArchiveFits a) (hb : HomeArchiveFits b)
    (hne : a ≠ b) (he : archiveDigest a = archiveDigest b) : CshakeCollision :=
  ⟨"obend.home.archive.v1", ⟨encodeHomeArchiveCbor a, encodeHomeArchiveCbor b,
    fun h => hne (encodeHomeArchiveCbor_injective a b ha hb h), congrArg Subtype.val he⟩⟩

/-- All fields, including nonce, epoch, destination, allowances and balances, are bound. -/
def archiveDigest_binding (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b) (hne : a ≠ b) :
    PSum (archiveDigest a ≠ archiveDigest b) CshakeCollision :=
  if he : archiveDigest a = archiveDigest b then .inr (archiveCollision a b ha hb hne he)
  else .inl he

def totalBalance (h : SovereignHome) : Nat :=
  (h.escrows.map fun e => Escrow.lockedTotal e.toEscrowState + Escrow.paidTotal e.toEscrowState).sum

/-- Every archive component is preserved by destination installation, including the
interpreted capability and escrow states. -/
theorem migrateHome_preserves_pages_membranes_and_balances
    (key genesis : Digest256) (host : Nat) (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    ∃ live, out.active = some live ∧ live.home.world = s.archive.home.world ∧
      live.home.membranes.map SturdyMembraneEntry.toSturdyEntry =
        s.archive.home.membranes.map SturdyMembraneEntry.toSturdyEntry ∧
      live.home.mandates.map PortableMandate.toMandate =
        s.archive.home.mandates.map PortableMandate.toMandate ∧
      live.home.escrows.map EscrowSnapshot.toEscrowState =
        s.archive.home.escrows.map EscrowSnapshot.toEscrowState ∧
      totalBalance live.home = totalBalance s.archive.home := by
  refine ⟨⟨host, genesis, 0, s.archive.home⟩,
    (importHomeArchive_effect key genesis host r out s h).1, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The shared registry grants write authority to at most one host. -/
def HasAuthority (r : MigrationRegistry) (host : Nat) : Prop :=
  ∃ live, r.active = some live ∧ live.hostId = host

theorem authority_unique (r : MigrationRegistry) (a b : Nat)
    (ha : HasAuthority r a) (hb : HasAuthority r b) : a = b := by
  obtain ⟨la, hla, rfl⟩ := ha
  obtain ⟨lb, hlb, rfl⟩ := hb
  have he := Option.some.inj (hla.symm.trans hlb)
  exact congrArg LiveHome.hostId he

inductive MigrationEvent where
  | export (target epoch : Nat) (nonce : Digest256)
  | importArchive (host : Nat) (genesis : Digest256) (archive : SignedHomeArchive)

/-- Histories include hostile archives: a step exists exactly when the executable admits it. -/
inductive ValidMigrationHistory (key : Digest256) :
    MigrationRegistry → List MigrationEvent → MigrationRegistry → Prop where
  | nil (r) : ValidMigrationHistory key r [] r
  | exportStep {r mid out target epoch nonce signed events}
      (step : exportHomeArchive key r target epoch nonce = .ok (signed, mid))
      (tail : ValidMigrationHistory key mid events out) :
      ValidMigrationHistory key r (.export target epoch nonce :: events) out
  | importStep {r mid out host genesis archive events}
      (step : importHomeArchive key genesis host r archive = .ok mid)
      (tail : ValidMigrationHistory key mid events out) :
      ValidMigrationHistory key r (.importArchive host genesis archive :: events) out

/-- Consumption accumulates through arbitrary exports and imports; it is never reset by a hop. -/
theorem migrationHistory_consumed_monotone (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (h : ValidMigrationHistory key r events out) : ∀ nonce ∈ r.consumed, nonce ∈ out.consumed := by
  induction h with
  | nil => exact fun _ h => h
  | @exportStep r mid out target epoch nonce signed events step tail ih =>
    have hc : mid.consumed = r.consumed := by
      simp only [exportHomeArchive] at step
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      cases step
      rfl
    intro n hn
    exact ih n (hc.symm ▸ hn)
  | @importStep r mid out host genesis archive events step tail ih =>
    have hc := (importHomeArchive_effect key genesis host r mid archive step).2.2.2
    intro n hn
    apply ih
    rw [hc]
    exact List.mem_cons_of_mem _ hn

/-- An admitted archive must match the registry's authenticated export commitment. -/
theorem importHomeArchive_authentic (key genesis : Digest256) (host : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive) (permit : TransferPermit)
    (hp : r.pending = some permit) (h : importHomeArchive key genesis host r s = .ok out) :
    archiveDigest s.archive = permit.digest ∧ HomeArchiveFits s.archive := by
  simp only [importHomeArchive, hp] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hauth
  split at h <;> try contradiction
  rename_i hhome
  have he : s.digest = permit.digest ∧ s.digest = archiveDigest s.archive ∧
      s.memberTag = memberAuthenticationTag key s.archive := by
    simpa only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not, and_assoc] using hauth
  refine ⟨he.2.1.symm.trans he.1, ?_⟩
  by_cases hf : HomeArchiveFits s.archive
  · exact hf
  · simp only [hf, decide_false, Bool.not_false, Bool.true_or, not_true_eq_false] at hhome

/-- Mutating any archive field either prevents state admission or constructs a concrete
collision. The comparison is against the permit installed when the source was tombstoned. -/
def tampered_homeArchive_refused_or_collision (key genesis : Digest256) (host : Nat)
    (r : MigrationRegistry) (original : HomeArchive) (submitted : SignedHomeArchive)
    (permit : TransferPermit) (hp : r.pending = some permit)
    (hcommit : permit.digest = archiveDigest original) (hfit : HomeArchiveFits original)
    (hneq : submitted.archive ≠ original) :
    PSum (∃ reason, importHomeArchive key genesis host r submitted = .error reason) CshakeCollision :=
  match he : importHomeArchive key genesis host r submitted with
  | .error reason => .inl ⟨reason, rfl⟩
  | .ok out =>
    let facts := importHomeArchive_authentic key genesis host r out submitted permit hp he
    .inr (archiveCollision submitted.archive original facts.2 hfit hneq (facts.1.trans hcommit))

/-- Export both carries the complete source home and revokes its live slot in one transition. -/
theorem exportHomeArchive_effect (key : Digest256) (r frozen : MigrationRegistry)
    (target epoch : Nat) (nonce : Digest256) (signed : SignedHomeArchive)
    (h : exportHomeArchive key r target epoch nonce = .ok (signed, frozen)) :
    ∃ source, r.active = some source ∧ signed.archive.home = source.home ∧
      frozen.active = none ∧ frozen.consumed = r.consumed ∧
      frozen.tombstones = (source.hostId, epoch) :: r.tombstones := by
  simp only [exportHomeArchive] at h
  split at h <;> try contradiction
  rename_i live hlive
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨live, hlive, rfl, rfl, rfl, rfl⟩

/-- Complete source-to-destination preservation, including wrapper re-anchoring. -/
theorem export_import_preserves_home (key genesis : Digest256) (target epoch : Nat)
    (nonce : Digest256) (before frozen after : MigrationRegistry) (signed : SignedHomeArchive)
    (he : exportHomeArchive key before target epoch nonce = .ok (signed, frozen))
    (hi : importHomeArchive key genesis target frozen signed = .ok after) :
    ∃ source destination, before.active = some source ∧ after.active = some destination ∧
      source.home = destination.home ∧ totalBalance source.home = totalBalance destination.home := by
  obtain ⟨source, hs, hh, _, _, _⟩ := exportHomeArchive_effect key before frozen target epoch nonce signed he
  have hd := (importHomeArchive_effect key genesis target frozen after signed hi).1
  refine ⟨source, ⟨target, genesis, 0, signed.archive.home⟩, hs, hd, hh.symm, ?_⟩
  exact congrArg totalBalance hh.symm

/-- An old slot token stays stale even if a later migration returns to the same physical host. -/
theorem stale_source_slot_refused (host epoch : Nat) (r : MigrationRegistry) (home : SovereignHome)
    (he : r.latestCommittedEpoch ≠ epoch) :
    admitHomeMutation host epoch r home = .error .tombstoned := by
  unfold admitHomeMutation
  cases r.active <;> simp only [he, and_false, ite_false]

/-- While authority is in transit, the registry keeps the commitment of the same home.
The archive witness is logical provenance, not data copied into the runtime registry. -/
structure HomeOrigin (home : SovereignHome) (r : MigrationRegistry) : Prop where
  active : ∀ live, r.active = some live → live.home = home
  pending : ∀ permit, r.pending = some permit →
    ∃ archive, archive.home = home ∧ HomeArchiveFits archive ∧ archiveDigest archive = permit.digest

theorem export_preserves_origin (home : SovereignHome) (key : Digest256)
    (r frozen : MigrationRegistry) (target epoch : Nat) (nonce : Digest256) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r)
    (h : exportHomeArchive key r target epoch nonce = .ok (signed, frozen)) : HomeOrigin home frozen := by
  simp only [exportHomeArchive] at h
  split at h <;> try contradiction
  rename_i live hlive
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hfits
  have hf : HomeArchiveFits ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩ := by
    by_cases hf : HomeArchiveFits ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩
    · exact hf
    · simp only [hf, decide_false, Bool.not_false, not_true_eq_false] at hfits
  cases h
  constructor
  · intro other ho; cases ho
  · intro permit hp
    cases hp
    exact ⟨_, origin.active live hlive, hf, rfl⟩

theorem import_preserves_origin_or_collision (home : SovereignHome) (key genesis : Digest256)
    (host : Nat) (r out : MigrationRegistry) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r)
    (h : importHomeArchive key genesis host r signed = .ok out) :
    HomeOrigin home out ∨ Nonempty CshakeCollision := by
  cases hp : r.pending with
  | none =>
    simp only [importHomeArchive, hp] at h
    split at h <;> try contradiction
    split at h <;> contradiction
  | some permit =>
    obtain ⟨original, hhome, hfit, hcommit⟩ := origin.pending permit hp
    have facts := importHomeArchive_authentic key genesis host r out signed permit hp h
    by_cases he : signed.archive = original
    · left
      have effect := importHomeArchive_effect key genesis host r out signed h
      constructor
      · intro live hlive
        rw [effect.1] at hlive
        cases hlive
        exact he ▸ hhome
      · intro other ho
        rw [effect.2.2.1] at ho
        cases ho
    · right
      exact ⟨archiveCollision signed.archive original facts.2 hfit he (facts.1.trans hcommit.symm)⟩

/-- Arbitrary accepted migration traces preserve the complete source home, including its
escrow value and mandate allowances, unless they furnish a cSHAKE collision. -/
theorem migrationHistory_preserves_home_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r) :
    HomeOrigin home out ∨ Nonempty CshakeCollision := by
  induction history with
  | nil => exact Or.inl origin
  | @exportStep r mid out target epoch nonce signed events step tail ih =>
    exact ih (export_preserves_origin home key r mid target epoch nonce signed origin step)
  | @importStep r mid out host genesis archive events step tail ih =>
    rcases import_preserves_origin_or_collision home key genesis host r mid archive origin step with ho | hc
    · exact ih ho
    · exact Or.inr hc

theorem migrationHistory_balance_conserved_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (live : LiveHome) (hlive : out.active = some live) :
    totalBalance live.home = totalBalance home ∨ Nonempty CshakeCollision := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · exact Or.inl (congrArg totalBalance (ho.active live hlive))
  · exact Or.inr hc

end Obend.Vault.PortableContinuation
