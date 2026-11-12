module
public import Obend.Vault.SurviveFirePor
import all Obend.Vault.SurviveFirePor
public import Obend.Vault.VerkleSnapshotBridge
import all Obend.Vault.VerkleSnapshotBridge
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
Bearer secrets are 256 bits wide and `cU64` refuses every wire natural `≥ 2^64`.
The migrated world is the world `Vault.Replay` serves (`Replay.World` abbreviates
`ChunkedWorld.World`); the last section connects its three representations: the portable
archive, the sharded checkpoint, and the authenticated Verkle snapshot recovered from the WAL.
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

/-- A sturdy reference carried across hosts. `swissNum` is the full 256-bit bearer secret. -/
structure SturdyMembraneEntry where
  swissNum : Digest256
  mandate : PortableMandate
  expectedNonce : UInt64
  expiresAt : Nat
  revoked : Bool
  deriving DecidableEq

/-- The 64-bit key of CapTP's sorted swiss table: the leading eight bytes of the secret. It locates
an entry; it does not authenticate a bearer (`SovereignHome.lookupMembrane` compares all 32 bytes). -/
def swissLocator (d : Digest256) : UInt64 :=
  UInt64.ofNat (Obend.Digest.HashBytes.ofBE (d.val.data.toList.take 8))

def SturdyMembraneEntry.toSturdyEntry (e : SturdyMembraneEntry) : Obend.Polis.CapTP.SturdyEntry :=
  ⟨swissLocator e.swissNum, e.mandate.toMandate, e.expectedNonce, e.expiresAt, e.revoked⟩

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

/-- Canonical `UInt64` codec. Decoding refuses every natural `≥ 2^64`; it never reduces one
modulo `2^64`, so `n + 2^64` is not a second encoding of `n`. -/
def cU64 : FastCodec UInt64 :=
  cMap UInt64.toNat (fun n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none)
    (by intro n; simp [n.toNat_lt]) cNat

theorem cU64_dec_refuses_overflow (n : Nat) (h : 2 ^ 64 ≤ n) (rest : Log.Bytes) :
    cU64.dec (cNat.enc n ++ rest) = none := by
  have hr := cNat.roundtrip n rest
  have hn : ¬ n < 2 ^ 64 := by omega
  simp [cU64, cMap, rawMap, hr, hn]

/-- A decoded `UInt64` is exactly the natural on the wire. -/
theorem cU64_dec_exact {bs rest : Log.Bytes} {v : UInt64} (h : cU64.dec bs = some (v, rest)) :
    cNat.dec bs = some (v.toNat, rest) := by
  simp only [cU64, cMap, rawMap] at h
  cases hd : cNat.dec bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨n, r⟩ := p
    rw [hd] at h
    if hn : n < 2 ^ 64 then
      simp only [hn, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
    else
      simp [hn] at h

/-- Wire injectivity without aliasing: two encoded naturals that decode to one `UInt64` are equal. -/
theorem cU64_wire_injective {n m : Nat} {r₁ r₂ t₁ t₂ : Log.Bytes} {v : UInt64}
    (h₁ : cU64.dec (cNat.enc n ++ r₁) = some (v, t₁))
    (h₂ : cU64.dec (cNat.enc m ++ r₂) = some (v, t₂)) : n = m := by
  have e₁ := cU64_dec_exact h₁
  have e₂ := cU64_dec_exact h₂
  rw [cNat.roundtrip] at e₁ e₂
  have a₁ := (Prod.mk.inj (Option.some.inj e₁)).1
  have a₂ := (Prod.mk.inj (Option.some.inj e₂)).1
  omega

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
    (cPair cDigest256 (cPair cPortableMandate (cPair cU64 (cPair cNat cBool))))

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
def HomeArchiveFits (a : HomeArchive) : Prop := WithinWidth (archiveCbor a) = true

instance (a : HomeArchive) : Decidable (HomeArchiveFits a) :=
  inferInstanceAs (Decidable (WithinWidth (archiveCbor a) = true))

theorem archiveCbor_canonical_of_fits (a : HomeArchive) (h : HomeArchiveFits a) :
    CanonicalCbor (archiveCbor a) = true := by
  simpa [HomeArchiveFits, CanonicalCbor, WithinWidth, archiveCbor, wfVal, wfList] using h

theorem decodeHomeArchiveCbor_encode (a : HomeArchive) (h : HomeArchiveFits a) :
    decodeHomeArchiveCbor (encodeHomeArchiveCbor a) = some a := by
  have hc := decodeDetCbor_encodeDetCbor (archiveCbor a) (archiveCbor_canonical_of_fits a h)
  have hr : cArchive.decodeExactArray (cArchive.encodeArray a) = some a := by
    rw [FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc]
  unfold decodeHomeArchiveCbor
  change ((decodeDetCbor (encodeDetCbor (archiveCbor a))).bind _) = some a
  rw [hc]
  simp only [archiveCbor, hr, bind, Option.bind, ite_true]

theorem encodeHomeArchiveCbor_injective (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b)
    (he : encodeHomeArchiveCbor a = encodeHomeArchiveCbor b) : a = b := by
  have hc := encodeDetCbor_injective (archiveCbor a) (archiveCbor b) ha hb he
  simp only [archiveCbor, CborVal.array.injEq, List.cons.injEq, CborVal.bytes.injEq,
    true_and, and_true] at hc
  have hd := congrArg cArchive.decodeExactArray hc
  rw [FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc,
      FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc] at hd
  exact Option.some.inj hd

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

/-- Bearer lookup by the full 256-bit secret. -/
def SovereignHome.lookupMembrane (h : SovereignHome) (secret : Digest256) :
    Option SturdyMembraneEntry :=
  h.membranes.find? fun e => decide (e.swissNum = secret)

/-- A granted lookup names a membrane of the home whose whole secret was presented: sharing the
64-bit `swissLocator` with some entry grants nothing. -/
theorem lookupMembrane_sound {h : SovereignHome} {secret : Digest256} {e : SturdyMembraneEntry}
    (hf : h.lookupMembrane secret = some e) : e ∈ h.membranes ∧ e.swissNum = secret := by
  have hf' : h.membranes.find? (fun e => decide (e.swissNum = secret)) = some e := hf
  have hd : decide (e.swissNum = secret) = true :=
    List.find?_some (p := fun (x : SturdyMembraneEntry) => decide (x.swissNum = secret)) hf'
  exact ⟨List.mem_of_find?_eq_some hf', of_decide_eq_true hd⟩

theorem lookupMembrane_refuses_unknown_secret {h : SovereignHome} {secret : Digest256}
    (hno : ∀ e ∈ h.membranes, e.swissNum ≠ secret) : h.lookupMembrane secret = none := by
  cases hf : h.lookupMembrane secret with
  | none => rfl
  | some e => exact absurd (lookupMembrane_sound hf).2 (hno e (lookupMembrane_sound hf).1)

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
  if hn : s.archive.transferNonce ∈ r.consumed then
    left; simp [importHomeArchive, hn]
  else
    right
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
    (hne : a ≠ b) (he : archiveDigest a = archiveDigest b) :
    CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor a) (encodeHomeArchiveCbor b) :=
  ⟨fun h => hne (encodeHomeArchiveCbor_injective a b ha hb h), congrArg Subtype.val he⟩

/-- All fields, including nonce, epoch, destination, allowances and balances, are bound. -/
def archiveDigest_binding (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b) (hne : a ≠ b) :
    PSum (archiveDigest a ≠ archiveDigest b)
      (CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor a) (encodeHomeArchiveCbor b)) :=
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
  if hf : HomeArchiveFits s.archive then
    exact hf
  else
    simp only [hf, decide_false, Bool.not_false, Bool.true_or, not_true_eq_false] at hhome

/-- Mutating any archive field either prevents state admission or constructs a concrete
collision. The comparison is against the permit installed when the source was tombstoned. -/
def tampered_homeArchive_refused_or_collision (key genesis : Digest256) (host : Nat)
    (r : MigrationRegistry) (original : HomeArchive) (submitted : SignedHomeArchive)
    (permit : TransferPermit) (hp : r.pending = some permit)
    (hcommit : permit.digest = archiveDigest original) (hfit : HomeArchiveFits original)
    (hneq : submitted.archive ≠ original) :
    PSum (∃ reason, importHomeArchive key genesis host r submitted = .error reason)
      (CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor submitted.archive)
        (encodeHomeArchiveCbor original)) :=
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

/-- The archive installed by a permit; all metadata is determined by the registry and permit. -/
def originArchive (home : SovereignHome) (r : MigrationRegistry) (p : TransferPermit) : HomeArchive :=
  ⟨r.memberId, p.source, p.target, p.epoch, p.nonce, home⟩

def archivePreimage (a : HomeArchive) : List UInt8 := (encodeHomeArchiveCbor a).data.toList

def archiveHash := Obend.Digest.Cshake256.cshake256Bytes "obend.home.archive.v1".toUTF8.data.toList

/-- Exactly the submitted and provenance preimages compared at an import. -/
def importPreimages (home : SovereignHome) (r : MigrationRegistry) (s : SignedHomeArchive) :
    List (List UInt8) :=
  archivePreimage s.archive :: (r.pending.toList.map fun p => archivePreimage (originArchive home r p))

/-- Finite comparison transcript of the executable history, including hostile submissions. -/
def migrationPreimages (home : SovereignHome) (key : Digest256) :
    MigrationRegistry → List MigrationEvent → List (List UInt8)
  | _, [] => []
  | r, .export target epoch nonce :: es =>
    match exportHomeArchive key r target epoch nonce with
    | .ok (_, mid) => migrationPreimages home key mid es
    | .error _ => []
  | r, .importArchive host genesis s :: es =>
    importPreimages home r s ++ (match importHomeArchive key genesis host r s with
    | .ok mid => migrationPreimages home key mid es
    | .error _ => [])

/-- While authority is in transit, the registry keeps the commitment of the same home.
The archive witness is logical provenance, not data copied into the runtime registry. -/
structure HomeOrigin (home : SovereignHome) (r : MigrationRegistry) : Prop where
  active : ∀ live, r.active = some live → live.home = home
  pending : ∀ permit, r.pending = some permit →
    HomeArchiveFits (originArchive home r permit) ∧
      archiveDigest (originArchive home r permit) = permit.digest

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
    if hf : HomeArchiveFits ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩ then
      exact hf
    else
      simp only [hf, decide_false, Bool.not_false, not_true_eq_false] at hfits
  cases h
  constructor
  · intro other ho; cases ho
  · intro permit hp
    cases hp
    have he := origin.active live hlive
    constructor
    · simpa only [originArchive, ← he] using hf
    · simp only [originArchive, ← he]

/-- Executable collision pair, with membership in this import's finite comparison transcript. -/
structure ArchiveCollisionOn (inputs : List (List UInt8)) : Type where
  left : List UInt8
  right : List UInt8
  left_mem : left ∈ inputs
  right_mem : right ∈ inputs
  distinct : left ≠ right
  sameDigest : Obend.Digest.HashBytes.ofBE (archiveHash left) =
    Obend.Digest.HashBytes.ofBE (archiveHash right)
theorem ArchiveCollisionOn.toCollisionAmong {inputs : List (List UInt8)} (w : ArchiveCollisionOn inputs) :
    Obend.Digest.HashBytes.CollisionAmong archiveHash (fun x => x ∈ inputs) :=
  ⟨w.left, w.right, w.left_mem, w.right_mem, w.distinct, w.sameDigest⟩

def extractImportOriginBreak (home : SovereignHome) (key genesis : Digest256)
    (host : Nat) (r out : MigrationRegistry) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r)
    (h : importHomeArchive key genesis host r signed = .ok out) :
    PSum (HomeOrigin home out) (ArchiveCollisionOn (importPreimages home r signed)) := by
  cases hp : r.pending with
  | none =>
    simp only [importHomeArchive, hp] at h
    split at h <;> try contradiction
    split at h <;> contradiction
  | some permit =>
    let original := originArchive home r permit
    have hhome : original.home = home := rfl
    obtain ⟨hfit, hcommit⟩ := origin.pending permit hp
    have facts := importHomeArchive_authentic key genesis host r out signed permit hp h
    if he : signed.archive = original then
      apply PSum.inl
      have effect := importHomeArchive_effect key genesis host r out signed h
      constructor
      · intro live hlive
        rw [effect.1] at hlive
        cases hlive
        exact he ▸ hhome
      · intro other ho
        rw [effect.2.2.1] at ho
        cases ho
    else
      apply PSum.inr
      let pair := archiveCollision signed.archive original facts.2 hfit he
        (facts.1.trans hcommit.symm)
      refine ⟨archivePreimage signed.archive, archivePreimage original,
        by simp [importPreimages], by simp [importPreimages, hp, original], ?_, ?_⟩
      · intro hpre; apply pair.distinct
        exact byteArrayList_injective hpre
      · exact congrArg (fun x : ByteArray => Obend.Digest.HashBytes.ofBE x.data.toList) pair.sameDigest

theorem import_preserves_origin_or_collision (home : SovereignHome) (key genesis : Digest256)
    (host : Nat) (r out : MigrationRegistry) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r) (h : importHomeArchive key genesis host r signed = .ok out) :
    HomeOrigin home out ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ importPreimages home r signed) :=
  match extractImportOriginBreak home key genesis host r out signed origin h with
  | .inl ho => .inl ho
  | .inr w => .inr w.toCollisionAmong

/-- Arbitrary accepted migration traces preserve the complete source home, including its
escrow value and mandate allowances, unless they furnish a cSHAKE collision. -/
theorem migrationHistory_preserves_home_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r) :
    HomeOrigin home out ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  induction history with
  | nil => exact Or.inl origin
  | @exportStep r mid out target epoch nonce signed events step tail ih =>
    simpa only [migrationPreimages, step] using
      ih (export_preserves_origin home key r mid target epoch nonce signed origin step)
  | @importStep r mid out host genesis archive events step tail ih =>
    rcases import_preserves_origin_or_collision home key genesis host r mid archive origin step with ho | hc
    · rcases ih ho with ho' | hc
      · exact .inl ho'
      · exact .inr (hc.mono (by
          intro x hx
          simp only [migrationPreimages, step]
          exact List.mem_append_right _ hx))
    · exact .inr (hc.mono (by
        intro x hx
        simp only [migrationPreimages, step]
        exact List.mem_append_left _ hx))

theorem migrationHistory_balance_conserved_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (live : LiveHome) (hlive : out.active = some live) :
    totalBalance live.home = totalBalance home ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · exact Or.inl (congrArg totalBalance (ho.active live hlive))
  · exact Or.inr hc

/-! ## The replayed world, its portable archive, its sharded checkpoint and its snapshot

`Vault.Replay.World` is an abbreviation of `ChunkedWorld.World`: the world a home carries is
already the type the log replays, so there is no conversion between the two to prove. What a
migration has to connect is the world's representations and the session it continues. -/

open VerkleSnapshotBridge in
/-- Project a portable archive to the sharded checkpoint form `Replay.decodeCheckpointWorld` reads. -/
def archiveToSharded (bytes : ByteArray) : Option ShardedWorld :=
  (decodeHomeArchiveCbor bytes).map fun a => encodeShardedWorld a.home.world

/-- Rehydrate the replay world of a sharded checkpoint. -/
def rehydrateWorld (s : ShardedWorld) : Option Replay.World :=
  match decodeShardedWorld s with
  | .ok w => some w
  | .error _ => none

/-- Archive → sharded checkpoint → world is lossless on every archive that fits CBOR. -/
theorem archive_sharded_rehydrate (a : HomeArchive) (h : HomeArchiveFits a) :
    (archiveToSharded (encodeHomeArchiveCbor a)).bind rehydrateWorld = some a.home.world := by
  simp [archiveToSharded, rehydrateWorld, decodeHomeArchiveCbor_encode a h,
    decodeShardedWorld_encodeShardedWorld]

/-- The checkpoint decoder of the deployed replay machine reads the migrated world back from the
manifest it commits to, given a store holding the shards of the projected archive. -/
theorem archive_checkpoint_rehydrate (a : HomeArchive) (store : String → Option Log.Bytes)
    (hstore : ∀ k sb, (k, sb) ∈ (encodeShardedWorld a.home.world).shards → store k = some sb) :
    Replay.decodeCheckpointWorld store (Replay.deployed.encW a.home.world) = some a.home.world := by
  have hm := decodeManifestWith_manifestBytes a.home.world store hstore
  change Replay.decodeCheckpointWorld store (manifestBytes a.home.world) = _
  simp [Replay.decodeCheckpointWorld, hm]

/-- **Migration continues the replay session.** If the source home carried the world of a
reachable `Replay` session, then after any accepted migration history the live home's world is the
replay of that session's log, the session over the migrated world is reachable, and it admits
every next turn exactly as the source would have; or the history exhibits a cSHAKE collision. -/
theorem migrationHistory_continues_replay_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (S : Replay.Session) (hS : Replay.Reachable S) (hw : home.world = S.world)
    (live : LiveHome) (hlive : out.active = some live) :
    (live.home.world = Log.replay Replay.deployed Replay.genesis S.log ∧
      Replay.Reachable ⟨live.home.world, S.log⟩ ∧
      ∀ b : Log.Bytes, (⟨live.home.world, S.log⟩ : Replay.Session).admit Replay.logHash
          Replay.deployed b = S.admit Replay.logHash Replay.deployed b) ∨
    Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · left
    have hlw : live.home.world = S.world := (congrArg SovereignHome.world (ho.active live hlive)).trans hw
    have hSeq : (⟨live.home.world, S.log⟩ : Replay.Session) = S := by cases S; simp_all
    exact ⟨hlw.trans (Replay.state_eq_replay_log hS), hSeq ▸ hS, fun b => by rw [hSeq]⟩
  · exact Or.inr hc

open VerkleSnapshotBridge in
/-- Crash recovery from the session's WAL bytes (with any uncommitted tail) rebuilds exactly the
authenticated snapshot of a world equal to the one the session serves. -/
theorem walRecovery_snapshot_of_session (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (S : Replay.Session) (hS : Replay.Reachable S) (w : Replay.World) (hw : w = S.world)
    {tornTail : Log.Bytes} (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash Rehydration.genesisSentinel S.log) tornTail) :
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).snapshot =
        buildAuthenticatedSnapshot pp hCols w := by
  obtain ⟨hlinked, hwf⟩ := Log.log_sound hS
  have hparse := Log.parseFrom_encodeAll Replay.logHash S.log Rehydration.genesisSentinel
    hlinked hwf tornTail
  have htail := (parseFrom_uncommittedWalTail Replay.logHash _ htorn).1
  unfold recoverWalSnapshot; dsimp only
  rw [hparse, htail, List.append_nil, hw, Replay.state_eq_replay_log hS]

open VerkleSnapshotBridge in
/-- Destination-side check: the home's world has the snapshot root of the world the WAL replays to. -/
def checkHomeAgainstWal (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) : Bool :=
  decide ((buildAuthenticatedSnapshot pp hCols home.world).snapshotRoot =
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis wal).snapshot.snapshotRoot)

open VerkleSnapshotBridge in
/-- The snapshot WAL recovery builds is the snapshot of the replay of the parsed records. -/
theorem recoverWalSnapshot_snapshot (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (wal : Log.Bytes) :
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis wal).snapshot =
      buildAuthenticatedSnapshot pp hCols (Log.replay Replay.deployed Replay.genesis
        (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1) := by
  unfold recoverWalSnapshot; dsimp only

open VerkleSnapshotBridge in
theorem checkHomeAgainstWal_iff (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) :
    checkHomeAgainstWal pp hCols home wal = true ↔
      (buildAuthenticatedSnapshot pp hCols home.world).snapshotRoot =
        (buildAuthenticatedSnapshot pp hCols (Log.replay Replay.deployed Replay.genesis
          (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1)).snapshotRoot := by
  unfold checkHomeAgainstWal
  rw [recoverWalSnapshot_snapshot]
  exact decide_eq_true_iff

open VerkleSnapshotBridge in
/-- **Completeness across migration.** After any accepted migration history of a home that carried
a reachable session's world, the live home passes the WAL check against that session's log, torn
tail or not; or the history exhibits a cSHAKE collision. -/
theorem migratedHome_passes_wal_check_or_collision (pp : Obend.Crypto.AjtaiParams)
    (hCols : pp.cols = 64) (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (S : Replay.Session) (hS : Replay.Reachable S) (hw : home.world = S.world)
    (live : LiveHome) (hlive : out.active = some live)
    {tornTail : Log.Bytes} (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash Rehydration.genesisSentinel S.log) tornTail) :
    checkHomeAgainstWal pp hCols live.home
      (Log.encodeAll Replay.logHash S.log ++ tornTail) = true ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · left
    have hlw : live.home.world = S.world := (congrArg SovereignHome.world (ho.active live hlive)).trans hw
    unfold checkHomeAgainstWal
    rw [walRecovery_snapshot_of_session pp hCols S hS live.home.world hlw htorn]
    exact decide_eq_true rfl
  · exact Or.inr hc

open VerkleSnapshotBridge in
/-- Two well-formed snapshots with one snapshot root have one 256-bit `VerkleUmem` root, or their
two snapshot-root headers are a named `treeHash` collision. -/
def snapshotRoot_binds_verkleRoot {pp : Obend.Crypto.AjtaiParams} {hCols : pp.cols = 64}
    {s t : AuthenticatedWorldSnapshot} (hs : SnapshotWF pp hCols s) (ht : SnapshotWF pp hCols t)
    (h : s.snapshotRoot = t.snapshotRoot) :
    PSum (s.verkleRoot = t.verkleRoot)
      (Obend.Judge.Computational.HashCollisionWitness Obend.Polis.treeHash verkleMaxPreimageBytes) :=
  have hsz : ∀ {u : AuthenticatedWorldSnapshot}, SnapshotWF pp hCols u → u.verkleRoot.size = 32 :=
    fun hwf => by rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  match extractSnapshotRootBreak (by rw [hs.1]; decide) (by rw [ht.1]; decide) (hsz hs) (hsz ht) h with
  | .inl heq => .inl heq.2
  | .inr col => .inr col.val

open VerkleSnapshotBridge in
/-- **Soundness of the WAL check.** A home that passes has the 256-bit `VerkleUmem` root of the
world the WAL replays to, or the two snapshot-root headers are a named `treeHash` collision. -/
def checkHomeAgainstWal_sound (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) (h : checkHomeAgainstWal pp hCols home wal = true) :
    PSum (fullVerkleCommitWorld home.world = fullVerkleCommitWorld
        (Log.replay Replay.deployed Replay.genesis
          (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1))
      (Obend.Judge.Computational.HashCollisionWitness Obend.Polis.treeHash verkleMaxPreimageBytes) :=
  match snapshotRoot_binds_verkleRoot (buildAuthenticatedSnapshot_wf pp hCols home.world)
      (buildAuthenticatedSnapshot_wf pp hCols (Log.replay Replay.deployed Replay.genesis
        (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1))
      ((checkHomeAgainstWal_iff pp hCols home wal).1 h) with
  | .inl heq => .inl ((buildAuthenticatedSnapshot_verkleRoot pp hCols home.world).symm.trans
      (heq.trans (buildAuthenticatedSnapshot_verkleRoot pp hCols _)))
  | .inr col => .inr col

end Obend.Vault.PortableContinuation
