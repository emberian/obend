module
public import Obend.Polis.PrepaidLeaseAndFork
import all Obend.Polis.PrepaidLeaseAndFork

public section
namespace Obend.Polis.Custody
open Obend.Crypto
set_option autoImplicit false

structure SignedGrainPackage where
  publisher : ByteArray
  code : ByteArray
  signature : ByteArray
  deriving DecidableEq

def packageDigest (p : SignedGrainPackage) : ByteArray :=
  hash "OBEND.CUSTODY.PACKAGE/v1" [p.publisher.data.toList, p.code.data.toList]

structure VarEntry where
  pathBytes : List UInt8
  contents : ByteArray
  deriving DecidableEq

def contentHash256 (e : VarEntry) : ByteArray :=
  hash "OBEND.CUSTODY.CONTENT/v1" [e.contents.data.toList]

def canonicalVar (es : List VarEntry) : List VarEntry :=
  es.mergeSort (fun a b => compare a.pathBytes b.pathBytes != .gt)

def varFields (es : List VarEntry) : List (List UInt8) :=
  (canonicalVar es).map fun e => encodeFields [e.pathBytes, (contentHash256 e).data.toList]

def computeVarDataRoot (es : List VarEntry) : ByteArray := merkleRoot (varFields es)

/-- Array storage has the same canonical sorted Merkle commitment as the list specification. -/
def computeVarDataRootExec (es : Array VarEntry) : ByteArray :=
  merkleRoot ((es.toList.mergeSort (fun a b => compare a.pathBytes b.pathBytes != .gt)).toArray.map
    (fun e => encodeFields [e.pathBytes, (contentHash256 e).data.toList])).toList

theorem computeVarDataRoot_exec_eq (es : Array VarEntry) :
    computeVarDataRootExec es = computeVarDataRoot es.toList := by
  simp [computeVarDataRootExec, computeVarDataRoot, varFields, canonicalVar]

theorem contentHash256_binds (a b : VarEntry) (h : contentHash256 a = contentHash256 b) :
    a.contents = b.contents ∨ CshakeCollision := by
  rcases hash_binds "OBEND.CUSTODY.CONTENT/v1" h with he | hc
  · have hb : a.contents.data.toList = b.contents.data.toList := by simpa using he
    exact .inl (byteArray_eq_of_toList_eq hb)
  · exact .inr hc

def entryFields (e : VarEntry) : List UInt8 :=
  encodeFields [e.pathBytes, (contentHash256 e).data.toList]

theorem entryFields_binds (a b : VarEntry) (h : entryFields a = entryFields b) :
    a = b ∨ CshakeCollision := by
  have he := encodeFields_injective _ _ h
  have hh : a.pathBytes = b.pathBytes ∧
      (contentHash256 a).data.toList = (contentHash256 b).data.toList := by simpa using he
  rcases contentHash256_binds a b (byteArray_eq_of_toList_eq hh.2) with hc | collision
  · left; cases a; cases b; simp_all
  · exact .inr collision

theorem entryList_binds (as bs : List VarEntry) (h : as.map entryFields = bs.map entryFields) :
    as = bs ∨ CshakeCollision := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .inl rfl
    | cons b bs => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have he := List.cons.inj h
      rcases entryFields_binds a b he.1 with hab | hc
      · rcases ih bs he.2 with ht | hc
        · exact .inl (by rw [hab,ht])
        · exact .inr hc
      · exact .inr hc

theorem varDataRoot_binds (as bs : List VarEntry) (h : computeVarDataRoot as = computeVarDataRoot bs) :
    canonicalVar as = canonicalVar bs ∨ CshakeCollision := by
  rcases merkleRoot_binds h with he | hc
  · exact entryList_binds _ _ he
  · exact .inr hc

theorem packageDigest_binds (a b : SignedGrainPackage) (h : packageDigest a = packageDigest b) :
    (a.publisher = b.publisher ∧ a.code = b.code) ∨ CshakeCollision := by
  rcases hash_binds "OBEND.CUSTODY.PACKAGE/v1" h with he | hc
  · have hh : a.publisher.data.toList = b.publisher.data.toList ∧
        a.code.data.toList = b.code.data.toList := by simpa using he
    exact .inl ⟨byteArray_eq_of_toList_eq hh.1, byteArray_eq_of_toList_eq hh.2⟩
  · exact .inr hc

structure GrainCustodyAnchor where
  generation : Nat
  packageDigest : ByteArray
  varDataRoot : ByteArray
  receiptHead : ByteArray
  leaseRoot : ByteArray
  deriving DecidableEq

structure GrainArchive where
  package : SignedGrainPackage
  entries : List VarEntry
  anchor : GrainCustodyAnchor
  previousHead : ByteArray
  deriving DecidableEq

inductive CustodyPoisonReason where
  | package | varData | divergence | rollback | brokenReceipt | missingArchive
  deriving DecidableEq, Repr
inductive GrainCustodyStatus where
  | empty | ready | recoveryRequired | poisoned (reason : CustodyPoisonReason)
  deriving DecidableEq, Repr

def transitionHead (a : GrainArchive) : ByteArray :=
  hash "OBEND.CUSTODY.ARCHIVE/v1" [a.previousHead.data.toList, leb128 a.anchor.generation,
    a.anchor.packageDigest.data.toList, a.anchor.varDataRoot.data.toList, a.anchor.leaseRoot.data.toList]

/-- Signature verification is supplied by the authenticated package boundary, not a hash predicate. -/
@[expose] def reopenCustody (authenticate : SignedGrainPackage → Bool)
    (archive : Option GrainArchive) (anchor : Option GrainCustodyAnchor) : GrainCustodyStatus :=
  match archive, anchor with
  | none, none => .empty
  | none, some _ => .poisoned .missingArchive
  | some a, base =>
    if authenticate a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest then .poisoned .package
    else if computeVarDataRoot a.entries ≠ a.anchor.varDataRoot then .poisoned .varData
    else if transitionHead a ≠ a.anchor.receiptHead then .poisoned .brokenReceipt
    else match base with
      | none => if a.anchor.generation = 0 then .recoveryRequired else .poisoned .divergence
      | some b =>
        if a.anchor.packageDigest ≠ b.packageDigest then .poisoned .package
        else if a.anchor = b then .ready
        else if a.anchor.generation < b.generation then .poisoned .rollback
        else if a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead then .recoveryRequired
        else .poisoned .divergence

theorem var_mismatch_poisoned (auth : SignedGrainPackage → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) (h : computeVarDataRoot a.entries ≠ a.anchor.varDataRoot) :
    ∃ reason, reopenCustody auth (some a) b = .poisoned reason := by
  by_cases hp : auth a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest
  · exact ⟨.package, by simp [reopenCustody, hp]⟩
  · exact ⟨.varData, by simp [reopenCustody, hp, h]⟩

theorem package_mismatch_poisoned (auth : SignedGrainPackage → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) (h : packageDigest a.package ≠ a.anchor.packageDigest) :
    reopenCustody auth (some a) b = .poisoned .package := by
  simp [reopenCustody, h]

/-- Reopening a changed canonical image either refuses it or exhibits a concrete collision.
Package substitution is checked against the immutable digest in the same archived anchor. -/
theorem tampered_var_or_package_poisoned_or_collision
    (auth : SignedGrainPackage → Bool) (a : GrainArchive) (b : Option GrainCustodyAnchor)
    (original : List VarEntry) (hroot : a.anchor.varDataRoot = computeVarDataRoot original)
    (ht : canonicalVar a.entries ≠ canonicalVar original ∨ packageDigest a.package ≠ a.anchor.packageDigest) :
    (∃ reason, reopenCustody auth (some a) b = .poisoned reason) ∨ CshakeCollision := by
  rcases ht with hv | hp
  · by_cases he : computeVarDataRoot a.entries = a.anchor.varDataRoot
    · rcases varDataRoot_binds a.entries original (he.trans hroot) with hf | hc
      · exact False.elim (hv hf)
      · exact .inr hc
    · exact .inl (var_mismatch_poisoned auth a b he)
  · exact .inl ⟨.package, package_mismatch_poisoned auth a b hp⟩

def recoverOneAhead (auth : SignedGrainPackage → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) : Option GrainCustodyAnchor :=
  if reopenCustody auth (some a) b = .recoveryRequired then some a.anchor else none

attribute [local irreducible] hash merkleRoot leaseStateRoot

theorem recovery_facts (auth : SignedGrainPackage → Bool) (a : GrainArchive) (b : GrainCustodyAnchor)
    (h : reopenCustody auth (some a) (some b) = .recoveryRequired) :
    auth a.package = true ∧ packageDigest a.package = a.anchor.packageDigest ∧
    computeVarDataRoot a.entries = a.anchor.varDataRoot ∧ transitionHead a = a.anchor.receiptHead ∧
    a.anchor.packageDigest = b.packageDigest ∧ a.anchor.generation = b.generation + 1 ∧
    a.previousHead = b.receiptHead := by
  simp only [reopenCustody] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all

theorem one_ahead_crash_recovery_exact (auth : SignedGrainPackage → Bool)
    (a : GrainArchive) (b : GrainCustodyAnchor)
    (h : reopenCustody auth (some a) (some b) = .recoveryRequired) :
    recoverOneAhead auth a (some b) = some a.anchor ∧
    reopenCustody auth (some a) (some a.anchor) = .ready ∧
    a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead := by
  obtain ⟨ha, hp, hv, ht, _, hg, hh⟩ := recovery_facts auth a b h
  refine ⟨by simp [recoverOneAhead, h], ?_, hg, hh⟩
  simp [reopenCustody, ha, hp, hv, ht]

theorem two_ahead_poisoned (auth : SignedGrainPackage → Bool) (a : GrainArchive)
    (b : GrainCustodyAnchor) (h : b.generation + 2 ≤ a.anchor.generation) :
    ∃ reason, reopenCustody auth (some a) (some b) = .poisoned reason := by
  have hn : a.anchor ≠ b := by intro he; have := congrArg GrainCustodyAnchor.generation he; omega
  have hg : a.anchor.generation ≠ b.generation + 1 := by omega
  have hl : ¬ a.anchor.generation < b.generation := by omega
  simp only [reopenCustody]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [hg, false_and, ite_false]; exact ⟨_, rfl⟩

abbrev SettlementKey := UInt64 × Nat
structure SettlementLedger where
  lease : PrepaidLease
  records : List (SettlementKey × ByteArray)
  deriving DecidableEq

def settledKeys (s : SettlementLedger) : List SettlementKey := s.records.map Prod.fst

def settlementReceipt (s : SettlementLedger) (key : SettlementKey) : Option ByteArray :=
  (s.records.find? (fun r => decide (r.1 = key))).map Prod.snd

@[expose] def settleOrReplay (s : SettlementLedger) (period : Nat) : SettlementLedger :=
  let key := (s.lease.leaseId, period)
  if key ∈ settledKeys s then s
  else match dischargePeriod s.lease period s.lease.rent with
  | .error _ => s
  | .ok l =>
    let receipt := hash "OBEND.CUSTODY.SETTLE/v1"
      [leb128 s.lease.leaseId.toNat, leb128 period,
       (leaseStateRoot s.lease).data.toList, (leaseStateRoot l).data.toList]
    ⟨l, (key, receipt) :: s.records⟩

/-- Records and the debit are the durable after image. Restart discards only the volatile
acknowledgement, so the same key returns the same stored receipt. -/
theorem settle_replay_unchanged (s : SettlementLedger) (p : Nat)
    (h : (s.lease.leaseId, p) ∈ settledKeys s) : settleOrReplay s p = s := by
  simp [settleOrReplay, h]

theorem settle_replay_same_receipt (s : SettlementLedger) (p : Nat)
    (h : (s.lease.leaseId, p) ∈ settledKeys s) :
    settlementReceipt (settleOrReplay s p) (s.lease.leaseId, p) =
      settlementReceipt s (s.lease.leaseId, p) := by rw [settle_replay_unchanged s p h]

inductive CustodyHostEvent where
  | settle (period : Nat)
  | crash
  | restart
  deriving DecidableEq, Repr

def custodyEvent (s : SettlementLedger) : CustodyHostEvent → SettlementLedger
  | .settle p => settleOrReplay s p
  | .crash => s
  | .restart => s

def runCustodyEvents (s : SettlementLedger) (events : List CustodyHostEvent) : SettlementLedger :=
  events.foldl custodyEvent s

def LedgerInvariant (id : UInt64) (start rent budget : Nat) (s : SettlementLedger) : Prop :=
  (settledKeys s).Nodup ∧ ReachableLease id start rent budget s.records.length s.lease

theorem settle_preserves_invariant {id : UInt64} {start rent budget : Nat}
    {s : SettlementLedger} (p : Nat) (h : LedgerInvariant id start rent budget s) :
    LedgerInvariant id start rent budget (settleOrReplay s p) := by
  simp only [settleOrReplay]
  split
  · exact h
  next hn =>
    split
    · exact h
    next l hd =>
      refine ⟨?_, ?_⟩
      · change ((s.lease.leaseId, p) :: settledKeys s).Nodup
        exact List.nodup_cons.mpr ⟨hn, h.1⟩
      · exact ReachableLease.step h.2 hd

theorem events_preserve_invariant {id : UInt64} {start rent budget : Nat}
    (es : List CustodyHostEvent) (s : SettlementLedger)
    (h : LedgerInvariant id start rent budget s) :
    LedgerInvariant id start rent budget (runCustodyEvents s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih =>
    apply ih
    cases e with
    | settle p => exact settle_preserves_invariant p h
    | crash => exact h
    | restart => exact h

/-- Any number of retries and crashes produces one record per key. The exact total debit
is the cardinality of that duplicate-free key list times rent, not the number of attempts. -/
theorem double_charge_impossible_across_crash (id : UInt64) (start rent budget : Nat)
    (events : List CustodyHostEvent) :
    let s := runCustodyEvents ⟨openLease id start rent budget, []⟩ events
    (settledKeys s).Nodup ∧ s.lease.drawn = (settledKeys s).length * rent ∧
    s.lease.remaining = budget - (settledKeys s).length * rent := by
  have hi : LedgerInvariant id start rent budget ⟨openLease id start rent budget, []⟩ :=
    ⟨List.nodup_nil, ReachableLease.initial⟩
  have he := events_preserve_invariant events _ hi
  refine ⟨he.1, ?_, ?_⟩
  · simpa [settledKeys] using drawnAfter_eq he.2
  · simpa [settledKeys] using remainingAfter_eq he.2

/-- The WAL persists a complete after image before installing it. A retry may encounter
that image before or after installation; replay is assignment, never a second subtraction. -/
structure SettlementWal where
  durable : SettlementLedger
  pending : Option SettlementLedger
  deriving DecidableEq

def SettlementWal.recover (w : SettlementWal) : SettlementWal :=
  ⟨w.pending.getD w.durable, none⟩

def SettlementWal.prepare (w : SettlementWal) (period : Nat) : SettlementWal :=
  match w.pending with
  | some _ => w
  | none => ⟨w.durable, some (settleOrReplay w.durable period)⟩

inductive WalEvent where
  | request (period : Nat)
  | install
  | crashRestart
  deriving DecidableEq, Repr

def walEvent (w : SettlementWal) : WalEvent → SettlementWal
  | .request p => w.prepare p
  | .install => w.recover
  | .crashRestart => w.recover

def WalInvariant (id : UInt64) (start rent budget : Nat) (w : SettlementWal) : Prop :=
  LedgerInvariant id start rent budget w.durable ∧
    ∀ s, w.pending = some s → LedgerInvariant id start rent budget s

theorem wal_recovery_idempotent (w : SettlementWal) : w.recover.recover = w.recover := by
  simp [SettlementWal.recover]

theorem wal_event_preserves {id : UInt64} {start rent budget : Nat} (w : SettlementWal)
    (e : WalEvent) (h : WalInvariant id start rent budget w) :
    WalInvariant id start rent budget (walEvent w e) := by
  cases e with
  | request p =>
    cases hp : w.pending with
    | none =>
      refine ⟨by simpa [walEvent, SettlementWal.prepare, hp] using h.1, ?_⟩
      intro s hs
      have he : settleOrReplay w.durable p = s := by
        simpa [walEvent, SettlementWal.prepare, hp] using hs
      rw [← he]
      exact settle_preserves_invariant p h.1
    | some s => simpa [walEvent, SettlementWal.prepare, hp] using h
  | install | crashRestart =>
    refine ⟨?_, ?_⟩
    · cases hp : w.pending with
      | none => simpa [walEvent, SettlementWal.recover, hp] using h.1
      | some s => simpa [walEvent, SettlementWal.recover, hp] using h.2 s hp
    · intro s hs; simp [walEvent, SettlementWal.recover] at hs

theorem wal_events_preserve {id : UInt64} {start rent budget : Nat}
    (es : List WalEvent) (w : SettlementWal) (h : WalInvariant id start rent budget w) :
    WalInvariant id start rent budget (es.foldl walEvent w) := by
  induction es generalizing w with
  | nil => exact h
  | cons e es ih => exact ih (walEvent w e) (wal_event_preserves w e h)

/-- This includes crashes between writing the redo record and installing its after image,
not just crashes between completed settlement calls. -/
theorem double_charge_impossible_during_wal_recovery (id : UInt64) (start rent budget : Nat)
    (events : List WalEvent) :
    let w := events.foldl walEvent ⟨⟨openLease id start rent budget, []⟩, none⟩
    let s := w.recover.durable
    (settledKeys s).Nodup ∧ s.lease.drawn = (settledKeys s).length * rent ∧
      s.lease.remaining = budget - (settledKeys s).length * rent := by
  have hi : WalInvariant id start rent budget ⟨⟨openLease id start rent budget, []⟩, none⟩ :=
    ⟨⟨List.nodup_nil, ReachableLease.initial⟩, fun _ h => by cases h⟩
  have he := wal_events_preserve events _ hi
  have hr := (wal_event_preserves _ .crashRestart he).1
  refine ⟨hr.1, ?_, ?_⟩
  · simpa [settledKeys, walEvent] using drawnAfter_eq hr.2
  · simpa [settledKeys, walEvent] using remainingAfter_eq hr.2

/-- A mountain carries every signed request opening, with sequence numbers in its leaves. -/
inductive IngressMountain where
  | leaf (seqNo : Nat) (reqDigest : ByteArray)
  | node (left right : IngressMountain)
  deriving DecidableEq

def IngressMountain.height : IngressMountain → Nat
  | .leaf _ _ => 0
  | .node a b => max a.height b.height + 1

def IngressMountain.root : IngressMountain → ByteArray
  | .leaf n r => hash "OBEND.CUSTODY.MOUNTAIN/v1" [[0], leb128 n, r.data.toList]
  | .node a b => hash "OBEND.CUSTODY.MOUNTAIN/v1" [[1], a.root.data.toList, b.root.data.toList]

def IngressMountain.openings : IngressMountain → List (Nat × ByteArray)
  | .leaf n r => [(n,r)]
  | .node a b => a.openings ++ b.openings

theorem IngressMountain.root_binds (a b : IngressMountain) (h : a.root = b.root) :
    a = b ∨ CshakeCollision := by
  induction a generalizing b with
  | leaf n r =>
    cases b with
    | leaf m s =>
      rcases hash_binds "OBEND.CUSTODY.MOUNTAIN/v1" h with hp | hc
      · have he : leb128 n = leb128 m ∧ r.data.toList = s.data.toList := by simpa using hp
        exact .inl (by rw [natBytes_inj he.1, byteArray_eq_of_toList_eq he.2])
      · exact .inr hc
    | node x y =>
      rcases hash_binds "OBEND.CUSTODY.MOUNTAIN/v1" h with hp | hc
      · simp at hp
      · exact .inr hc
  | node x y ihx ihy =>
    cases b with
    | leaf n r =>
      rcases hash_binds "OBEND.CUSTODY.MOUNTAIN/v1" h with hp | hc
      · simp at hp
      · exact .inr hc
    | node u v =>
      rcases hash_binds "OBEND.CUSTODY.MOUNTAIN/v1" h with hp | hc
      · have he : x.root.data.toList = u.root.data.toList ∧ y.root.data.toList = v.root.data.toList := by simpa using hp
        rcases ihx u (byteArray_eq_of_toList_eq he.1) with hx | hc
        · rcases ihy v (byteArray_eq_of_toList_eq he.2) with hy | hc
          · exact .inl (by rw [hx,hy])
          · exact .inr hc
        · exact .inr hc
      · exact .inr hc

/-- Peaks are stored smallest first; equal heights carry into a binary parent. -/
def appendMountain (m : IngressMountain) : List IngressMountain → List IngressMountain
  | [] => [m]
  | p :: ps => if p.height = m.height then appendMountain (.node p m) ps else m :: p :: ps

theorem appendMountain_openings (m : IngressMountain) (ps : List IngressMountain) :
    ((appendMountain m ps).reverse.flatMap IngressMountain.openings) =
      ps.reverse.flatMap IngressMountain.openings ++ m.openings := by
  induction ps generalizing m with
  | nil => simp [appendMountain]
  | cons p ps ih =>
    simp only [appendMountain]
    split
    · rw [ih]; simp [IngressMountain.openings, List.append_assoc]
    · simp [List.append_assoc]

structure IngressMmr where
  count : Nat
  peaks : List IngressMountain
  deriving DecidableEq

def IngressMmr.empty : IngressMmr := ⟨0, []⟩
def IngressMmr.openings (s : IngressMmr) : List (Nat × ByteArray) :=
  s.peaks.reverse.flatMap IngressMountain.openings

def IngressMmr.root (s : IngressMmr) : ByteArray :=
  hash "OBEND.CUSTODY.MMR.ROOT/v1"
    [leb128 s.count, encodeFields (s.peaks.map fun p => p.root.data.toList)]

def IngressMmr.append (s : IngressMmr) (req : ByteArray) : IngressMmr :=
  ⟨s.count + 1, appendMountain (.leaf s.count req) s.peaks⟩

theorem IngressMmr.append_openings (s : IngressMmr) (req : ByteArray) :
    (s.append req).openings = s.openings ++ [(s.count, req)] :=
  appendMountain_openings _ _

theorem peaks_bind : ∀ (a b : List IngressMountain),
    (a.map fun p => p.root.data.toList) = (b.map fun p => p.root.data.toList) →
    a = b ∨ CshakeCollision
  | [], [], _ => .inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    have he := List.cons.inj h
    rcases x.root_binds y (byteArray_eq_of_toList_eq he.1) with hx | hc
    · rcases peaks_bind xs ys he.2 with ht | hc
      · exact .inl (by rw [hx,ht])
      · exact .inr hc
    · exact .inr hc

theorem IngressMmr.root_binds (a b : IngressMmr) (h : a.root = b.root) :
    a = b ∨ CshakeCollision := by
  rcases hash_binds "OBEND.CUSTODY.MMR.ROOT/v1" h with hp | hc
  · have he : leb128 a.count = leb128 b.count ∧
        encodeFields (a.peaks.map fun p => p.root.data.toList) =
          encodeFields (b.peaks.map fun p => p.root.data.toList) := by simpa using hp
    have hn := natBytes_inj he.1
    rcases peaks_bind a.peaks b.peaks (encodeFields_injective _ _ he.2) with hs | hc
    · left; cases a; cases b; simp_all
    · exact .inr hc
  · exact .inr hc

structure AriadneTicket where
  seqNo : Nat
  reqDigest : ByteArray
  mmrRoot : ByteArray
  signature : ByteArray
  deriving DecidableEq

def ticketMessage (t : AriadneTicket) : ByteArray :=
  hash "OBEND.CUSTODY.TICKET/v1" [leb128 t.seqNo, t.reqDigest.data.toList, t.mmrRoot.data.toList]

def ariadneCommitTurn (sign : ByteArray → ByteArray) (s : IngressMmr) (req : ByteArray) :
    IngressMmr × AriadneTicket :=
  let next := s.append req
  let t : AriadneTicket := ⟨s.count, req, next.root, ByteArray.empty⟩
  (next, { t with signature := sign (ticketMessage t) })

/-- A ticket is checked against a public signature verifier and an opening of its exact prior. -/
@[expose] def ValidTicket (verifySignature : ByteArray → ByteArray → Bool) (t : AriadneTicket)
    (prior : IngressMmr) : Prop :=
  verifySignature (ticketMessage t) t.signature = true ∧ prior.root = t.mmrRoot ∧
  prior.openings[t.seqNo]? = some (t.seqNo, t.reqDigest)

inductive ReachableIngress : IngressMmr → Prop
  | empty : ReachableIngress IngressMmr.empty
  | append {s} (req : ByteArray) : ReachableIngress s → ReachableIngress (s.append req)

theorem reachableIngress_length {s : IngressMmr} (h : ReachableIngress s) : s.openings.length = s.count := by
  induction h with
  | empty => rfl
  | @append s req _ ih => rw [IngressMmr.append_openings]; simpa [IngressMmr.append] using ih

theorem ariadneCommitTurn_complete (sign : ByteArray → ByteArray)
    (verify : ByteArray → ByteArray → Bool) (law : ∀ msg, verify msg (sign msg) = true)
    (s : IngressMmr) (req : ByteArray) (hs : ReachableIngress s) :
    ValidTicket verify (ariadneCommitTurn sign s req).2 (ariadneCommitTurn sign s req).1 := by
  refine ⟨?_, rfl, ?_⟩
  · exact law _
  · change (s.append req).openings[s.count]? = some (s.count, req)
    rw [IngressMmr.append_openings, ← reachableIngress_length hs]
    simp

/-- Full audit: the ticket's prior and the sequential turns are opened independently.
The host must supply an extension of that prior, and every turn must match its leaf. -/
def verifyNonOmission (t : AriadneTicket) (prior later : IngressMmr)
    (turns : List (Nat × ByteArray)) : Bool :=
  decide (prior.root = t.mmrRoot ∧ prior.openings.IsPrefix later.openings ∧
    later.openings = turns ∧ t.seqNo < turns.length)

/-- An accepted later turns cannot delete or substitute a committed sequential opening.
A different opening of the ticket's MMR root constructs an actual cSHAKE collision. -/
theorem host_cannot_omit_committed_turn_or_collision
    (verifySignature : ByteArray → ByteArray → Bool) (t : AriadneTicket)
    (original prior later : IngressMmr) (turns : List (Nat × ByteArray))
    (ht : ValidTicket verifySignature t original)
    (bad : turns[t.seqNo]? ≠ some (t.seqNo, t.reqDigest)) :
    verifyNonOmission t prior later turns = false ∨ CshakeCollision := by
  by_cases hv : verifyNonOmission t prior later turns = true
  · have he : prior.root = t.mmrRoot ∧ prior.openings.IsPrefix later.openings ∧
        later.openings = turns ∧ t.seqNo < turns.length := of_decide_eq_true hv
    rcases original.root_binds prior (ht.2.1.trans he.1.symm) with hp | hc
    · subst prior
      obtain ⟨suffix, hs⟩ := he.2.1
      have hlen : t.seqNo < original.openings.length := List.getElem?_eq_some_iff.1 ht.2.2 |>.1
      have hh : turns[t.seqNo]? = original.openings[t.seqNo]? := by
        rw [← he.2.2.1, ← hs]
        exact List.getElem?_append_left hlen
      exact False.elim (bad (hh.trans ht.2.2))
    · exact .inr hc
  · exact .inl (Bool.eq_false_iff.mpr hv)

end Obend.Polis.Custody
