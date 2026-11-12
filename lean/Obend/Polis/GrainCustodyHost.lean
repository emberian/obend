module
public import Obend.Polis.PrepaidLeaseAndFork
public import Obend.Polis.GrainPowerbox
import all Obend.Polis.PrepaidLeaseAndFork

public section
namespace Obend.Polis.Custody
open Obend.Crypto
set_option autoImplicit false

structure SignedGrainPackage where
  publisher : ByteArray
  code : ByteArray
  signature : ByteArray
  programDigest : ByteArray
  deriving DecidableEq

def packageDigest (p : SignedGrainPackage) : ByteArray :=
  hash "OBEND.CUSTODY.PACKAGE/v1" [p.publisher.data.toList, p.code.data.toList, p.programDigest.data.toList]

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

def contentHash256Call (e : VarEntry) : CshakeCall :=
  ("OBEND.CUSTODY.CONTENT/v1", [e.contents.data.toList])

def contentHash256Extract (a b : VarEntry) (h : contentHash256 a = contentHash256 b) :
    PSum (PLift (a.contents = b.contents)) (CshakeCallCollision [contentHash256Call a, contentHash256Call b]) :=
  match hashExtract "OBEND.CUSTODY.CONTENT/v1" [a.contents.data.toList] [b.contents.data.toList] h with
  | .inl he =>
    have hb : a.contents.data.toList = b.contents.data.toList := by simpa using he.down
    .inl ⟨byteArray_eq_of_toList_eq hb⟩
  | .inr hc => .inr hc

theorem contentHash256_binds (a b : VarEntry) (h : contentHash256 a = contentHash256 b) :
    a.contents = b.contents ∨ CshakeCollisionAmong [contentHash256Call a, contentHash256Call b] := by
  cases contentHash256Extract a b h with
  | inl hb => exact .inl hb.down
  | inr hc => exact .inr ⟨hc⟩

def entryFields (e : VarEntry) : List UInt8 :=
  encodeFields [e.pathBytes, (contentHash256 e).data.toList]

def entryFieldsExtract (a b : VarEntry) (h : entryFields a = entryFields b) :
    PSum (PLift (a = b)) (CshakeCallCollision [contentHash256Call a, contentHash256Call b]) :=
  have he := encodeFields_injective _ _ h
  have hh : a.pathBytes = b.pathBytes ∧
      (contentHash256 a).data.toList = (contentHash256 b).data.toList := by simpa using he
  match contentHash256Extract a b (byteArray_eq_of_toList_eq hh.2) with
  | .inl hc => .inl ⟨by cases a; cases b; have hc' := hc.down; simp_all⟩
  | .inr collision => .inr collision

theorem entryFields_binds (a b : VarEntry) (h : entryFields a = entryFields b) :
    a = b ∨ CshakeCollisionAmong [contentHash256Call a, contentHash256Call b] := by
  cases entryFieldsExtract a b h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

def entryListCalls (es : List VarEntry) : List CshakeCall :=
  es.map contentHash256Call

def entryListExtract : ∀ (as bs : List VarEntry),
    as.map entryFields = bs.map entryFields →
    PSum (PLift (as = bs)) (CshakeCallCollision (entryListCalls as ++ entryListCalls bs))
  | [], [], _ => .inl ⟨rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, b :: bs, h =>
    have he := List.cons.inj h
    match entryFieldsExtract a b he.1 with
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))
    | .inl hab =>
      match entryListExtract as bs he.2 with
      | .inl ht => .inl ⟨by rw [hab.down, ht.down]⟩
      | .inr hc =>
        .inr (hc.weaken (by
          intro c hmem
          rcases List.mem_append.1 hmem with hL | hR
          · exact List.mem_append_left _ (.tail _ hL)
          · exact List.mem_append_right _ (.tail _ hR)))

theorem entryList_binds (as bs : List VarEntry) (h : as.map entryFields = bs.map entryFields) :
    as = bs ∨ CshakeCollisionAmong (entryListCalls as ++ entryListCalls bs) := by
  cases entryListExtract as bs h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

def varDataRootCalls (es : List VarEntry) : List CshakeCall :=
  merkleRootCalls (varFields es) ++ entryListCalls (canonicalVar es)

def varDataRootExtract (as bs : List VarEntry) (h : computeVarDataRoot as = computeVarDataRoot bs) :
    PSum (PLift (canonicalVar as = canonicalVar bs))
      (CshakeCallCollision (varDataRootCalls as ++ varDataRootCalls bs)) :=
  match merkleRootExtract (varFields as) (varFields bs) h with
  | .inr hc =>
    .inr (hc.weaken (by
      intro c hmem
      simp only [varDataRootCalls]
      rcases List.mem_append.1 hmem with hL | hR
      · exact List.mem_append_left _ (List.mem_append_left _ hL)
      · exact List.mem_append_right _ (List.mem_append_left _ hR)))
  | .inl he =>
    match entryListExtract (canonicalVar as) (canonicalVar bs) he.down with
    | .inl hcan => .inl hcan
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [varDataRootCalls]
        rcases List.mem_append.1 hmem with hL | hR
        · exact List.mem_append_left _ (List.mem_append_right _ hL)
        · exact List.mem_append_right _ (List.mem_append_right _ hR)))

theorem varDataRoot_binds (as bs : List VarEntry) (h : computeVarDataRoot as = computeVarDataRoot bs) :
    canonicalVar as = canonicalVar bs ∨
      CshakeCollisionAmong (varDataRootCalls as ++ varDataRootCalls bs) := by
  cases varDataRootExtract as bs h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

def packageDigestCall (p : SignedGrainPackage) : CshakeCall :=
  ("OBEND.CUSTODY.PACKAGE/v1",
   [p.publisher.data.toList, p.code.data.toList, p.programDigest.data.toList])

def packageDigestExtract (a b : SignedGrainPackage) (h : packageDigest a = packageDigest b) :
    PSum (PLift (a.publisher = b.publisher ∧ a.code = b.code ∧ a.programDigest = b.programDigest))
      (CshakeCallCollision [packageDigestCall a, packageDigestCall b]) :=
  match hashExtract "OBEND.CUSTODY.PACKAGE/v1"
      [a.publisher.data.toList, a.code.data.toList, a.programDigest.data.toList]
      [b.publisher.data.toList, b.code.data.toList, b.programDigest.data.toList] h with
  | .inl he =>
    have hh : a.publisher.data.toList = b.publisher.data.toList ∧
        a.code.data.toList = b.code.data.toList ∧
        a.programDigest.data.toList = b.programDigest.data.toList := by simpa using he.down
    .inl ⟨byteArray_eq_of_toList_eq hh.1, byteArray_eq_of_toList_eq hh.2.1, byteArray_eq_of_toList_eq hh.2.2⟩
  | .inr hc => .inr hc

theorem packageDigest_binds (a b : SignedGrainPackage) (h : packageDigest a = packageDigest b) :
    (a.publisher = b.publisher ∧ a.code = b.code ∧ a.programDigest = b.programDigest) ∨
      CshakeCollisionAmong [packageDigestCall a, packageDigestCall b] := by
  cases packageDigestExtract a b h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

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

def settlementEvent (s : SettlementLedger) : CustodyHostEvent → SettlementLedger
  | .settle p => settleOrReplay s p
  | .crash => s
  | .restart => s

def runSettlementEvents (s : SettlementLedger) (events : List CustodyHostEvent) : SettlementLedger :=
  events.foldl settlementEvent s

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
    LedgerInvariant id start rent budget (runSettlementEvents s es) := by
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
    let s := runSettlementEvents ⟨openLease id start rent budget, []⟩ events
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

def IngressMountain.rootCalls : IngressMountain → List CshakeCall
  | .leaf n r => [("OBEND.CUSTODY.MOUNTAIN/v1", [[0], leb128 n, r.data.toList])]
  | .node a b =>
    ("OBEND.CUSTODY.MOUNTAIN/v1", [[1], a.root.data.toList, b.root.data.toList]) ::
      (a.rootCalls ++ b.rootCalls)

def IngressMountain.rootExtract : ∀ (a b : IngressMountain), a.root = b.root →
    PSum (PLift (a = b)) (CshakeCallCollision (a.rootCalls ++ b.rootCalls))
  | .leaf n r, .leaf m s, h =>
    match hashExtract "OBEND.CUSTODY.MOUNTAIN/v1"
        [[0], leb128 n, r.data.toList] [[0], leb128 m, s.data.toList] h with
    | .inl hp =>
      have he : leb128 n = leb128 m ∧ r.data.toList = s.data.toList := by simpa using hp.down
      .inl ⟨by rw [natBytes_inj he.1, byteArray_eq_of_toList_eq he.2]⟩
    | .inr hc => .inr hc
  | .leaf n r, .node x y, h =>
    match hashExtract "OBEND.CUSTODY.MOUNTAIN/v1"
        [[0], leb128 n, r.data.toList] [[1], x.root.data.toList, y.root.data.toList] h with
    | .inl hp => False.elim (by have hp' := hp.down; simp at hp')
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))
  | .node x y, .leaf n r, h =>
    match hashExtract "OBEND.CUSTODY.MOUNTAIN/v1"
        [[1], x.root.data.toList, y.root.data.toList] [[0], leb128 n, r.data.toList] h with
    | .inl hp => False.elim (by have hp' := hp.down; simp at hp')
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))
  | .node x y, .node u v, h =>
    match hashExtract "OBEND.CUSTODY.MOUNTAIN/v1"
        [[1], x.root.data.toList, y.root.data.toList] [[1], u.root.data.toList, v.root.data.toList] h with
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))
    | .inl hp =>
      have he : x.root.data.toList = u.root.data.toList ∧ y.root.data.toList = v.root.data.toList := by
        simpa using hp.down
      match x.rootExtract u (byteArray_eq_of_toList_eq he.1) with
      | .inr hc =>
        .inr (hc.weaken (by
          intro c hmem
          rcases List.mem_append.1 hmem with hL | hR
          · exact List.mem_append_left _ (.tail _ (List.mem_append_left _ hL))
          · exact List.mem_append_right _ (.tail _ (List.mem_append_left _ hR))))
      | .inl hx =>
        match y.rootExtract v (byteArray_eq_of_toList_eq he.2) with
        | .inl hy => .inl ⟨by rw [hx.down, hy.down]⟩
        | .inr hc =>
          .inr (hc.weaken (by
            intro c hmem
            rcases List.mem_append.1 hmem with hL | hR
            · exact List.mem_append_left _ (.tail _ (List.mem_append_right _ hL))
            · exact List.mem_append_right _ (.tail _ (List.mem_append_right _ hR))))

theorem IngressMountain.root_binds (a b : IngressMountain) (h : a.root = b.root) :
    a = b ∨ CshakeCollisionAmong (a.rootCalls ++ b.rootCalls) := by
  cases a.rootExtract b h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

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

def peaksRootCalls : List IngressMountain → List CshakeCall
  | [] => []
  | p :: ps => p.rootCalls ++ peaksRootCalls ps

def peaksExtract : ∀ (a b : List IngressMountain),
    (a.map fun p => p.root.data.toList) = (b.map fun p => p.root.data.toList) →
    PSum (PLift (a = b)) (CshakeCallCollision (peaksRootCalls a ++ peaksRootCalls b))
  | [], [], _ => .inl ⟨rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h =>
    have he := List.cons.inj h
    match x.rootExtract y (byteArray_eq_of_toList_eq he.1) with
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [peaksRootCalls]
        rcases List.mem_append.1 hmem with hL | hR
        · exact List.mem_append_left _ (List.mem_append_left _ hL)
        · exact List.mem_append_right _ (List.mem_append_left _ hR)))
    | .inl hx =>
      match peaksExtract xs ys he.2 with
      | .inl ht => .inl ⟨by rw [hx.down, ht.down]⟩
      | .inr hc =>
        .inr (hc.weaken (by
          intro c hmem
          simp only [peaksRootCalls]
          rcases List.mem_append.1 hmem with hL | hR
          · exact List.mem_append_left _ (List.mem_append_right _ hL)
          · exact List.mem_append_right _ (List.mem_append_right _ hR)))

theorem peaks_bind (a b : List IngressMountain)
    (h : (a.map fun p => p.root.data.toList) = (b.map fun p => p.root.data.toList)) :
    a = b ∨ CshakeCollisionAmong (peaksRootCalls a ++ peaksRootCalls b) := by
  cases peaksExtract a b h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

def IngressMmr.rootCalls (s : IngressMmr) : List CshakeCall :=
  ("OBEND.CUSTODY.MMR.ROOT/v1",
   [leb128 s.count, encodeFields (s.peaks.map fun p => p.root.data.toList)]) ::
    peaksRootCalls s.peaks

def IngressMmr.rootExtract (a b : IngressMmr) (h : a.root = b.root) :
    PSum (PLift (a = b)) (CshakeCallCollision (a.rootCalls ++ b.rootCalls)) :=
  match hashExtract "OBEND.CUSTODY.MMR.ROOT/v1"
      [leb128 a.count, encodeFields (a.peaks.map fun p => p.root.data.toList)]
      [leb128 b.count, encodeFields (b.peaks.map fun p => p.root.data.toList)]
      (by unfold IngressMmr.root at h; exact h) with
  | .inr hc =>
    .inr (hc.weaken (by
      intro c hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact List.mem_append_left _ (.head _)
      · exact List.mem_append_right _ (.head _)))
  | .inl hp =>
    have he : leb128 a.count = leb128 b.count ∧
        encodeFields (a.peaks.map fun p => p.root.data.toList) =
          encodeFields (b.peaks.map fun p => p.root.data.toList) := by simpa using hp.down
    have hn := natBytes_inj he.1
    match peaksExtract a.peaks b.peaks (encodeFields_injective _ _ he.2) with
    | .inl hs => .inl ⟨by cases a; cases b; have hs' := hs.down; simp_all⟩
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        rcases List.mem_append.1 hmem with hL | hR
        · exact List.mem_append_left _ (.tail _ hL)
        · exact List.mem_append_right _ (.tail _ hR)))

theorem IngressMmr.root_binds (a b : IngressMmr) (h : a.root = b.root) :
    a = b ∨ CshakeCollisionAmong (a.rootCalls ++ b.rootCalls) := by
  cases a.rootExtract b h with
  | inl he => exact .inl he.down
  | inr hc => exact .inr ⟨hc⟩

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

/-- Constructive `0 Classical` non-omission extractor: either `verifyNonOmission` refuses
    or `original.rootCalls ++ prior.rootCalls` constructively exhibits a `CshakeCallCollision`. -/
def hostOmissionExtract
    (verifySignature : ByteArray → ByteArray → Bool) (t : AriadneTicket)
    (original prior later : IngressMmr) (turns : List (Nat × ByteArray))
    (ht : ValidTicket verifySignature t original)
    (bad : turns[t.seqNo]? ≠ some (t.seqNo, t.reqDigest)) :
    PSum (PLift (verifyNonOmission t prior later turns = false))
         (CshakeCallCollision (original.rootCalls ++ prior.rootCalls)) :=
  if hv : verifyNonOmission t prior later turns = true then
    have he : prior.root = t.mmrRoot ∧ prior.openings.IsPrefix later.openings ∧
        later.openings = turns ∧ t.seqNo < turns.length := of_decide_eq_true hv
    match original.rootExtract prior (ht.2.1.trans he.1.symm) with
    | .inl hp =>
      False.elim (by
        have hEq := hp.down
        subst hEq
        obtain ⟨suffix, hs⟩ := he.2.1
        have hlen : t.seqNo < original.openings.length := List.getElem?_eq_some_iff.1 ht.2.2 |>.1
        have hh : turns[t.seqNo]? = original.openings[t.seqNo]? := by
          rw [← he.2.2.1, ← hs]
          exact List.getElem?_append_left hlen
        exact bad (hh.trans ht.2.2))
    | .inr hc => .inr hc
  else
    .inl ⟨Bool.eq_false_iff.mpr hv⟩

/-- An accepted later turns cannot delete or substitute a committed sequential opening.
A different opening of the ticket's MMR root constructs an actual cSHAKE collision
inside `original.rootCalls ++ prior.rootCalls`. -/
theorem host_cannot_omit_committed_turn_or_collision
    (verifySignature : ByteArray → ByteArray → Bool) (t : AriadneTicket)
    (original prior later : IngressMmr) (turns : List (Nat × ByteArray))
    (ht : ValidTicket verifySignature t original)
    (bad : turns[t.seqNo]? ≠ some (t.seqNo, t.reqDigest)) :
    verifyNonOmission t prior later turns = false ∨
      CshakeCollisionAmong (original.rootCalls ++ prior.rootCalls) := by
  cases hostOmissionExtract verifySignature t original prior later turns ht bad with
  | inl hf => exact .inl hf.down
  | inr hc => exact .inr ⟨hc⟩

structure GrainCustodyAnchor where
  generation : Nat
  packageDigest : ByteArray
  varDataRoot : ByteArray
  receiptHead : ByteArray
  leaseRoot : ByteArray
  ingressRoot : ByteArray
  deriving DecidableEq

structure GrainArchive where
  package : SignedGrainPackage
  entries : List VarEntry
  anchor : GrainCustodyAnchor
  previousHead : ByteArray
  frozenGrain : GrainPowerbox.FrozenGrain
  lease : PrepaidLease
  settlements : SettlementLedger
  ingress : IngressMmr
  executions : List (Nat × ByteArray × ByteArray)
  transitionSignature : ByteArray

inductive CustodyPoisonReason where
  | package | varData | lease | ingress | signature | divergence | rollback | brokenReceipt | missingArchive
  deriving DecidableEq, Repr
inductive GrainCustodyStatus where
  | empty | ready | recoveryRequired | poisoned (reason : CustodyPoisonReason)
  deriving DecidableEq, Repr

def settlementRoot (s : SettlementLedger) : ByteArray :=
  merkleRoot (s.records.reverse.map fun (key, receipt) =>
    encodeFields [leb128 key.1.toNat, leb128 key.2, receipt.data.toList])

def executionRoot (xs : List (Nat × ByteArray × ByteArray)) : ByteArray :=
  merkleRoot (xs.map fun (n, req, receipt) =>
    encodeFields [leb128 n, req.data.toList, receipt.data.toList])

def transitionHead (a : GrainArchive) : ByteArray :=
  hash "OBEND.CUSTODY.ARCHIVE/v1" [a.previousHead.data.toList, leb128 a.anchor.generation,
    a.anchor.packageDigest.data.toList, a.anchor.varDataRoot.data.toList, a.anchor.leaseRoot.data.toList,
    (frozenGrainRoot a.frozenGrain).data.toList, (settlementRoot a.settlements).data.toList,
    a.anchor.ingressRoot.data.toList, (executionRoot a.executions).data.toList]

def transitionHeadCall (a : GrainArchive) : CshakeCall :=
  ("OBEND.CUSTODY.ARCHIVE/v1",
   [a.previousHead.data.toList, leb128 a.anchor.generation,
    a.anchor.packageDigest.data.toList, a.anchor.varDataRoot.data.toList, a.anchor.leaseRoot.data.toList,
    (frozenGrainRoot a.frozenGrain).data.toList, (settlementRoot a.settlements).data.toList,
    a.anchor.ingressRoot.data.toList, (executionRoot a.executions).data.toList])

/-- Equality of transition heads binds every committed component, or supplies an actual
full-output cSHAKE collision in `[transitionHeadCall a, transitionHeadCall b]`. -/
theorem transitionHead_binds (a b : GrainArchive) (h : transitionHead a = transitionHead b) :
    (a.previousHead = b.previousHead ∧ a.anchor.generation = b.anchor.generation ∧
      a.anchor.packageDigest = b.anchor.packageDigest ∧ a.anchor.varDataRoot = b.anchor.varDataRoot ∧
      a.anchor.leaseRoot = b.anchor.leaseRoot ∧ frozenGrainRoot a.frozenGrain = frozenGrainRoot b.frozenGrain ∧
      settlementRoot a.settlements = settlementRoot b.settlements ∧
      a.anchor.ingressRoot = b.anchor.ingressRoot ∧ executionRoot a.executions = executionRoot b.executions) ∨
    CshakeCollisionAmong [transitionHeadCall a, transitionHeadCall b] := by
  cases hashExtract "OBEND.CUSTODY.ARCHIVE/v1" (transitionHeadCall a).2 (transitionHeadCall b).2 h with
  | inl he =>
    have he' := he.down
    simp only [transitionHeadCall, List.cons.injEq, and_true] at he'
    obtain ⟨hp, hg, hk, hv, hl, hf, hs, hi, hx⟩ := he'
    exact .inl ⟨byteArray_eq_of_toList_eq hp, natBytes_inj hg,
      byteArray_eq_of_toList_eq hk, byteArray_eq_of_toList_eq hv,
      byteArray_eq_of_toList_eq hl, byteArray_eq_of_toList_eq hf,
      byteArray_eq_of_toList_eq hs, byteArray_eq_of_toList_eq hi, byteArray_eq_of_toList_eq hx⟩
  | inr hc => exact .inr ⟨hc⟩

/-- Signature verification is supplied by the authenticated package boundary, not a hash predicate. -/
@[expose] def reopenCustody (authenticate : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool)
    (archive : Option GrainArchive) (anchor : Option GrainCustodyAnchor) : GrainCustodyStatus :=
  match archive, anchor with
  | none, none => .empty
  | none, some _ => .poisoned .missingArchive
  | some a, base =>
    if authenticate a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest then .poisoned .package
    else if computeVarDataRoot a.entries ≠ a.anchor.varDataRoot then .poisoned .varData
    else if transitionHead a ≠ a.anchor.receiptHead then .poisoned .brokenReceipt
    else if a.anchor.leaseRoot ≠ leaseStateRoot a.lease ∨ a.settlements.lease ≠ a.lease then .poisoned .lease
    else if a.anchor.ingressRoot ≠ a.ingress.root then .poisoned .ingress
    else if verify (transitionHead a) a.transitionSignature = false then .poisoned .signature
    else match base with
      | none => if a.anchor.generation = 0 then .recoveryRequired else .poisoned .divergence
      | some b =>
        if a.anchor.packageDigest ≠ b.packageDigest then .poisoned .package
        else if a.anchor = b then .ready
        else if a.anchor.generation < b.generation then .poisoned .rollback
        else if a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead then .recoveryRequired
        else .poisoned .divergence

theorem var_mismatch_poisoned (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) (h : computeVarDataRoot a.entries ≠ a.anchor.varDataRoot) :
    ∃ reason, reopenCustody auth verify (some a) b = .poisoned reason := by
  by_cases hp : auth a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest
  · exact ⟨.package, by simp [reopenCustody, hp]⟩
  · exact ⟨.varData, by simp [reopenCustody, hp, h]⟩

theorem package_mismatch_poisoned (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) (h : packageDigest a.package ≠ a.anchor.packageDigest) :
    reopenCustody auth verify (some a) b = .poisoned .package := by
  simp [reopenCustody, h]

/-- Reopening a changed canonical image either refuses it or exhibits a concrete collision
    among `varDataRootCalls a.entries ++ varDataRootCalls original`.
    Package substitution is checked against the immutable digest in the same archived anchor. -/
theorem tampered_var_or_package_poisoned_or_collision
    (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive) (b : Option GrainCustodyAnchor)
    (original : List VarEntry) (hroot : a.anchor.varDataRoot = computeVarDataRoot original)
    (ht : canonicalVar a.entries ≠ canonicalVar original ∨ packageDigest a.package ≠ a.anchor.packageDigest) :
    (∃ reason, reopenCustody auth verify (some a) b = .poisoned reason) ∨
      CshakeCollisionAmong (varDataRootCalls a.entries ++ varDataRootCalls original) := by
  rcases ht with hv | hp
  · if he : computeVarDataRoot a.entries = a.anchor.varDataRoot then
      rcases varDataRoot_binds a.entries original (he.trans hroot) with hf | hc
      · exact False.elim (hv hf)
      · exact .inr hc
    else
      exact .inl (var_mismatch_poisoned auth verify a b he)
  · exact .inl ⟨.package, package_mismatch_poisoned auth verify a b hp⟩

def recoverOneAhead (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive)
    (b : Option GrainCustodyAnchor) : Option GrainCustodyAnchor :=
  if reopenCustody auth verify (some a) b = .recoveryRequired then some a.anchor else none

attribute [local irreducible] hash merkleRoot leaseStateRoot

theorem recovery_facts (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive) (b : GrainCustodyAnchor)
    (h : reopenCustody auth verify (some a) (some b) = .recoveryRequired) :
    auth a.package = true ∧ packageDigest a.package = a.anchor.packageDigest ∧
    computeVarDataRoot a.entries = a.anchor.varDataRoot ∧ transitionHead a = a.anchor.receiptHead ∧
    a.anchor.packageDigest = b.packageDigest ∧ a.anchor.generation = b.generation + 1 ∧
    a.previousHead = b.receiptHead ∧ a.anchor.leaseRoot = leaseStateRoot a.lease ∧
    a.settlements.lease = a.lease ∧ a.anchor.ingressRoot = a.ingress.root ∧
    verify (transitionHead a) a.transitionSignature = true := by
  simp only [reopenCustody] at h
  repeat first | contradiction | split at h
  all_goals simp_all

theorem one_ahead_crash_recovery_exact (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool)
    (a : GrainArchive) (b : GrainCustodyAnchor)
    (h : reopenCustody auth verify (some a) (some b) = .recoveryRequired) :
    recoverOneAhead auth verify a (some b) = some a.anchor ∧
    reopenCustody auth verify (some a) (some a.anchor) = .ready ∧
    a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead := by
  obtain ⟨ha, hp, hv, ht, _, hg, hh, hl, hs, hi, hvfy⟩ := recovery_facts auth verify a b h
  refine ⟨by simp [recoverOneAhead, h], ?_, hg, hh⟩
  have hvfy' : verify a.anchor.receiptHead a.transitionSignature = true := by simpa [ht] using hvfy
  simp [reopenCustody, ha, hp, hv, ht, hl, hs, hi, hvfy']

theorem two_ahead_poisoned (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool) (a : GrainArchive)
    (b : GrainCustodyAnchor) (h : b.generation + 2 ≤ a.anchor.generation) :
    ∃ reason, reopenCustody auth verify (some a) (some b) = .poisoned reason := by
  have hn : a.anchor ≠ b := by intro he; have := congrArg GrainCustodyAnchor.generation he; omega
  have hg : a.anchor.generation ≠ b.generation + 1 := by omega
  have hl : ¬ a.anchor.generation < b.generation := by omega
  simp only [reopenCustody]
  repeat first | (exact ⟨_, rfl⟩) | split
  all_goals simp_all

/-- Both ordinary reopen and WAL replay authenticate the complete transition. -/
theorem unsigned_archive_refused (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (a : GrainArchive) (b : Option GrainCustodyAnchor)
    (h : verify (transitionHead a) a.transitionSignature = false) :
    ∃ reason, reopenCustody auth verify (some a) b = .poisoned reason := by
  simp only [reopenCustody]
  repeat first | (exact ⟨_, rfl⟩) | split
  all_goals simp_all

theorem lease_mismatch_refused (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (a : GrainArchive) (b : Option GrainCustodyAnchor)
    (h : a.anchor.leaseRoot ≠ leaseStateRoot a.lease) :
    ∃ reason, reopenCustody auth verify (some a) b = .poisoned reason := by
  simp only [reopenCustody]
  repeat first | (exact ⟨_, rfl⟩) | split
  all_goals simp_all

/-- Seal the composed after-image; signatures are not modeled as hashes. -/
def sealArchive (sign : ByteArray → ByteArray) (a : GrainArchive) : GrainArchive :=
  let anchor := { a.anchor with
    packageDigest := packageDigest a.package
    varDataRoot := computeVarDataRoot a.entries
    leaseRoot := leaseStateRoot a.lease
    ingressRoot := a.ingress.root }
  let a := { a with anchor := anchor, settlements := {a.settlements with lease := a.lease} }
  { a with
    anchor := { a.anchor with receiptHead := transitionHead a }
    transitionSignature := sign (transitionHead a) }

theorem sealed_one_ahead_recovers (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (sign : ByteArray → ByteArray)
    (law : ∀ msg, verify msg (sign msg) = true) (a : GrainArchive) (base : GrainCustodyAnchor)
    (hp : auth a.package = true) (hb : packageDigest a.package = base.packageDigest)
    (hg : a.anchor.generation = base.generation + 1) (hh : a.previousHead = base.receiptHead) :
    reopenCustody auth verify (some (sealArchive sign a)) (some base) = .recoveryRequired := by
  have hn : (sealArchive sign a).anchor ≠ base := by
    intro he
    have he := congrArg GrainCustodyAnchor.generation he
    simp only [sealArchive] at he
    omega
  simp only [sealArchive, transitionHead, hg, hb, hh] at hn
  simp [reopenCustody, sealArchive, transitionHead, hp, hb, hg, hh, law, hn,
    show ¬ base.generation + 1 < base.generation by omega]

/-- The archive and one-ahead WAL survive a crash; the working image does not. -/
structure GrainCustodyHost where
  durable : GrainArchive
  wal : Option GrainArchive
  volatile : Option GrainArchive

def custodyEvent (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool)
    (s : GrainCustodyHost) : CustodyHostEvent → GrainCustodyHost
  | .crash => {s with volatile := none}
  | .restart =>
    let candidate := s.wal.getD s.durable
    match reopenCustody auth verify (some candidate) (some s.durable.anchor) with
    | .ready | .recoveryRequired => ⟨candidate, none, some candidate⟩
    | _ => {s with volatile := none}
  | .settle p =>
    match s.volatile with
    | none => s
    | some a =>
      let ledger := settleOrReplay a.settlements p
      {s with volatile := some {a with lease := ledger.lease, settlements := ledger}}

theorem crash_erases_volatile (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (s : GrainCustodyHost) :
    (custodyEvent auth verify s .crash).volatile = none ∧
    (custodyEvent auth verify s .crash).durable = s.durable ∧
    (custodyEvent auth verify s .crash).wal = s.wal := by
  simp [custodyEvent]

theorem restart_ignores_uncommitted (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (s : GrainCustodyHost) (v : Option GrainArchive) :
    custodyEvent auth verify {s with volatile := v} .restart =
      custodyEvent auth verify {s with volatile := none} .restart := by
  simp [custodyEvent]

/-- Prepare a signed WAL after-image from volatile state. Installation uses the same
reopen verifier as crash recovery; an existing pending image cannot be overwritten. -/
def prepareCustody (auth : SignedGrainPackage → Bool) (verify : ByteArray → ByteArray → Bool)
    (sign : ByteArray → ByteArray) (s : GrainCustodyHost) : Option GrainCustodyHost :=
  match s.wal, s.volatile with
  | none, some working =>
    let next := sealArchive sign {working with
      previousHead := s.durable.anchor.receiptHead
      anchor := {working.anchor with generation := s.durable.anchor.generation + 1}}
    if reopenCustody auth verify (some next) (some s.durable.anchor) = .recoveryRequired then
      some {s with wal := some next}
    else none
  | _, _ => none

theorem prepared_wal_authenticated (auth : SignedGrainPackage → Bool)
    (verify : ByteArray → ByteArray → Bool) (sign : ByteArray → ByteArray)
    (s next : GrainCustodyHost) (h : prepareCustody auth verify sign s = some next) :
    next.durable = s.durable ∧ ∃ a, next.wal = some a ∧
      reopenCustody auth verify (some a) (some s.durable.anchor) = .recoveryRequired := by
  cases hw : s.wal with
  | some pending => simp [prepareCustody, hw] at h
  | none =>
    cases hv : s.volatile with
    | none => simp [prepareCustody, hw, hv] at h
    | some working =>
      let a := sealArchive sign {working with
        previousHead := s.durable.anchor.receiptHead
        anchor := {working.anchor with generation := s.durable.anchor.generation + 1}}
      simp only [prepareCustody, hw, hv] at h
      change (if reopenCustody auth verify (some a) (some s.durable.anchor) = .recoveryRequired
        then some {s with wal := some a, volatile := some working} else none) = some next at h
      by_cases hc : reopenCustody auth verify (some a) (some s.durable.anchor) = .recoveryRequired
      · have he : {s with wal := some a, volatile := some working} = next := by simpa only [if_pos hc, Option.some.injEq] using h
        subst next
        exact ⟨rfl, a, rfl, hc⟩
      · simp [hc] at h

/-- Restoring authority uses the powerbox revocation and provenance machinery. -/
def restorePowerbox (host : GrainPowerbox.PowerboxHost) (a : GrainArchive) : GrainPowerbox.GrainState :=
  GrainPowerbox.thawGrain host a.frozenGrain

end Obend.Polis.Custody
