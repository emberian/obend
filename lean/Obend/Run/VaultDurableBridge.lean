module
/-
# Obend.Run.VaultDurableBridge — Segmented Disk Log → `Run.Durable` Simulation & `Transferable` Plans

1. **Part A (`SegmentLog` → `Run.Durable`):** Forward simulation (`SegmentedSimInv`,
   `segmentedStep_refines_durable`) between fixed-width `SegmentLog` disk blocks of `OBL1` frames
   and `Run.Durable`, proving multi-segment rotation (`segmented_append_rotates_across_boundary`),
   torn-tail crash recovery (`parseFrom_committed_with_torn_frame`,
   `segmented_torn_crash_recover_idempotent`), and `segmented_exposed_once`.
2. **Part B (`Ty.isTransferable` + `CapTable` Sealing Across `.perform`):** Extends `Ty.isData` /
   `Ty.isPlan` with `.custody` leaves while forbidding higher-order types, and proves exact linear
   capability dehydration/rehydration round-trip (`rehydrate_dehydrate_roundtrip`), custody
   conservation (`transfer_conserves_custody_exact`), and deterministic forgery/tamper refusals.
-/
public import Obend.Run.Durable
public import Obend.Run.Proofs.Durable
public import Obend.Vault.SegmentLog
public import Obend.Core.Ty
public import Obend.Core.Data
import all Obend.Run.Durable
import all Obend.Core.Data

public section

set_option autoImplicit false

/-! ## Part B.1 — `Ty.isTransferable` on `Obend.Core.Ty` -/

namespace Obend.Core.Ty

/-- First-order transferable types: `Ty.isData` extended with linear `.custody` leaves. -/
@[expose] def Ty.isTransferable : Ty → Bool
  | .natural | .label | .boolean | .emptyRow | .custody _ => true
  | .field _ member tail => member.isTransferable && tail.isTransferable
  | .variant row => row.isTransferable
  | _ => false

/-- A capability-carrying Plan is a variant sum over `isTransferable` action payloads. -/
@[expose] def Ty.isTransferablePlan : Ty → Bool
  | .variant row => row.isTransferable
  | _ => false

theorem isData_imp_isTransferable : ∀ (ty : Ty), ty.isData = true → ty.isTransferable = true
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ => rfl
  | .field _ member tail, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp [Ty.isTransferable, isData_imp_isTransferable member h.1, isData_imp_isTransferable tail h.2]
  | .variant row, h => by
    simp only [Ty.isData] at h; simp [Ty.isTransferable, isData_imp_isTransferable row h]

theorem isPlan_imp_isTransferablePlan (ty : Ty) (h : ty.isPlan = true) :
    ty.isTransferablePlan = true := by
  cases ty with
  | variant row => exact isData_imp_isTransferable row h
  | _ => cases h

/-- `.custody id` is `isTransferable` (crosses `.perform` via `CapTable`) but not pure `isData`. -/
theorem custody_isTransferable_not_isData (id : Nat) :
    (Ty.custody id).isTransferable = true ∧ (Ty.custody id).isData = false := ⟨rfl, rfl⟩

/-- `isTransferable` forbids closures, activities, prototypes, specifications, and rigid variables. -/
theorem isTransferable_forbids_higher_order (ty : Ty) (h : ty.isTransferable = true) :
    ty.isComputation = false ∧ (∀ r q d c, ty ≠ .arrow r q d c) ∧
    (∀ s t, ty ≠ .prototype s t) ∧ (∀ m e, ty ≠ .specification m e) ∧
    (∀ idx, ty ≠ .variable idx) := by
  cases ty <;> simp_all [Ty.isTransferable, Ty.isComputation]

end Obend.Core.Ty

namespace Obend.Run.VaultDurableBridge

open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Vault.Log (Bytes Record Drop encodeRecord encodeAll parseOne parseFrom
  Linked lastHash dig dig_lt Hr be unbe bound magic)
open Obend.Vault.Rehydration (WitnessReceipt genesisSentinel)
open Obend.Vault.SegmentLog (capacity split split_join)
open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared Obend.Run.Durable

/-! ## Part A — Segmented Disk Log (`SegmentLog`) Refines `Run.Durable` -/

/-- Canonical little-endian variable-length byte encoding of `Nat` (`[]` for `0`). -/
def encodeNatLE : Nat → Bytes
  | 0 => []
  | n + 1 => UInt8.ofNat ((n + 1) % 256) :: encodeNatLE ((n + 1) / 256)
termination_by n => n

/-- Inverse decoder for `encodeNatLE`. -/
def decodeNatLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeNatLE bs

@[simp] theorem decodeNatLE_encodeNatLE (n : Nat) : decodeNatLE (encodeNatLE n) = n := by
  induction n using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [encodeNatLE, decodeNatLE]
    | succ m =>
      rw [encodeNatLE]; simp only [decodeNatLE, UInt8.toNat_ofNat']
      rw [ih ((m + 1) / 256) (by omega)]; omega

/-- A committed durable log entry persisted on disk (`journal` append or `outbox` exposure). -/
inductive DiskEntry (Ev : Type) where
  | journalAppend (ev : Ev)
  | outboxExpose (pos : Nat)
  deriving DecidableEq, Repr

/-- Verified byte-level wire codec for domain joint events `Ev`. -/
structure EventWireCodec (Ev : Type) where
  encodeEv : Ev → Bytes
  decodeEv : Bytes → Option Ev
  decode_encodeEv : ∀ (ev : Ev), decodeEv (encodeEv ev) = some ev

/-- Inhabited canonical `EventWireCodec` for `Nat` payloads. -/
def natEventCodec : EventWireCodec Nat where
  encodeEv := encodeNatLE
  decodeEv := fun bs => some (decodeNatLE bs)
  decode_encodeEv := fun ev => congrArg some (decodeNatLE_encodeNatLE ev)

/-- Encode `DiskEntry Ev` with a 1-byte tag prefix (`0x01` = journal, `0x02` = outbox). -/
def encodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev) : DiskEntry Ev → Bytes
  | .journalAppend ev => (1 : UInt8) :: codec.encodeEv ev
  | .outboxExpose pos => (2 : UInt8) :: encodeNatLE pos

/-- Decode `DiskEntry Ev` from payload bytes. -/
def decodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev) : Bytes → Option (DiskEntry Ev)
  | 1 :: rest => (codec.decodeEv rest).map .journalAppend
  | 2 :: rest => some (.outboxExpose (decodeNatLE rest))
  | _ => none

@[simp] theorem decodeDiskEntry_encodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev)
    (e : DiskEntry Ev) : decodeDiskEntry codec (encodeDiskEntry codec e) = some e := by
  cases e with
  | journalAppend ev => simp [encodeDiskEntry, decodeDiskEntry, codec.decode_encodeEv]
  | outboxExpose pos => simp [encodeDiskEntry, decodeDiskEntry]

/-- Left-to-right fold of decoded `DiskEntry` records into `(journal, outbox)`. -/
def foldDiskEntries {Ev : Type} (codec : EventWireCodec Ev) :
    List Record → List Ev → List Nat → Option (List Ev × List Nat)
  | [], j, o => some (j, o)
  | r :: rs, j, o =>
    match decodeDiskEntry codec r.payload with
    | some (.journalAppend ev) => foldDiskEntries codec rs (j ++ [ev]) o
    | some (.outboxExpose pos) => foldDiskEntries codec rs j (o ++ [pos])
    | none => none

/-- Decode a committed `List Record` into `(journal, outbox)`. -/
@[expose] def decodeDurableRecords {Ev : Type} (codec : EventWireCodec Ev)
    (rs : List Record) : Option (List Ev × List Nat) :=
  foldDiskEntries codec rs [] []

theorem foldDiskEntries_snoc {Ev : Type} (codec : EventWireCodec Ev) :
    ∀ (rs : List Record) (r : Record) (j : List Ev) (o : List Nat) (j' : List Ev) (o' : List Nat),
      foldDiskEntries codec rs j o = some (j', o') →
      foldDiskEntries codec (rs ++ [r]) j o =
        match decodeDiskEntry codec r.payload with
        | some (.journalAppend ev) => some (j' ++ [ev], o')
        | some (.outboxExpose pos) => some (j', o' ++ [pos])
        | none => none
  | [], r, _, _, _, _, h => by
    simp only [foldDiskEntries, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp only [List.nil_append, foldDiskEntries]
    cases decodeDiskEntry codec r.payload with
    | none => rfl
    | some entry => cases entry <;> rfl
  | x :: xs, r, j, o, j', o', h => by
    simp only [foldDiskEntries] at h
    cases hd : decodeDiskEntry codec x.payload with
    | none => rw [hd] at h; cases h
    | some entry =>
      rw [hd] at h
      cases entry with
      | journalAppend ev =>
        simp only [List.cons_append, foldDiskEntries, hd]
        exact foldDiskEntries_snoc codec xs r (j ++ [ev]) o j' o' h
      | outboxExpose pos =>
        simp only [List.cons_append, foldDiskEntries, hd]
        exact foldDiskEntries_snoc codec xs r j (o ++ [pos]) j' o' h

/-- Construct a well-formed, hash-chained `Vault.Log.Record` following `prev`. -/
def mkChainedRecord (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) : Record :=
  let d := dig Hb payload
  ⟨⟨prev, prev, d, d⟩, payload⟩

theorem mkChainedRecord_wf (Hb : Bytes → Bytes) {prev : Nat} (hp : prev < bound)
    {payload : Bytes} (hlen : payload.length < 256 ^ 4) :
    (mkChainedRecord Hb prev payload).WF Hb :=
  ⟨hp, hp, dig_lt Hb payload, rfl, hlen⟩

theorem mkChainedRecord_prevHash (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) :
    (mkChainedRecord Hb prev payload).receipt.prevHash = prev := by
  rfl

theorem mkChainedRecord_payload (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) :
    (mkChainedRecord Hb prev payload).payload = payload := by
  rfl

/-- Append raw frame bytes into fixed-capacity physical disk segments via `SegmentLog.split`. -/
def appendSegmentedBytes (segCap : Nat) (hCap : 0 < segCap) (segments : List Bytes) (bs : Bytes) :
    List Bytes :=
  split segCap hCap (segments.flatten ++ bs)

theorem appendSegmentedBytes_flatten (segCap : Nat) (hCap : 0 < segCap)
    (segments : List Bytes) (bs : Bytes) :
    (appendSegmentedBytes segCap hCap segments bs).flatten = segments.flatten ++ bs :=
  split_join segCap hCap (segments.flatten ++ bs)

/-- **Segment Boundary Rotation**: pushing total bytes past `segCap` rotates into `≥ 2` segments. -/
theorem segmented_append_rotates_across_boundary (segCap : Nat) (hCap : 0 < segCap)
    (segments : List Bytes) (bs : Bytes) (hCross : segCap < (segments.flatten ++ bs).length) :
    2 ≤ (appendSegmentedBytes segCap hCap segments bs).length ∧
    ∃ seg0 rest,
      appendSegmentedBytes segCap hCap segments bs = seg0 :: rest ∧
      seg0.length = segCap ∧ rest ≠ [] := by
  unfold appendSegmentedBytes
  generalize segments.flatten ++ bs = total at hCross
  rw [split]
  have hne : total.isEmpty = false := by
    cases h : total.isEmpty with
    | false => rfl
    | true => rw [List.isEmpty_iff.mp h] at hCross; simp at hCross
  simp only [hne, Bool.false_eq_true, ↓reduceIte]; rw [split]
  have hrem_pos : 0 < (total.drop segCap).length := by simp only [List.length_drop]; omega
  have hrem_ne : (total.drop segCap).isEmpty = false := by
    cases h : (total.drop segCap).isEmpty with
    | false => rfl
    | true => rw [List.isEmpty_iff.mp h] at hrem_pos; simp at hrem_pos
  simp only [hrem_ne, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by simp, total.take segCap, _, rfl, ?_, by simp⟩
  simp only [List.length_take]; omega

/-- Any empty or `parseOne`-rejected trailing bytes are discarded cleanly by `parseFrom`. -/
theorem parseFrom_committed_with_rejected_tail (Hb : Bytes → Bytes) (rs : List Record)
    (hl : Linked Hb genesisSentinel rs) (hwf : ∀ r ∈ rs, r.WF Hb) (tail : Bytes)
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d) :
    (parseFrom Hb genesisSentinel (encodeAll Hb rs ++ tail)).1 = rs := by
  rw [Obend.Vault.Log.parseFrom_encodeAll Hb rs genesisSentinel hl hwf tail]
  rcases hRej with rfl | ⟨d, hd⟩
  · simp [Obend.Vault.Log.parseFrom_nil]
  · by_cases hne : tail = []
    · subst hne; simp [Obend.Vault.Log.parseFrom_nil]
    · rw [Obend.Vault.Log.parseFrom_error Hb hne hd]; simp

/-- **Torn-Frame Crash Recovery**: any torn in-flight frame `k < length` is truncated to `rs`. -/
theorem parseFrom_committed_with_torn_frame (Hb : Bytes → Bytes) (segCap : Nat) (hCap : 0 < segCap)
    (rs : List Record) (hl : Linked Hb genesisSentinel rs) (hwf : ∀ r ∈ rs, r.WF Hb)
    (r_inflight : Record) (hwf_in : r_inflight.WF Hb)
    (k : Nat) (hk : k < (encodeRecord Hb r_inflight).length) :
    let crashedSegs := split segCap hCap (encodeAll Hb rs ++ (encodeRecord Hb r_inflight).take k)
    (parseFrom Hb genesisSentinel crashedSegs.flatten).1 = rs := by
  dsimp only; rw [split_join]
  apply parseFrom_committed_with_rejected_tail Hb rs hl hwf
  by_cases hk0 : k = 0
  · subst hk0; exact .inl (by simp)
  · exact .inr ⟨.torn, Obend.Vault.Log.parseOne_torn Hb hwf_in
      (List.take_append_drop k (encodeRecord Hb r_inflight))
      (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩

/-- Necessity witness: a 5-byte torn `OBL1` header is non-empty garbage flagged as `some .torn`. -/
theorem torn_header_flagged_as_torn (Hb : Bytes → Bytes) :
    let r := mkChainedRecord Hb genesisSentinel [42]
    let tornBytes := (encodeRecord Hb r).take 5
    tornBytes ≠ [] ∧ parseFrom Hb genesisSentinel tornBytes = ([], tornBytes, some .torn) := by
  dsimp only
  have hwf : (mkChainedRecord Hb genesisSentinel [42]).WF Hb :=
    mkChainedRecord_wf Hb (by decide) (by decide)
  have hne : ((encodeRecord Hb (mkChainedRecord Hb genesisSentinel [42])).take 5) ≠ [] := by
    intro h; have := congrArg List.length h
    rw [List.length_take, Obend.Vault.Log.encodeRecord_length] at this
    simp only [mkChainedRecord, List.length_singleton, List.length_nil] at this; omega
  have htorn : parseOne Hb (some genesisSentinel)
      ((encodeRecord Hb (mkChainedRecord Hb genesisSentinel [42])).take 5) = .error .torn :=
    Obend.Vault.Log.parseOne_torn Hb hwf (List.take_append_drop 5 _) (by
      rw [Ne, List.drop_eq_nil_iff, Obend.Vault.Log.encodeRecord_length]
      simp only [mkChainedRecord, List.length_singleton]; omega)
  exact ⟨hne, Obend.Vault.Log.parseFrom_error Hb hne htorn⟩

/-! ### Segmented Durable Host & Forward Simulation to `Obend.Run.Durable` -/

section Simulation
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {i₀ : Ix}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]

/-- Physical host state backed by `Vault.SegmentLog` fixed-width disk blocks plus volatile memory. -/
structure SegmentedDState (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type)
    (P Cand Fact Ob : Type) (i₀ : Ix) where
  segCap : Nat
  segCap_pos : 0 < segCap
  segments : List Bytes
  mem : Option (JCfg L S Hole A P Cand Fact Ob i₀)

/-- Initial segmented host state at block width `segCap`. -/
def SegmentedDState.init (L : Ledger ι W Tok) (segCap : Nat) (hCap : 0 < segCap)
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) : SegmentedDState L S Hole A P Cand Fact Ob i₀ :=
  ⟨segCap, hCap, [], some J₀⟩

/-- Default 64 KiB `SegmentLog.capacity` initial state. -/
def SegmentedDState.initDefault (L : Ledger ι W Tok) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ :=
  SegmentedDState.init L capacity (by decide) J₀

/-- Segmented host events, extending `.crash` with torn/unfsynced trailing frames on disk. -/
inductive SegmentedHEvent (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type)
    (P Cred Cand Fact : Type) where
  | submit (ev : JEv L S Hole A P Cred Cand Fact)
  | expose (n : Nat)
  | tornCrash (r_inflight : Record) (k : Nat)
  | cleanCrash
  | recover

/-- Map a physical `SegmentedHEvent` to its abstract `Obend.Run.Durable.HEvent` counterpart. -/
@[expose] def SegmentedHEvent.toAbstract {L : Ledger ι W Tok} :
    SegmentedHEvent L S Hole A P Cred Cand Fact → HEvent L S Hole A P Cred Cand Fact
  | .submit ev => .submit ev
  | .expose n => .expose n
  | .tornCrash _ _ | .cleanCrash => .crash
  | .recover => .recover

/-- Refusals of the segmented disk host. -/
inductive SegmentedRefusal (ι Tok : Type) (S : Sig Ix) (Hole : Ix → Type) (P Cand Fact : Type) where
  | host (r : HRefusal ι Tok S Hole P Cand Fact)
  | frameTooLarge
  | dirtyTailNeedsRecovery
  | invalidTornSpec

/-- Decode `(journal, outbox)` from the physical segment list of `disk`. -/
def recoverJournalAndOutbox {L : Ledger ι W Tok} (Hb : Bytes → Bytes)
    (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀) :
    Option (List (JEv L S Hole A P Cred Cand Fact) × List Nat) :=
  decodeDurableRecords codec (parseFrom Hb genesisSentinel disk.segments.flatten).1

/-- One physical step of the segmented durable host (submit/rotate, expose, crash/tear, recover). -/
def segmentedStep (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀)
    (hev : SegmentedHEvent L S Hole A P Cred Cand Fact) :
    Except (SegmentedRefusal ι Tok S Hole P Cand Fact) (SegmentedDState L S Hole A P Cand Fact Ob i₀) :=
  let parsed := parseFrom Hb genesisSentinel disk.segments.flatten
  let rs := parsed.1
  let tail := parsed.2.1
  match hev with
  | .submit ev =>
    if !tail.isEmpty then .error .dirtyTailNeedsRecovery else
    match disk.mem with
    | none => .error (.host .down)
    | some J =>
      let payload := encodeDiskEntry codec (.journalAppend ev)
      if payload.length < 256 ^ 4 then
        match jrun L base sp au k J ev with
        | .ok J' =>
          let newRec := mkChainedRecord Hb (lastHash Hb genesisSentinel rs) payload
          let segs' := appendSegmentedBytes disk.segCap disk.segCap_pos disk.segments (encodeRecord Hb newRec)
          .ok ⟨disk.segCap, disk.segCap_pos, segs', some J'⟩
        | .error r => .error (.host (.joint r))
      else .error .frameTooLarge
  | .expose n =>
    if !tail.isEmpty then .error .dirtyTailNeedsRecovery else
    match decodeDurableRecords codec rs with
    | none => .error (.host .corrupt)
    | some (journal, outbox) =>
      match journal[n]? with
      | some (.dispatch _ _) =>
        if n ∈ outbox then .error (.host (.exposed n)) else
        let payload := encodeDiskEntry codec (.outboxExpose n)
        if payload.length < 256 ^ 4 then
          let newRec := mkChainedRecord Hb (lastHash Hb genesisSentinel rs) payload
          let segs' := appendSegmentedBytes disk.segCap disk.segCap_pos disk.segments (encodeRecord Hb newRec)
          .ok ⟨disk.segCap, disk.segCap_pos, segs', disk.mem⟩
        else .error .frameTooLarge
      | _ => .error (.host (.notDispatch n))
  | .cleanCrash => .ok ⟨disk.segCap, disk.segCap_pos, disk.segments, none⟩
  | .tornCrash r_in bytesWritten =>
    if r_in.receipt.prevHash < bound ∧ r_in.receipt.oldCommit < bound ∧
        r_in.receipt.newCommit < bound ∧ r_in.receipt.effectsHash = dig Hb r_in.payload ∧
        r_in.payload.length < 256 ^ 4 ∧ bytesWritten < (encodeRecord Hb r_in).length then
      let crashedSegs := split disk.segCap disk.segCap_pos
        (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten)
      .ok ⟨disk.segCap, disk.segCap_pos, crashedSegs, none⟩
    else .error .invalidTornSpec
  | .recover =>
    match disk.mem with
    | some _ => .error (.host .up)
    | none =>
      match decodeDurableRecords codec rs with
      | none => .error (.host .corrupt)
      | some (journal, _) =>
        match replay L base sp au k J₀ journal with
        | some J => .ok ⟨disk.segCap, disk.segCap_pos, split disk.segCap disk.segCap_pos (encodeAll Hb rs), some J⟩
        | none => .error (.host .corrupt)

/-- Forward simulation relation coupling `SegmentedDState` on disk to `Obend.Run.Durable.DState`. -/
def SegmentedSimInv (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀)
    (s : DState L S Hole A P Cred Cand Fact Ob i₀) : Prop :=
  ∃ committedRecords : List Record,
    Linked Hb genesisSentinel committedRecords ∧
    (∀ r ∈ committedRecords, r.WF Hb) ∧
    (∃ tail : Bytes,
      disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb committedRecords ++ tail) ∧
      (tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel committedRecords)) tail = .error d) ∧
      (disk.mem.isSome = true → tail = [])) ∧
    decodeDurableRecords codec committedRecords = some (s.journal, s.outbox) ∧
    disk.mem = s.mem ∧ HReachable L base sp au k J₀ s

theorem segmentedSimInv_init (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedSimInv L base sp au k Hb codec J₀ (SegmentedDState.init L segCap hCap J₀) (DState.init L J₀) :=
  ⟨[], trivial, by simp, ⟨[], by simp [SegmentedDState.init, split, encodeAll], .inl rfl, fun _ => rfl⟩,
    rfl, by rfl, .init⟩

omit [DecidableEq ι] [DecidableEq Ix] [(i : Ix) → DecidableEq (Hole i)]
  [DecidableEq Tok] [DecidableEq Cand] [DecidableEq ((i : Ix) × S.Op i)] in
theorem segmented_parseFrom_rs {L : Ledger ι W Tok}
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀} {rs : List Record} {tail : Bytes}
    {journal : List (JEv L S Hole A P Cred Cand Fact)} {outbox : List Nat}
    (hLinked : Linked Hb genesisSentinel rs) (hWf : ∀ r ∈ rs, r.WF Hb)
    (hSegs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ tail))
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d)
    (hDec : decodeDurableRecords codec rs = some (journal, outbox)) :
    (parseFrom Hb genesisSentinel disk.segments.flatten).1 = rs ∧
    recoverJournalAndOutbox Hb codec disk = some (journal, outbox) := by
  have hp1 : (parseFrom Hb genesisSentinel disk.segments.flatten).1 = rs := by
    rw [hSegs, split_join]; exact parseFrom_committed_with_rejected_tail Hb rs hLinked hWf tail hRej
  exact ⟨hp1, by unfold recoverJournalAndOutbox; rw [hp1]; exact hDec⟩

omit [DecidableEq ι] [DecidableEq Ix] [(i : Ix) → DecidableEq (Hole i)]
  [DecidableEq Tok] [DecidableEq Cand] [DecidableEq ((i : Ix) × S.Op i)] in
theorem segmented_clean_tail_flatten {L : Ledger ι W Tok} (Hb : Bytes → Bytes)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀} {rs : List Record} {tail : Bytes}
    (hLinked : Linked Hb genesisSentinel rs) (hWf : ∀ r ∈ rs, r.WF Hb)
    (hSegs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ tail))
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d)
    (hEmpty : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty = true) :
    disk.segments.flatten = encodeAll Hb rs := by
  have hflat : disk.segments.flatten = encodeAll Hb rs ++ tail := by rw [hSegs, split_join]
  rw [hflat, Obend.Vault.Log.parseFrom_encodeAll Hb rs genesisSentinel hLinked hWf tail] at hEmpty
  rcases hRej with rfl | ⟨d, hd⟩
  · simpa using hflat
  · by_cases hne : tail = []
    · subst hne; simpa using hflat
    · rw [Obend.Vault.Log.parseFrom_error Hb hne hd] at hEmpty
      exact absurd (List.isEmpty_iff.mp hEmpty) hne

/-- **Forward Simulation Step**: every accepted `segmentedStep` refines `Durable.hstep`. -/
theorem segmentedStep_refines_durable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk disk' : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (hev : SegmentedHEvent L S Hole A P Cred Cand Fact)
    (hSim : SegmentedSimInv L base sp au k Hb codec J₀ disk s)
    (hStep : segmentedStep L base sp au k Hb codec J₀ disk hev = .ok disk') :
    ∃ s', hstep L base sp au k J₀ s hev.toAbstract = .ok s' ∧
      SegmentedSimInv L base sp au k Hb codec J₀ disk' s' := by
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, hClean⟩, hDec, hMem, hReach⟩
  have ⟨hp_rs, _⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  cases hev with
  | submit ev =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases htail_emp : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty with
    | false => simp [htail_emp] at hStep
    | true =>
      simp only [htail_emp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      have hflat_clean := segmented_clean_tail_flatten Hb hLinked hWf hSegs hRej htail_emp
      cases hmem : disk.mem with
      | none => rw [hmem] at hStep; cases hStep
      | some J =>
        rw [hmem] at hStep; dsimp only at hStep; split at hStep
        · rename_i hlen
          cases hj : jrun L base sp au k J ev with
          | error r => rw [hj] at hStep; cases hStep
          | ok J' =>
            rw [hj] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep
            have hs_mem : s.mem = some J := hMem.symm.trans hmem
            have hhstep : hstep L base sp au k J₀ s (.submit ev) =
                .ok ⟨s.journal ++ [ev], s.outbox, some J'⟩ := by unfold hstep; simp [hs_mem, hj]
            refine ⟨⟨s.journal ++ [ev], s.outbox, some J'⟩, hhstep, ?_⟩
            let prev := lastHash Hb genesisSentinel rs
            let payload := encodeDiskEntry codec (.journalAppend ev)
            let newRec := mkChainedRecord Hb prev payload
            have hrec_wf : newRec.WF Hb :=
              mkChainedRecord_wf Hb (Obend.Vault.Log.lastHash_lt Hb (by decide) rs) hlen
            refine ⟨rs ++ [newRec],
              (Obend.Vault.Log.Linked_append Hb genesisSentinel rs [newRec]).mpr ⟨hLinked, rfl, trivial⟩,
              fun r hr => ?_, ⟨[], ?_, .inl rfl, fun _ => rfl⟩, ?_, rfl, .step (.submit ev) hReach hhstep⟩
            · rcases List.mem_append.mp hr with hr | hr
              · exact hWf r hr
              · simp only [List.mem_singleton] at hr; subst hr; exact hrec_wf
            · simp only [appendSegmentedBytes, hflat_clean, Obend.Vault.Log.encodeAll_append,
                encodeAll, List.append_nil]; rfl
            · unfold decodeDurableRecords
              rw [foldDiskEntries_snoc codec rs newRec [] [] s.journal s.outbox hDec]
              simp [newRec, mkChainedRecord, payload]
        · cases hStep
  | expose n =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases htail_emp : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty with
    | false => simp [htail_emp] at hStep
    | true =>
      simp only [htail_emp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      have hflat_clean := segmented_clean_tail_flatten Hb hLinked hWf hSegs hRej htail_emp
      rw [hDec] at hStep; dsimp only at hStep; split at hStep
      · rename_i i o hjn
        split at hStep
        · cases hStep
        · rename_i hnot_out
          split at hStep
          · rename_i hlen
            simp only [Except.ok.injEq] at hStep; subst hStep
            have hhstep : hstep L base sp au k J₀ s (.expose n) =
                .ok ⟨s.journal, s.outbox ++ [n], disk.mem⟩ := by
              unfold hstep; simp [hjn, hnot_out, hMem]
            refine ⟨⟨s.journal, s.outbox ++ [n], disk.mem⟩, hhstep, ?_⟩
            let prev := lastHash Hb genesisSentinel rs
            let payload := encodeDiskEntry codec (.outboxExpose n)
            let newRec := mkChainedRecord Hb prev payload
            have hrec_wf : newRec.WF Hb :=
              mkChainedRecord_wf Hb (Obend.Vault.Log.lastHash_lt Hb (by decide) rs) hlen
            refine ⟨rs ++ [newRec],
              (Obend.Vault.Log.Linked_append Hb genesisSentinel rs [newRec]).mpr ⟨hLinked, rfl, trivial⟩,
              fun r hr => ?_, ⟨[], ?_, .inl rfl, fun _ => rfl⟩, ?_, rfl, .step (.expose n) hReach hhstep⟩
            · rcases List.mem_append.mp hr with hr | hr
              · exact hWf r hr
              · simp only [List.mem_singleton] at hr; subst hr; exact hrec_wf
            · simp only [appendSegmentedBytes, hflat_clean, Obend.Vault.Log.encodeAll_append,
                encodeAll, List.append_nil]; rfl
            · unfold decodeDurableRecords
              rw [foldDiskEntries_snoc codec rs newRec [] [] s.journal s.outbox hDec]
              simp [newRec, mkChainedRecord, payload]
          · cases hStep
      · cases hStep
  | cleanCrash =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract, Except.ok.injEq] at hStep ⊢; subst hStep
    have hhstep : hstep L base sp au k J₀ s .crash = .ok ⟨s.journal, s.outbox, none⟩ := rfl
    exact ⟨⟨s.journal, s.outbox, none⟩, hhstep,
      ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, fun h => by simp at h⟩,
        hDec, rfl, .step .crash hReach hhstep⟩⟩
  | tornCrash r_in bytesWritten =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    split at hStep
    · rename_i hspec
      simp only [Except.ok.injEq] at hStep; subst hStep
      obtain ⟨h0, h1, h2, h3, h4, hk_lt⟩ := hspec
      have hwf_in : r_in.WF Hb := ⟨h0, h1, h2, h3, h4⟩
      have hhstep : hstep L base sp au k J₀ s .crash = .ok ⟨s.journal, s.outbox, none⟩ := rfl
      have hrej' : (encodeRecord Hb r_in).take bytesWritten = [] ∨
          ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs))
            ((encodeRecord Hb r_in).take bytesWritten) = .error d := by
        by_cases hb0 : bytesWritten = 0
        · subst hb0; exact .inl (by simp)
        · exact .inr ⟨.torn, Obend.Vault.Log.parseOne_torn Hb hwf_in
            (List.take_append_drop bytesWritten _) (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩
      exact ⟨⟨s.journal, s.outbox, none⟩, hhstep,
        ⟨rs, hLinked, hWf, ⟨(encodeRecord Hb r_in).take bytesWritten, rfl, hrej', fun h => by simp at h⟩,
          hDec, rfl, .step .crash hReach hhstep⟩⟩
    · cases hStep
  | recover =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases hmem : disk.mem with
    | some _ => rw [hmem] at hStep; cases hStep
    | none =>
      rw [hmem, hDec] at hStep; dsimp only at hStep
      cases hrep : replay L base sp au k J₀ s.journal with
      | none => rw [hrep] at hStep; cases hStep
      | some J =>
        rw [hrep] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep
        have hs_mem : s.mem = none := hMem.symm.trans hmem
        have hhstep : hstep L base sp au k J₀ s .recover = .ok ⟨s.journal, s.outbox, some J⟩ := by
          unfold hstep; simp [hs_mem, hrep]
        exact ⟨⟨s.journal, s.outbox, some J⟩, hhstep,
          ⟨rs, hLinked, hWf, ⟨[], by simp, .inl rfl, fun _ => rfl⟩,
            hDec, rfl, .step .recover hReach hhstep⟩⟩

/-- Multi-step segmented trace execution (keeping state on refused steps). -/
def runSegmentedTrace (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ →
    List (SegmentedHEvent L S Hole A P Cred Cand Fact) → SegmentedDState L S Hole A P Cand Fact Ob i₀
  | disk, [] => disk
  | disk, e :: es =>
    match segmentedStep L base sp au k Hb codec J₀ disk e with
    | .ok disk' => runSegmentedTrace L base sp au k Hb codec J₀ disk' es
    | .error _ => runSegmentedTrace L base sp au k Hb codec J₀ disk es

/-- Reachable physical segmented states from `SegmentedDState.init`. -/
inductive SegmentedReachable (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ → Prop
  | init : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ (SegmentedDState.init L segCap hCap J₀)
  | step {d d' : SegmentedDState L S Hole A P Cand Fact Ob i₀}
      (hev : SegmentedHEvent L S Hole A P Cred Cand Fact) :
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀ d →
      segmentedStep L base sp au k Hb codec J₀ d hev = .ok d' →
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀ d'

theorem runSegmentedTrace_reachable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ disk) :
    ∀ (es : List (SegmentedHEvent L S Hole A P Cred Cand Fact)),
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀
        (runSegmentedTrace L base sp au k Hb codec J₀ disk es)
  | [] => hReach
  | e :: es => by
    simp only [runSegmentedTrace]
    cases hs : segmentedStep L base sp au k Hb codec J₀ disk e with
    | ok disk' => exact runSegmentedTrace_reachable L base sp au k Hb codec segCap hCap J₀ (.step e hReach hs) es
    | error _ => exact runSegmentedTrace_reachable L base sp au k Hb codec segCap hCap J₀ hReach es

theorem segmentedReachable_simulates_durable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ disk) :
    ∃ s, SegmentedSimInv L base sp au k Hb codec J₀ disk s := by
  induction hReach with
  | init => exact ⟨DState.init L J₀, segmentedSimInv_init L base sp au k Hb codec segCap hCap J₀⟩
  | step hev _ hs ih =>
    obtain ⟨s, hSim⟩ := ih
    obtain ⟨s', _, hSim'⟩ := segmentedStep_refines_durable L base sp au k Hb codec J₀ hev hSim hs
    exact ⟨s', hSim'⟩

/-- **Torn-Tail Crash Recovery Idempotence**: `.tornCrash` followed by `.recover` restores `disk`. -/
theorem segmented_torn_crash_recover_idempotent
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    {s : DState L S Hole A P Cred Cand Fact Ob i₀} {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (hSim : SegmentedSimInv L base sp au k Hb codec J₀ disk s) (hUp : disk.mem = some J)
    (r_in : Record) (hwf_in : r_in.WF Hb)
    (bytesWritten : Nat) (hk : bytesWritten < (encodeRecord Hb r_in).length) :
    ∃ crashed recovered,
      segmentedStep L base sp au k Hb codec J₀ disk (.tornCrash r_in bytesWritten) = .ok crashed ∧
      segmentedStep L base sp au k Hb codec J₀ crashed .recover = .ok recovered ∧
      recovered = disk ∧
      recoverJournalAndOutbox Hb codec recovered = some (s.journal, s.outbox) := by
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, hClean⟩, hDec, hMem, hReach⟩
  have ⟨hp_rs, hrec_jo⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  obtain ⟨h0, h1, h2, h3, h4⟩ := hwf_in
  have hcrash : segmentedStep L base sp au k Hb codec J₀ disk (.tornCrash r_in bytesWritten) =
      .ok ⟨disk.segCap, disk.segCap_pos,
        split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten),
        none⟩ := by
    unfold segmentedStep; dsimp only; rw [hp_rs]
    split
    · rfl
    · rename_i hneg; exact absurd ⟨h0, h1, h2, h3, h4, hk⟩ hneg
  obtain ⟨J', hrep, _, hm_inv⟩ := (hreach_inv hReach).replays
  have hs_mem : s.mem = some J := hMem.symm.trans hUp
  have hJ_eq : J' = J := by
    rcases hm_inv with hm_inv | hm_inv <;> rw [hm_inv] at hs_mem <;> cases hs_mem; rfl
  subst hJ_eq
  have htail_nil : tail = [] := hClean (by simp [hUp])
  subst htail_nil
  have hdisk_segs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs) := by
    simpa using hSegs
  have hrec : segmentedStep L base sp au k Hb codec J₀
      ⟨disk.segCap, disk.segCap_pos,
        split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten),
        none⟩ .recover = .ok disk := by
    unfold segmentedStep; dsimp only
    rw [parseFrom_committed_with_torn_frame Hb disk.segCap disk.segCap_pos
      rs hLinked hWf r_in ⟨h0, h1, h2, h3, h4⟩ bytesWritten hk, hDec]
    dsimp only; rw [hrep]
    cases disk with
    | mk sc scp segs m => dsimp only at hUp hdisk_segs ⊢; subst hUp; rw [← hdisk_segs]
  exact ⟨_, disk, hcrash, hrec, rfl, hrec_jo⟩

/-- **Keystone Chasm 3A Theorem (`segmented_exposed_once`)**: across arbitrary multi-segment
    rotations and torn-tail crash-restart cycles, each linear token `t` is exposed at most once. -/
theorem segmented_exposed_once
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap)
    {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
    {stored₀ : ι → (j : Ix) → Hole j → Option Cand}
    (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap (JCfg.init L d₀ O stored₀) disk)
    {journal : List (JEv L S Hole A P Cred Cand Fact)} {outbox : List Nat}
    (hDisk : recoverJournalAndOutbox Hb codec disk = some (journal, outbox))
    {n m : Nat} (hn : n ∈ outbox) (hm : m ∈ outbox)
    {i j : ι} {o o' : Σ i, S.Op i} {t : Tok}
    (hio : journal[n]? = some (.dispatch i o)) (hjo : journal[m]? = some (.dispatch j o'))
    (ht : (sp i).consumes o.2 = some t) (ht' : (sp j).consumes o'.2 = some t) :
    n = m ∧ i = j := by
  obtain ⟨s, hSim⟩ := segmentedReachable_simulates_durable L base sp au k Hb codec segCap hCap
    (JCfg.init L d₀ O stored₀) hReach
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, _⟩, hDec, _, hAbsReach⟩
  have ⟨_, hrec⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  rw [hrec] at hDisk; simp only [Option.some.injEq, Prod.mk.injEq] at hDisk
  obtain ⟨rfl, rfl⟩ := hDisk
  exact exposed_once hs₀ hg₀ hAbsReach hn hm hio hjo ht ht'

end Simulation

/-! ## Part B.2 — Linear Capability-Carrying Plans (`TVal`, `DataWire`, `CapTable`, `CapSealFrame`) -/

/-- Live runtime transferable value (`Core.Data` extended with linear `.cap slotId custodyId`). -/
inductive TVal where
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | record (fields : List (String × TVal))
  | variant (tag : String) (payload : TVal)
  | cap (slotId : Nat) (custodyId : Nat)
  deriving Repr

mutual
def tvalBeq : TVal → TVal → Bool
  | .natural a, .natural b => a == b
  | .boolean a, .boolean b => a == b
  | .label a, .label b => a == b
  | .record fa, .record fb => tvalFieldsBeq fa fb
  | .variant ta pa, .variant tb pb => ta == tb && tvalBeq pa pb
  | .cap sa ca, .cap sb cb => sa == sb && ca == cb
  | _, _ => false

def tvalFieldsBeq : List (String × TVal) → List (String × TVal) → Bool
  | [], [] => true
  | (ka, va) :: ra, (kb, vb) :: rb => ka == kb && tvalBeq va vb && tvalFieldsBeq ra rb
  | _, _ => false
end

instance : BEq TVal := ⟨tvalBeq⟩

mutual
def tvalOfData : Data → TVal
  | .natural n => .natural n
  | .boolean b => .boolean b
  | .label s => .label s
  | .record fs => .record (tvalOfDataFields fs)
  | .variant tag p => .variant tag (tvalOfData p)

def tvalOfDataFields : List (String × Data) → List (String × TVal)
  | [] => []
  | (k, v) :: rest => (k, tvalOfData v) :: tvalOfDataFields rest
end

/-- Embed pure `Obend.Core.Data.Data` into `TVal`. -/
@[expose] def TVal.ofData (d : Data) : TVal := tvalOfData d

mutual
def tvalCapSlots : TVal → List Nat
  | .natural _ | .boolean _ | .label _ => []
  | .cap slotId _ => [slotId]
  | .variant _ p => tvalCapSlots p
  | .record fs => tvalCapSlotsFields fs

def tvalCapSlotsFields : List (String × TVal) → List Nat
  | [] => []
  | (_, v) :: rest => tvalCapSlots v ++ tvalCapSlotsFields rest
end

/-- Collect all capability `slotId`s referenced in `v` in left-to-right order. -/
@[expose] def TVal.capSlots (v : TVal) : List Nat := tvalCapSlots v

mutual
def tvalConforms : TVal → Ty → Bool
  | .natural _, .natural | .boolean _, .boolean | .label _, .label => true
  | .cap _ cid, .custody expectedId => cid == expectedId
  | .record fields, row =>
    fields.length == (Obend.Core.Data.rowNames row).length &&
    (fields.map Prod.fst).eraseDups.length == fields.length &&
    tvalConformsFields fields row
  | .variant tag payload, .variant row =>
    match Obend.Core.Data.rowMember row tag with
    | some member => tvalConforms payload member
    | none => false
  | _, _ => false

def tvalConformsFields : List (String × TVal) → Ty → Bool
  | [], _ => true
  | (name, val) :: rest, row =>
    (match Obend.Core.Data.rowMember row name with
      | some member => tvalConforms val member
      | none => false) && tvalConformsFields rest row
end

/-- Type conformance of a `TVal` against a `Ty.isTransferable` type. -/
@[expose] def TVal.conforms (v : TVal) (ty : Ty) : Bool := tvalConforms v ty

/-- Dehydrated wire skeleton: capability leaves replaced by descriptor indices into `CapTable`. -/
inductive DataWire where
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | record (fields : List (String × DataWire))
  | variant (tag : String) (payload : DataWire)
  | sealedCap (capIndex : Nat) (custodyId : Nat)
  deriving Repr

mutual
def dataWireBeq : DataWire → DataWire → Bool
  | .natural a, .natural b => a == b
  | .boolean a, .boolean b => a == b
  | .label a, .label b => a == b
  | .record fa, .record fb => dataWireFieldsBeq fa fb
  | .variant ta pa, .variant tb pb => ta == tb && dataWireBeq pa pb
  | .sealedCap ia ca, .sealedCap ib cb => ia == ib && ca == cb
  | _, _ => false

def dataWireFieldsBeq : List (String × DataWire) → List (String × DataWire) → Bool
  | [], [] => true
  | (ka, va) :: ra, (kb, vb) :: rb => ka == kb && dataWireBeq va vb && dataWireFieldsBeq ra rb
  | _, _ => false
end

instance : BEq DataWire := ⟨dataWireBeq⟩

mutual
def dataWireToData : DataWire → Data
  | .natural n => .variant "wire.nat" (.natural n)
  | .boolean b => .variant "wire.bool" (.boolean b)
  | .label s => .variant "wire.label" (.label s)
  | .record fs => .variant "wire.rec" (.record (dataWireFieldsToData fs))
  | .variant tag p => .variant "wire.var" (.record [("tag", .label tag), ("payload", dataWireToData p)])
  | .sealedCap idx cid => .variant "wire.cap" (.record [("idx", .natural idx), ("cid", .natural cid)])

def dataWireFieldsToData : List (String × DataWire) → List (String × Data)
  | [] => []
  | (k, v) :: rest => (k, dataWireToData v) :: dataWireFieldsToData rest
end

/-- Lower `DataWire` bijectively to pure first-order `Obend.Core.Data.Data`. -/
@[expose] def DataWire.toData (w : DataWire) : Data := dataWireToData w

mutual
def dataWireOfData? : Data → Option DataWire
  | .variant "wire.nat" (.natural n) => some (.natural n)
  | .variant "wire.bool" (.boolean b) => some (.boolean b)
  | .variant "wire.label" (.label s) => some (.label s)
  | .variant "wire.rec" (.record fs) => (dataWireFieldsOfData? fs).map .record
  | .variant "wire.var" (.record [("tag", .label tag), ("payload", p)]) =>
    (dataWireOfData? p).map (.variant tag)
  | .variant "wire.cap" (.record [("idx", .natural idx), ("cid", .natural cid)]) =>
    some (.sealedCap idx cid)
  | _ => none

def dataWireFieldsOfData? : List (String × Data) → Option (List (String × DataWire))
  | [] => some []
  | (k, v) :: rest =>
    match dataWireOfData? v, dataWireFieldsOfData? rest with
    | some wv, some wrest => some ((k, wv) :: wrest)
    | _, _ => none
end

/-- Parse pure `Obend.Core.Data.Data` back into `DataWire`. -/
@[expose] def DataWire.ofData? (d : Data) : Option DataWire := dataWireOfData? d

mutual
theorem dataWireOfData_toData : ∀ (w : DataWire), dataWireOfData? (dataWireToData w) = some w
  | .natural _ | .boolean _ | .label _ | .sealedCap _ _ => rfl
  | .record fs => by simp [dataWireToData, dataWireOfData?, dataWireFieldsOfData_toData fs]
  | .variant tag p => by simp [dataWireToData, dataWireOfData?, dataWireOfData_toData p]

theorem dataWireFieldsOfData_toData :
    ∀ (fs : List (String × DataWire)), dataWireFieldsOfData? (dataWireFieldsToData fs) = some fs
  | [] => rfl
  | (k, v) :: rest => by
    simp [dataWireFieldsToData, dataWireFieldsOfData?,
      dataWireOfData_toData v, dataWireFieldsOfData_toData rest]
end

/-- Bijective round-trip of `DataWire` through pure `Obend.Core.Data.Data`. -/
theorem DataWire.ofData_toData (w : DataWire) : DataWire.ofData? w.toData = some w :=
  dataWireOfData_toData w

/-- Live unforgeable linear capability token held in a `CustodyEnv`. -/
structure CapToken where
  slotId : Nat
  custodyId : Nat
  badge : Bytes
  deriving DecidableEq, Repr

/-- Linear custody environment owning live capability tokens. -/
structure CustodyEnv where
  tokens : List CapToken
  deriving DecidableEq, Repr

/-- One sealed entry inside a `CapTable`. -/
structure SealedCapEntry where
  index : Nat
  token : CapToken
  deriving DecidableEq, Repr

/-- Linear Capability Export/Import Table indexing extracted capabilities `0 .. n-1`. -/
structure CapTable where
  entries : List SealedCapEntry
  deriving DecidableEq, Repr

/-- Serialize `(nonce, tbl)` to canonical bytes for 256-bit `Hb` frame sealing. -/
def encodeCapTableBytes (nonce : Nat) (tbl : CapTable) : Bytes :=
  be 8 nonce ++ (tbl.entries.flatMap fun e =>
    be 4 e.index ++ be 8 e.token.slotId ++ be 8 e.token.custodyId ++
      be 4 e.token.badge.length ++ e.token.badge)

/-- Compute the 32-byte (256-bit) frame seal over `(nonce, tbl)` via `Hb`. -/
def computeCapFrameSeal (Hb : Bytes → Bytes) (nonce : Nat) (tbl : CapTable) : Bytes :=
  be 32 (dig Hb (encodeCapTableBytes nonce tbl))

/-- Sealed capability table frame crossing `.perform` alongside `DataWire`. -/
structure CapSealFrame where
  nonce : Nat
  table : CapTable
  sealBytes : Bytes
  deriving DecidableEq, Repr

/-- Verify `frame.sealBytes` against the 256-bit `Hb` commitment to `(frame.nonce, frame.table)`. -/
@[expose] def CapSealFrame.sealValid (Hb : Bytes → Bytes) (frame : CapSealFrame) : Bool :=
  frame.sealBytes == computeCapFrameSeal Hb frame.nonce frame.table

/-- Check consecutive 0-based indices starting at `start`. -/
@[expose] def indexedFromBool (start : Nat) : List SealedCapEntry → Bool
  | [] => true
  | e :: es => (e.index == start) && indexedFromBool (start + 1) es

/-- Deterministic refusals of `dehydrate` / `rehydrate`. -/
inductive TransferRefusal where
  | missingOrDuplicateSlot (slotId : Nat)
  | custodyIdMismatch (idOrIdx expected actual : Nat)
  | droppedCustody (slotId : Nat)
  | unsealedFrame
  | malformedCapTable
  | forgedCapIndex (capIndex : Nat)
  | duplicateCapIndex (capIndex : Nat)
  | droppedSealedCap (capIndex : Nat)
  deriving DecidableEq, Repr

/-- Linearly extract and remove the first `CapToken` with `slotId` from `ts`. -/
def takeCapAtSlot (slotId : Nat) : List CapToken → Option (CapToken × List CapToken)
  | [] => none
  | t :: ts =>
    if t.slotId == slotId then some (t, ts)
    else (takeCapAtSlot slotId ts).map fun (found, rest) => (found, t :: rest)

theorem takeCapAtSlot_spec {slotId : Nat} {ts rest : List CapToken} {found : CapToken}
    (h : takeCapAtSlot slotId ts = some (found, rest)) :
    found.slotId = slotId ∧ ts.Perm (found :: rest) := by
  induction ts generalizing rest found with
  | nil => cases h
  | cons t ts ih =>
    simp only [takeCapAtSlot] at h; split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨beq_iff_eq.mp heq, List.Perm.refl _⟩
    · cases hrec : takeCapAtSlot slotId ts with
      | none => rw [hrec] at h; cases h
      | some pair =>
        obtain ⟨f', r'⟩ := pair; rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hid, hp⟩ := ih hrec
        exact ⟨hid, (hp.cons t).trans (List.Perm.swap f' t r')⟩

/-- Linearly extract and remove the `SealedCapEntry` at `capIndex` from `es`. -/
def takeSealedAtIndex (capIndex : Nat) : List SealedCapEntry → Option (SealedCapEntry × List SealedCapEntry)
  | [] => none
  | e :: es =>
    if e.index == capIndex then some (e, es)
    else (takeSealedAtIndex capIndex es).map fun (found, rest) => (found, e :: rest)

theorem takeSealedAtIndex_perm {capIndex : Nat} {es rest : List SealedCapEntry} {found : SealedCapEntry}
    (h : takeSealedAtIndex capIndex es = some (found, rest)) :
    found.index = capIndex ∧ es.Perm (found :: rest) := by
  induction es generalizing rest found with
  | nil => cases h
  | cons e es ih =>
    simp only [takeSealedAtIndex] at h; split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨beq_iff_eq.mp heq, List.Perm.refl _⟩
    · cases hrec : takeSealedAtIndex capIndex es with
      | none => rw [hrec] at h; cases h
      | some pair =>
        obtain ⟨f', r'⟩ := pair; rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hid, hp⟩ := ih hrec
        exact ⟨hid, (hp.cons e).trans (List.Perm.swap f' e r')⟩

mutual
def dehydrateVal (nextIdx : Nat) :
    TVal → List CapToken → Except TransferRefusal (DataWire × List CapToken × List SealedCapEntry)
  | .natural n, rem => .ok (.natural n, rem, [])
  | .boolean b, rem => .ok (.boolean b, rem, [])
  | .label s, rem => .ok (.label s, rem, [])
  | .cap slotId custodyId, rem =>
    match takeCapAtSlot slotId rem with
    | none => .error (.missingOrDuplicateSlot slotId)
    | some (tok, rem') =>
      if tok.custodyId == custodyId then .ok (.sealedCap nextIdx custodyId, rem', [⟨nextIdx, tok⟩])
      else .error (.custodyIdMismatch slotId custodyId tok.custodyId)
  | .variant tag p, rem =>
    match dehydrateVal nextIdx p rem with
    | .ok (wp, rem', ep) => .ok (.variant tag wp, rem', ep)
    | .error e => .error e
  | .record fs, rem =>
    match dehydrateFields nextIdx fs rem with
    | .ok (wfs, rem', efs) => .ok (.record wfs, rem', efs)
    | .error e => .error e

def dehydrateFields (nextIdx : Nat) :
    List (String × TVal) → List CapToken →
      Except TransferRefusal (List (String × DataWire) × List CapToken × List SealedCapEntry)
  | [], rem => .ok ([], rem, [])
  | (k, v) :: rest, rem =>
    match dehydrateVal nextIdx v rem with
    | .error e => .error e
    | .ok (wv, rem₁, e₁) =>
      match dehydrateFields (nextIdx + e₁.length) rest rem₁ with
      | .error e => .error e
      | .ok (wrest, rem₂, e₂) => .ok ((k, wv) :: wrest, rem₂, e₁ ++ e₂)
end

/-- **Dehydrate on `.perform` yield**: extracts linear capabilities into `(DataWire, CapSealFrame)`. -/
def dehydrate (Hb : Bytes → Bytes) (nonce : Nat) (env : CustodyEnv) (v : TVal) :
    Except TransferRefusal (DataWire × CapSealFrame) :=
  match dehydrateVal 0 v env.tokens with
  | .error e => .error e
  | .ok (wire, [], entries) =>
    let tbl : CapTable := ⟨entries⟩
    .ok (wire, ⟨nonce, tbl, computeCapFrameSeal Hb nonce tbl⟩)
  | .ok (_, leftover :: _, _) => .error (.droppedCustody leftover.slotId)

mutual
def rehydrateVal (boundLen : Nat) :
    DataWire → List SealedCapEntry → Except TransferRefusal (TVal × List SealedCapEntry × List CapToken)
  | .natural n, avail => .ok (.natural n, avail, [])
  | .boolean b, avail => .ok (.boolean b, avail, [])
  | .label s, avail => .ok (.label s, avail, [])
  | .sealedCap idx custodyId, avail =>
    if idx ≥ boundLen then .error (.forgedCapIndex idx) else
    match takeSealedAtIndex idx avail with
    | none => .error (.duplicateCapIndex idx)
    | some (entry, avail') =>
      if entry.token.custodyId == custodyId then
        .ok (.cap entry.token.slotId custodyId, avail', [entry.token])
      else .error (.custodyIdMismatch idx custodyId entry.token.custodyId)
  | .variant tag wp, avail =>
    match rehydrateVal boundLen wp avail with
    | .ok (p, avail', toks) => .ok (.variant tag p, avail', toks)
    | .error e => .error e
  | .record wfs, avail =>
    match rehydrateFields boundLen wfs avail with
    | .ok (fs, avail', toks) => .ok (.record fs, avail', toks)
    | .error e => .error e

def rehydrateFields (boundLen : Nat) :
    List (String × DataWire) → List SealedCapEntry →
      Except TransferRefusal (List (String × TVal) × List SealedCapEntry × List CapToken)
  | [], avail => .ok ([], avail, [])
  | (k, wv) :: wrest, avail =>
    match rehydrateVal boundLen wv avail with
    | .error e => .error e
    | .ok (v, avail₁, t₁) =>
      match rehydrateFields boundLen wrest avail₁ with
      | .error e => .error e
      | .ok (rest, avail₂, t₂) => .ok ((k, v) :: rest, avail₂, t₁ ++ t₂)
end

/-- **Rehydrate on `.perform` resume**: verifies seal, reconstructs `(TVal, CustodyEnv)` linearly. -/
def rehydrate (Hb : Bytes → Bytes) (wire : DataWire) (frame : CapSealFrame) :
    Except TransferRefusal (TVal × CustodyEnv) :=
  if !frame.sealValid Hb then .error .unsealedFrame
  else if !indexedFromBool 0 frame.table.entries then .error .malformedCapTable
  else
    match rehydrateVal frame.table.entries.length wire frame.table.entries with
    | .error e => .error e
    | .ok (v, [], imported) => .ok (v, ⟨imported⟩)
    | .ok (_, leftover :: _, _) => .error (.droppedSealedCap leftover.index)

/-! ### Round-Trip & Strict Linear Custody Conservation Proofs -/

theorem indexedFromBool_append :
    ∀ (e₁ e₂ : List SealedCapEntry) (start : Nat),
      indexedFromBool start e₁ = true → indexedFromBool (start + e₁.length) e₂ = true →
      indexedFromBool start (e₁ ++ e₂) = true
  | [], e₂, start, _, h₂ => by simpa using h₂
  | x :: xs, e₂, start, h₁, h₂ => by
    simp only [indexedFromBool, List.cons_append, Bool.and_eq_true] at h₁ ⊢
    have hlen : start + (x :: xs).length = (start + 1) + xs.length := by simp [List.length_cons]; omega
    rw [hlen] at h₂; exact ⟨h₁.1, indexedFromBool_append xs e₂ (start + 1) h₁.2 h₂⟩

mutual
theorem dehydrateVal_spec :
    ∀ (v : TVal) (nextIdx : Nat) (rem rem' : List CapToken) (wire : DataWire)
      (entries : List SealedCapEntry),
      dehydrateVal nextIdx v rem = .ok (wire, rem', entries) →
      indexedFromBool nextIdx entries = true ∧
      rem.Perm (entries.map SealedCapEntry.token ++ rem') ∧
      entries.map (fun e => e.token.slotId) = tvalCapSlots v ∧
      ∀ (boundLen : Nat) (tailAvail : List SealedCapEntry),
        nextIdx + entries.length ≤ boundLen →
        rehydrateVal boundLen wire (entries ++ tailAvail) =
          .ok (v, tailAvail, entries.map SealedCapEntry.token)
  | .natural _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .boolean _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .label _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .cap slotId custodyId, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases ht : takeCapAtSlot slotId rem with
    | none => rw [ht] at h; cases h
    | some pair =>
      obtain ⟨tok, r₁⟩ := pair; rw [ht] at h; dsimp only at h; split at h
      · rename_i hcid
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hslot, hperm⟩ := takeCapAtSlot_spec ht
        refine ⟨by simp [indexedFromBool], hperm, by simp [tvalCapSlots, hslot], ?_⟩
        intro boundLen tailAvail hle; simp only [List.length_singleton] at hle
        have hnot_ge : ¬ (nextIdx ≥ boundLen) := by omega
        simp [rehydrateVal, hnot_ge, takeSealedAtIndex, hcid, hslot]
      · cases h
  | .variant tag p, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases hd : dehydrateVal nextIdx p rem with
    | error e => rw [hd] at h; cases h
    | ok res =>
      obtain ⟨wp, r₁, ep⟩ := res; rw [hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hind, hperm, hslots, hrehyd⟩ := dehydrateVal_spec p nextIdx rem r₁ wp ep hd
      refine ⟨hind, hperm, by simpa [tvalCapSlots] using hslots, ?_⟩
      intro boundLen tailAvail hle; simp [rehydrateVal, hrehyd boundLen tailAvail hle]
  | .record fs, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases hd : dehydrateFields nextIdx fs rem with
    | error e => rw [hd] at h; cases h
    | ok res =>
      obtain ⟨wfs, r₁, efs⟩ := res; rw [hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hind, hperm, hslots, hrehyd⟩ := dehydrateFields_spec fs nextIdx rem r₁ wfs efs hd
      refine ⟨hind, hperm, by simpa [tvalCapSlots] using hslots, ?_⟩
      intro boundLen tailAvail hle; simp [rehydrateVal, hrehyd boundLen tailAvail hle]

theorem dehydrateFields_spec :
    ∀ (fs : List (String × TVal)) (nextIdx : Nat) (rem rem' : List CapToken)
      (wfs : List (String × DataWire)) (entries : List SealedCapEntry),
      dehydrateFields nextIdx fs rem = .ok (wfs, rem', entries) →
      indexedFromBool nextIdx entries = true ∧
      rem.Perm (entries.map SealedCapEntry.token ++ rem') ∧
      entries.map (fun e => e.token.slotId) = tvalCapSlotsFields fs ∧
      ∀ (boundLen : Nat) (tailAvail : List SealedCapEntry),
        nextIdx + entries.length ≤ boundLen →
        rehydrateFields boundLen wfs (entries ++ tailAvail) =
          .ok (fs, tailAvail, entries.map SealedCapEntry.token)
  | [], _, _, _, _, _, h => by
    simp only [dehydrateFields, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | (k, v) :: rest, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateFields] at h
    cases hd1 : dehydrateVal nextIdx v rem with
    | error e => rw [hd1] at h; cases h
    | ok res1 =>
      obtain ⟨wv, rem₁, e₁⟩ := res1; rw [hd1] at h; dsimp only at h
      cases hd2 : dehydrateFields (nextIdx + e₁.length) rest rem₁ with
      | error e => rw [hd2] at h; cases h
      | ok res2 =>
        obtain ⟨wrest, rem₂, e₂⟩ := res2; rw [hd2] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hi1, hp1, hs1, hr1⟩ := dehydrateVal_spec v nextIdx rem rem₁ wv e₁ hd1
        obtain ⟨hi2, hp2, hs2, hr2⟩ := dehydrateFields_spec rest (nextIdx + e₁.length) rem₁ rem₂ wrest e₂ hd2
        have hperm_all : rem.Perm ((e₁ ++ e₂).map SealedCapEntry.token ++ rem₂) := by
          rw [List.map_append, List.append_assoc]; exact hp1.trans (hp2.append_left _)
        refine ⟨indexedFromBool_append e₁ e₂ nextIdx hi1 hi2, hperm_all, ?_, ?_⟩
        · simp [tvalCapSlotsFields, List.map_append, hs1, hs2]
        · intro boundLen tailAvail hle; rw [List.length_append] at hle; rw [List.append_assoc]
          simp [rehydrateFields, hr1 boundLen (e₂ ++ tailAvail) (by omega),
            hr2 boundLen tailAvail (by omega), List.map_append]
end

mutual
theorem rehydrateVal_perm :
    ∀ (boundLen : Nat) (wire : DataWire) (avail avail' : List SealedCapEntry)
      (v : TVal) (toks : List CapToken),
      rehydrateVal boundLen wire avail = .ok (v, avail', toks) →
      (avail.map SealedCapEntry.token).Perm (toks ++ avail'.map SealedCapEntry.token)
  | _, .natural _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .boolean _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .label _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .sealedCap idx _, avail, _, _, _, h => by
    simp only [rehydrateVal] at h; split at h
    · cases h
    · cases ht : takeSealedAtIndex idx avail with
      | none => rw [ht] at h; cases h
      | some pair =>
        obtain ⟨entry, av₁⟩ := pair; rw [ht] at h; dsimp only at h; split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          simpa using (takeSealedAtIndex_perm ht).2.map SealedCapEntry.token
        · cases h
  | boundLen, .variant _ wp, avail, _, _, _, h => by
    simp only [rehydrateVal] at h
    cases hr : rehydrateVal boundLen wp avail with
    | error e => rw [hr] at h; cases h
    | ok res =>
      obtain ⟨p, av₁, t₁⟩ := res; rw [hr] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact rehydrateVal_perm boundLen wp avail av₁ p t₁ hr
  | boundLen, .record wfs, avail, _, _, _, h => by
    simp only [rehydrateVal] at h
    cases hr : rehydrateFields boundLen wfs avail with
    | error e => rw [hr] at h; cases h
    | ok res =>
      obtain ⟨fs, av₁, t₁⟩ := res; rw [hr] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact rehydrateFields_perm boundLen wfs avail av₁ fs t₁ hr

theorem rehydrateFields_perm :
    ∀ (boundLen : Nat) (wfs : List (String × DataWire)) (avail avail' : List SealedCapEntry)
      (fs : List (String × TVal)) (toks : List CapToken),
      rehydrateFields boundLen wfs avail = .ok (fs, avail', toks) →
      (avail.map SealedCapEntry.token).Perm (toks ++ avail'.map SealedCapEntry.token)
  | _, [], _, _, _, _, h => by
    simp only [rehydrateFields, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | boundLen, (_, wv) :: wrest, avail, _, _, _, h => by
    simp only [rehydrateFields] at h
    cases hr1 : rehydrateVal boundLen wv avail with
    | error e => rw [hr1] at h; cases h
    | ok res1 =>
      obtain ⟨v, av₁, t₁⟩ := res1; rw [hr1] at h; dsimp only at h
      cases hr2 : rehydrateFields boundLen wrest av₁ with
      | error e => rw [hr2] at h; cases h
      | ok res2 =>
        obtain ⟨rest, av₂, t₂⟩ := res2; rw [hr2] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        rw [List.append_assoc]
        exact (rehydrateVal_perm boundLen wv avail av₁ v t₁ hr1).trans
          ((rehydrateFields_perm boundLen wrest av₁ av₂ rest t₂ hr2).append_left t₁)
end

/-- **Keystone Chasm 3B Theorem 1 (`rehydrate_dehydrate_roundtrip`)**: exact round-trip of `v` + custody. -/
theorem rehydrate_dehydrate_roundtrip (Hb : Bytes → Bytes) (nonce : Nat)
    (srcEnv : CustodyEnv) (v : TVal) {wire : DataWire} {frame : CapSealFrame}
    (hDehyd : dehydrate Hb nonce srcEnv v = .ok (wire, frame)) :
    rehydrate Hb wire frame = .ok (v, ⟨frame.table.entries.map SealedCapEntry.token⟩) ∧
    (frame.table.entries.map SealedCapEntry.token).Perm srcEnv.tokens := by
  unfold dehydrate at hDehyd
  cases hd : dehydrateVal 0 v srcEnv.tokens with
  | error e => rw [hd] at hDehyd; cases hDehyd
  | ok res =>
    obtain ⟨w, rem, entries⟩ := res; rw [hd] at hDehyd
    cases rem with
    | cons _ _ => cases hDehyd
    | nil =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hDehyd; obtain ⟨rfl, rfl⟩ := hDehyd
      obtain ⟨hind, hperm, _, hrehyd⟩ := dehydrateVal_spec v 0 srcEnv.tokens [] w entries hd
      rw [List.append_nil] at hperm
      refine ⟨?_, hperm.symm⟩
      unfold rehydrate
      have hseal : (CapSealFrame.mk nonce ⟨entries⟩ (computeCapFrameSeal Hb nonce ⟨entries⟩)).sealValid Hb = true := by
        simp [CapSealFrame.sealValid]
      have hr := hrehyd entries.length [] (by omega); rw [List.append_nil] at hr
      simp [hseal, hind, hr]

/-- **Keystone Chasm 3B Theorem 2 (`transfer_conserves_custody_exact`)**: zero duplication & zero drop. -/
theorem transfer_conserves_custody_exact (Hb : Bytes → Bytes) (nonce : Nat)
    (srcEnv dstEnv : CustodyEnv) (v v' : TVal) (wire wire' : DataWire) (frame : CapSealFrame)
    (hDehyd : dehydrate Hb nonce srcEnv v = .ok (wire, frame))
    (hRehyd : rehydrate Hb wire' frame = .ok (v', dstEnv)) :
    dstEnv.tokens.Perm srcEnv.tokens ∧
    dstEnv.tokens.length = srcEnv.tokens.length ∧
    (∀ tok : CapToken, dstEnv.tokens.count tok = srcEnv.tokens.count tok) ∧
    (srcEnv.tokens.map CapToken.slotId).Perm v.capSlots ∧
    ((srcEnv.tokens.map CapToken.slotId).Nodup → v.capSlots.Nodup) := by
  unfold dehydrate at hDehyd
  cases hd : dehydrateVal 0 v srcEnv.tokens with
  | error e => rw [hd] at hDehyd; cases hDehyd
  | ok res =>
    obtain ⟨w, rem, entries⟩ := res; rw [hd] at hDehyd
    cases rem with
    | cons _ _ => cases hDehyd
    | nil =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hDehyd; obtain ⟨rfl, rfl⟩ := hDehyd
      obtain ⟨_, hperm_src, hslots, _⟩ := dehydrateVal_spec v 0 srcEnv.tokens [] w entries hd
      rw [List.append_nil] at hperm_src
      unfold rehydrate at hRehyd; split at hRehyd
      · cases hRehyd
      · split at hRehyd
        · cases hRehyd
        · cases hr : rehydrateVal entries.length wire' entries with
          | error e => rw [hr] at hRehyd; cases hRehyd
          | ok rres =>
            obtain ⟨vr, availRem, imported⟩ := rres; rw [hr] at hRehyd
            cases availRem with
            | cons _ _ => cases hRehyd
            | nil =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hRehyd; obtain ⟨rfl, rfl⟩ := hRehyd
              have hperm_dst := rehydrateVal_perm entries.length wire' entries [] vr imported hr
              simp only [List.map_nil, List.append_nil] at hperm_dst
              have hperm_both : imported.Perm srcEnv.tokens := hperm_dst.symm.trans hperm_src.symm
              have hslot_perm : (srcEnv.tokens.map CapToken.slotId).Perm v.capSlots := by
                have hp := hperm_src.map CapToken.slotId; rw [List.map_map] at hp
                have hcomp : (CapToken.slotId ∘ SealedCapEntry.token) = (fun e => e.token.slotId) := rfl
                rw [hcomp, hslots] at hp; exact hp
              refine ⟨hperm_both, hperm_both.length_eq, fun tok => hperm_both.count_eq tok,
                hslot_perm, fun hnd => hslot_perm.nodup_iff.mp hnd⟩

/-- Out-of-bounds capability indices `idx ≥ frame.table.entries.length` are deterministically refused. -/
theorem forged_cap_index_refused (Hb : Bytes → Bytes) (frame : CapSealFrame)
    (hSeal : frame.sealValid Hb = true) (hIdx : indexedFromBool 0 frame.table.entries = true)
    (idx custodyId : Nat) (hForged : idx ≥ frame.table.entries.length) :
    rehydrate Hb (.sealedCap idx custodyId) frame = .error (.forgedCapIndex idx) := by
  simp [rehydrate, hSeal, hIdx, rehydrateVal, hForged]

/-- Any `CapSealFrame` failing `sealValid Hb` is deterministically refused with `.unsealedFrame`. -/
theorem unsealed_frame_refused (Hb : Bytes → Bytes) (wire : DataWire) (frame : CapSealFrame)
    (hBad : frame.sealValid Hb = false) :
    rehydrate Hb wire frame = .error .unsealedFrame := by
  simp [rehydrate, hBad]

/-- Referencing the same `slotId` twice in `TVal` is deterministically refused on `dehydrate`. -/
theorem duplicate_cap_slot_refused (Hb : Bytes → Bytes) (nonce slotId cid : Nat) (badge : Bytes) :
    let env : CustodyEnv := ⟨[⟨slotId, cid, badge⟩]⟩
    let dupPlan : TVal := .record [("first", .cap slotId cid), ("second", .cap slotId cid)]
    dehydrate Hb nonce env dupPlan = .error (.missingOrDuplicateSlot slotId) := by
  simp [dehydrate, dehydrateVal, dehydrateFields, takeCapAtSlot]

/-- Leaving an unspent capability in `srcEnv` on `.perform` is refused with `.droppedCustody`. -/
theorem dropped_custody_refused (Hb : Bytes → Bytes) (nonce slotId cid : Nat) (badge : Bytes) :
    let env : CustodyEnv := ⟨[⟨slotId, cid, badge⟩]⟩
    dehydrate Hb nonce env (.natural 7) = .error (.droppedCustody slotId) := by
  simp [dehydrate, dehydrateVal]

/-! ### Inhabited Module Witnesses -/

def sampleIdentityHash (bs : Bytes) : Bytes := bs ++ List.replicate 32 0x5a

def samplePlanVal : TVal :=
  .variant "transferSturdyref"
    (.record [("badgeCap", .cap 10 1), ("coReceipt", .cap 20 2), ("epoch", .natural 9)])

def sampleCustodyEnv : CustodyEnv := ⟨[⟨10, 1, [0xaa, 0xbb]⟩, ⟨20, 2, [0xcc, 0xdd]⟩]⟩

def sampleRoundtripCheck : Bool :=
  match dehydrate sampleIdentityHash 42 sampleCustodyEnv samplePlanVal with
  | .ok (wire, frame) =>
    DataWire.ofData? wire.toData == some wire &&
    frame.sealValid sampleIdentityHash &&
    indexedFromBool 0 frame.table.entries &&
    match rehydrate sampleIdentityHash wire frame with
    | .ok (v', env') => v' == samplePlanVal && env' == sampleCustodyEnv
    | .error _ => false
  | .error _ => false

example : (Ty.variant (.field "badgeCap" (.custody 1) (.field "epoch" .natural .emptyRow))).isTransferablePlan = true := by decide
example : (Ty.variant (.field "badgeCap" (.custody 1) (.field "epoch" .natural .emptyRow))).isPlan = false := by decide
example : TVal.conforms samplePlanVal
    (.variant (.field "transferSturdyref"
      (.field "badgeCap" (.custody 1) (.field "coReceipt" (.custody 2) (.field "epoch" .natural .emptyRow)))
      .emptyRow)) = true := by decide
example : sampleRoundtripCheck = true := by decide

end Obend.Run.VaultDurableBridge

end
