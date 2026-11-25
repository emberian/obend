module
public import Obend.OS.NvmeDurablePersist
public import Obend.OS.SddfOwnership
import all Obend.OS.Sel4MicrokitKernel
import all Obend.OS.SmmuDmaConfinement
import all Obend.OS.NvmeDurablePersist
import all Obend.OS.SddfOwnership

public section
namespace Obend.OS.DragonStyleAppliance

open Sel4MicrokitKernel SmmuDmaConfinement NvmeDurablePersist
open Obend.Consensus.SimplexProtocol
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (SeL4MicrokitPartition)
open Obend.Digest.Cshake256
open Obend.Digest.Cshake256.Native
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Pure `ByteArray` Envelopes (Zero `List.replicate` / `bytesOfList`) -/

/-- Canonical 72-byte committed envelope built purely on `ByteArray`:
40-byte big-endian `(principal, nonce, nullifier, cost, payload.size)` header followed by
the 32-byte `cSHAKE256` payload digest. Fits inside a single 4KiB Microkit ingress page
for ANY payload size `0..4096`B (and beyond). -/
def envelope (r : Record) : ByteArray := recordPreimage r

/-- Raw variable-width pure-`ByteArray` envelope `(40B header ++ payload)`. -/
def rawEnvelope (r : Record) : ByteArray :=
  let out := ByteArray.emptyWithCapacity (40 + r.payload.size)
  let out := pushBEU64 8 (UInt64.ofNat r.principal) out
  let out := pushBEU64 8 (UInt64.ofNat r.nonce) out
  let out := pushBEU64 8 (UInt64.ofNat r.nullifier) out
  let out := pushBEU64 8 (UInt64.ofNat r.cost) out
  let out := pushBEU64 8 (UInt64.ofNat r.payload.size) out
  appendBytes out r.payload

theorem envelope_size (r : Record) : (envelope r).size = 72 :=
  recordPreimage_size r

theorem rawEnvelope_injective {pol : Policy} {r1 r2 : Record}
    (h1 : r1.fits pol) (h2 : r2.fits pol) (hp1 : r1.payload.size < 2 ^ 64) (hp2 : r2.payload.size < 2 ^ 64)
    (heq : rawEnvelope r1 = rawEnvelope r2) : r1 = r2 := by
  have hl : (rawEnvelope r1).data.toList = (rawEnvelope r2).data.toList := congrArg (fun b => b.data.toList) heq
  have hemp : ∀ n, (ByteArray.emptyWithCapacity n).data.toList = [] := fun _ => rfl
  simp only [rawEnvelope, appendBytes_toList, pushBEU64_toList 8 (by decide), hemp,
    List.nil_append, List.append_assoc] at hl
  obtain ⟨hpr, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hno, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hnu, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hco, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨_, hpay⟩ := List.append_inj hl (by simp)
  have epr := be_injective (UInt64.ofNat r1.principal).toBitVec.isLt (UInt64.ofNat r2.principal).toBitVec.isLt hpr
  have eno := be_injective (UInt64.ofNat r1.nonce).toBitVec.isLt (UInt64.ofNat r2.nonce).toBitVec.isLt hno
  have enu := be_injective (UInt64.ofNat r1.nullifier).toBitVec.isLt (UInt64.ofNat r2.nullifier).toBitVec.isLt hnu
  have eco := be_injective (UInt64.ofNat r1.cost).toBitVec.isLt (UInt64.ofNat r2.cost).toBitVec.isLt hco
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1] at epr
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1.2.1, Nat.mod_eq_of_lt h2.2.1] at eno
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1.2.2.1, Nat.mod_eq_of_lt h2.2.2.1] at enu
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1.2.2.2.1, Nat.mod_eq_of_lt h2.2.2.2.1] at eco
  cases r1; cases r2
  simp only [Record.mk.injEq]
  exact ⟨epr, eno, enu, eco, byteArray_eq_of_toList_eq hpay⟩

/-- **256-bit `cSHAKE256` binding of `envelope`**:
two fitting records sharing the same 72-byte `envelope` are either identical or produce
a concrete `cSHAKE256` collision on their payloads. -/
theorem envelope_binds {pol : Policy} {r1 r2 : Record} (h1 : r1.fits pol) (h2 : r2.fits pol)
    (heq : envelope r1 = envelope r2) :
    r1 = r2 ∨ CollisionAmong (cshake256Bytes payloadDomain.data.toList)
      (fun x => x = r1.payload.data.toList ∨ x = r2.payload.data.toList) := by
  have hl : (recordPreimage r1).data.toList = (recordPreimage r2).data.toList :=
    congrArg (fun b => b.data.toList) heq
  simp only [recordPreimage_toList, List.append_assoc] at hl
  obtain ⟨hpr, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hno, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hnu, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨hco, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨_, hdig⟩ := List.append_inj hl (by simp)
  have epr := be_injective (UInt64.ofNat r1.principal).toBitVec.isLt (UInt64.ofNat r2.principal).toBitVec.isLt hpr
  have eno := be_injective (UInt64.ofNat r1.nonce).toBitVec.isLt (UInt64.ofNat r2.nonce).toBitVec.isLt hno
  have enu := be_injective (UInt64.ofNat r1.nullifier).toBitVec.isLt (UInt64.ofNat r2.nullifier).toBitVec.isLt hnu
  have eco := be_injective (UInt64.ofNat r1.cost).toBitVec.isLt (UInt64.ofNat r2.cost).toBitVec.isLt hco
  simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1,
    Nat.mod_eq_of_lt h1.2.1, Nat.mod_eq_of_lt h2.2.1,
    Nat.mod_eq_of_lt h1.2.2.1, Nat.mod_eq_of_lt h2.2.2.1,
    Nat.mod_eq_of_lt h1.2.2.2.1, Nat.mod_eq_of_lt h2.2.2.2.1] at epr eno enu eco
  if hpay : r1.payload.data.toList = r2.payload.data.toList then
    left
    cases r1; cases r2
    simp only [Record.mk.injEq]
    exact ⟨epr, eno, enu, eco, byteArray_eq_of_toList_eq hpay⟩
  else
    right
    simp only [payloadDigest, cshake256Kernel_toList] at hdig
    exact ⟨r1.payload.data.toList, r2.payload.data.toList, .inl rfl, .inr rfl, hpay, congrArg ofBE hdig⟩

/-! ## 2. Unified Microkit + SMMU `.dev` Admission Gate -/

structure Ports where
  nicDriver : PdId
  nvmeDriver : PdId
  descriptorFrames : List Nat

def Ports.layout (ports : Ports) (cfg : IngressCfg) (io : ChokepointSmmuConfig) :
    SddfOwnership.Layout :=
  ⟨[ports.nicDriver, ports.nvmeDriver], cfg.vpd, ports.descriptorFrames,
    io.partition.ingressRingFrames, io.partition.commitPrivateFrames,
    io.partition.kernelAndCodeFrames, io.partition.persistFrames,
    io.partition.egressOutboxFrames, io.manifest⟩

private def settle (P : Protocol) (t : OutboxTurn) (st : OutboxState) : Option OutboxState :=
  match t.reconcileCert? with
  | none => some st
  | some cert => reconcileEscrowsWithCert P t.nextSent cert st

/-- Validate the candidate against the mapped private copy, full CPU+SMMU `.dev` confinement,
and both authority gates (Powerbox + IrreversibleOutbox). -/
def checkTurn (P : Protocol) (part : SeL4MicrokitPartition) (cfg : IngressCfg)
    (io : ChokepointSmmuConfig) (ports : Ports) (s : LoopState) (t : SmmuVerifierTurn) :
    Option LoopState := do
  let k := copyState s.kernel t.toVerifierTurn
  let k' := dispatchState cfg s.kernel t.toVerifierTurn
  if (verifyChokepointSmmuConfig io).isOk ∧ Obend.Trailblaze.Polis.checkMicrokitIsolation part ∧
      t.preEvents.all (fun e => e.actor != some cfg.vpd) ∧
      t.midEvents.all (fun e => e.actor != some cfg.vpd) ∧
      SddfOwnership.systemLayout (ports.layout cfg io) k.maps ∧
      SddfOwnership.systemLayout (ports.layout cfg io) k'.maps ∧
      readVia k cfg.vpd cfg.sharedV cfg.len = some t.ringAtCopy ∧
      (translate k.maps (.cpu cfg.vpd) cfg.privV true).isSome = true ∧
      readVia k' cfg.vpd (dispatchVaddr cfg) cfg.len = some t.out.req.spsc.sharedRingBeforeCopy then
    let host ← Obend.Polis.GrainPowerbox.stepPowerboxHost s.host (invokeOf t.toVerifierTurn)
    let mid ← stepOutbox P part t.out.nextSent s.outbox t.out.req
    let next ← settle P t.out mid
    return ⟨k', t.out.nextSent, next, host⟩
  else none

theorem checked_refines {P part cfg io ports s t f}
    (h : checkTurn P part cfg io ports s t = some f) (hr : Reach P s.sent)
    (network : SentSteps P s.sent t.out.nextSent) :
    ValidSmmuVerifierLoop io P part cfg s [t] f ∧
    SddfOwnership.systemLayout (ports.layout cfg io) (copyState s.kernel t.toVerifierTurn).maps = true := by
  unfold checkTurn at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i accepted
  obtain ⟨hw, iso, pre, midEvents, sys, _, ring, priv, disp⟩ := accepted
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨host, hostOk, st, gateOk, next, rec, rfl⟩ := h
  have ioOk : verifyChokepointSmmuConfig io = .ok () := by
    cases eq : verifyChokepointSmmuConfig io with
    | error err => rw [eq] at hw; contradiction
    | ok u => cases u; rfl
  simp only [List.all_eq_true, bne_iff_ne] at pre midEvents
  refine ⟨⟨ioOk, pre, midEvents, ring, priv, disp, hr, network, host, st, next, hostOk, gateOk, ?_,
    rfl, sentSteps_reach hr network, iso, ioOk⟩, sys⟩
  cases eq : t.out.reconcileCert? <;> simp_all [settle]

/-- **End-to-end CPU + Kernel `.dev` SMMU + Hardware Stage-2 DMA confinement**:
proves simultaneously that (1) driver PDs map only descriptor frames, (2) EVERY kernel `.dev`
stream mapping is confined to an authorized `SmmuDmaConfinement` region away from private & kernel
frames, and (3) arbitrary stage-2 DMA bursts preserve verifier-private frames. -/
theorem checked_confinement {P part cfg io ports s t f}
    (h : checkTurn P part cfg io ports s t = some f) (hr : Reach P s.sent)
    (network : SentSteps P s.sent t.out.nextSent) :
    (∀ pd ∈ [ports.nicDriver, ports.nvmeDriver], ∀ va wr pa,
      translate (copyState s.kernel t.toVerifierTurn).maps (.cpu pd) va wr = some pa →
      pa / pageSize ∈ ports.descriptorFrames ∧ pa / pageSize ∉ io.partition.ingressRingFrames ∧
        pa / pageSize ∉ io.partition.commitPrivateFrames ∧
        pa / pageSize ∉ io.partition.kernelAndCodeFrames) ∧
    (∀ sid va wr pa,
      translate (copyState s.kernel t.toVerifierTurn).maps (.dev sid) va wr = some pa →
      pa / pageSize ∉ io.partition.commitPrivateFrames ∧
        pa / pageSize ∉ io.partition.kernelAndCodeFrames ∧
        (wr = true → pa / pageSize ∉ io.partition.egressOutboxFrames) ∧
        ∃ pt ∈ io.manifest.streams, pt.streamId.toNat = sid ∧
          ∃ reg ∈ pt.regions, reg.iova.toNat ≤ va ∧ va < reg.iova.toNat + reg.size.toNat ∧
            reg.paddr.toNat + (va - reg.iova.toNat) = pa ∧
            (wr = true → reg.perm.allowsWrite = true)) ∧
    (∀ ops mem pa, pa / pageSize ∈ io.partition.commitPrivateFrames →
      (execStage2DmaBurst io.manifest mem ops).1 pa = mem pa) := by
  obtain ⟨loop, sys⟩ := checked_refines h hr network
  refine ⟨?_, ?_, ?_⟩
  · intro pd driver va wr pa access
    exact SddfOwnership.driver_descriptor_only sys driver access
  · intro sid va wr pa access
    obtain ⟨_, _, _, hnp, hnk, hne, _, hreg⟩ := SddfOwnership.dev_dma_confined sys access
    exact ⟨hnp, hnk, hne, hreg⟩
  · intro ops mem pa privateFrame
    exact (dma_burst_preserves_private_pd_frames loop.1 ops mem mem
      (fun _ _ _ => rfl)).1 pa (.inl privateFrame)

/-- Refusal witness: `checkTurn` rejects any state whose `.dev` mapping aliases a commit-private frame. -/
theorem checkTurn_refuses_dev_private {P part cfg io ports s t m sid}
    (hm : m ∈ (copyState s.kernel t.toVerifierTurn).maps) (hdev : m.space = .dev sid)
    (hpriv : m.pfn ∈ io.partition.commitPrivateFrames) :
    checkTurn P part cfg io ports s t = none := by
  have hbad := SddfOwnership.systemLayout_refuses_dev_private (l := ports.layout cfg io) hm hdev hpriv
  simp [checkTurn, hbad]

/-! ## 3. Multi-Epoch Durable Appliance Composition -/

structure Verifier where
  policy : Policy
  protocol : Protocol
  partition : SeL4MicrokitPartition
  ingress : IngressCfg
  iommu : ChokepointSmmuConfig
  ports : Ports
  stateAt : Nat → LoopState
  turnAt : Nat → SmmuVerifierTurn

/-- Bind the candidate's metadata and `0..maxPayload` payload (via 72-byte `cSHAKE256` envelope)
to the bytes copied by the kernel before consulting Powerbox and IrreversibleOutbox. -/
def authorizeBody (pol : Policy) (P : Protocol) (part : SeL4MicrokitPartition) (cfg : IngressCfg)
    (io : ChokepointSmmuConfig) (ports : Ports) (s : LoopState) (t : SmmuVerifierTurn)
    (r : Record) : Option LoopState :=
  if decide (r.payload.size ≤ pol.maxPayload ∧ r.principal < 2 ^ 64 ∧ r.nonce < 2 ^ 64 ∧
      r.nullifier < 2 ^ 64 ∧ r.cost < 2 ^ 64) ∧
      t.ringAtCopy = envelope r ∧
      t.out.req.spsc.sharedRingBeforeCopy = t.ringAtCopy ∧ t.grain = r.principal ∧
      t.out.req.nullifierId = r.nullifier ∧ t.out.req.effectClass = .irreversibleActuation
  then checkTurn P part cfg io ports s t else none

def permits (v : Verifier) (xs : List Record) (r : Record) : Prop :=
  let i := xs.length
  let t := v.turnAt i
  Reach v.protocol (v.stateAt i).sent ∧ SentSteps v.protocol (v.stateAt i).sent t.out.nextSent ∧
  authorizeBody v.policy v.protocol v.partition v.ingress v.iommu v.ports (v.stateAt i) t r =
    some (v.stateAt (i + 1))

private theorem loop_append {P part cfg s m f} {as bs : List VerifierTurn}
    (a : ValidVerifierLoop P part cfg s as m) (b : ValidVerifierLoop P part cfg m bs f) :
    ValidVerifierLoop P part cfg s (as ++ bs) f := by
  induction as generalizing s with
  | nil => exact a.1 ▸ b
  | cons t ts ih =>
    obtain ⟨pre, mid, ring, priv, disp, reach, steps, host, st₁, st₂, inv, gate, rec, rest⟩ := a
    exact ⟨pre, mid, ring, priv, disp, reach, steps, host, st₁, st₂, inv, gate, rec, ih rest⟩

def turns (v : Verifier) (n : Nat) : List VerifierTurn :=
  (List.range n).map fun i => (v.turnAt i).toVerifierTurn

private theorem accepted_loop (v : Verifier) {xs : List Record} (h : Accepted v.policy (permits v) xs)
    (boot : ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) [] (v.stateAt 0)) :
    ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) (turns v xs.length)
      (v.stateAt xs.length) ∧
    ∀ i r, xs[i]? = some r → (v.turnAt i).ringAtCopy = envelope r ∧
      (v.turnAt i).out.req.nullifierId = r.nullifier := by
  induction h with
  | nil => exact ⟨boot, by simp⟩
  | @snoc xs r _ admitted _ _ _ _ _ ih =>
    obtain ⟨hr, advance, checked⟩ := admitted
    unfold authorizeBody at checked
    split at checked <;> try contradiction
    rename_i bound
    obtain ⟨_, bytes, _, _, effect, _⟩ := bound
    have single := (checked_refines checked hr advance).1
    have step := (validSmmuVerifierLoop_to_kernelLoop single).2
    constructor
    · simpa [turns, List.range_succ] using loop_append ih.1 step
    · intro i old atIndex
      by_cases lt : i < xs.length
      · rw [List.getElem?_append_left lt] at atIndex
        exact ih.2 i old atIndex
      · rw [List.getElem?_append_right (by omega)] at atIndex
        cases eq : i - xs.length with
        | zero =>
          have : i = xs.length := by omega
          subst i
          simp at atIndex
          subst old
          exact ⟨bytes, effect⟩
        | succ n => simp [eq] at atIndex

/-- **End-to-end DragonStyle durable appliance theorem**:
for arbitrary parameterized `Policy` (`maxTurns`, `budgetCap`, `maxPayload`), real 512-byte
`ByteArray` LBA sectors, out-of-order volatile write cache + `FLUSH` + atomic `FUA` `cSHAKE256`
superblock, and multi-epoch checkpoints:
1. Cold recovery from durable `d.media` yields the exact active suffix and `cSHAKE256` chain digest.
2. Dispatched actuations have unique nullifiers and strictly respect `v.policy.budgetCap`.
3. The full committed history refines `ValidVerifierLoop` with CPU + `.dev` SMMU confinement.
4. Every historical TX receipt indexes its exact committed record and bound `envelope`, and every
   active-window receipt replays to `.cached (z.1 + 1)`. -/
theorem dragonstyle_appliance (v : Verifier) {d p all base tx issues}
    (boot : ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) [] (v.stateAt 0))
    (h : Run v.policy (permits v) d p all base tx issues) :
    (∃ sb, recoverFull v.policy d = some (sb, all.drop base) ∧
      sb.generation.toNat = all.length ∧ sb.baseGen.toNat = base ∧
      sb.chainDigest = logDigest all) ∧
    issues.Nodup ∧ (all.map Record.nullifier).Nodup ∧
    (∀ who, spent all who ≤ v.policy.budgetCap) ∧
    ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) (turns v all.length)
      (v.stateAt all.length) ∧
    ∀ z ∈ tx, all[z.1]? = some z.2 ∧
      (base ≤ z.1 →
        requestWith v.policy base (maxNullifier (all.take base)) (fun who => spent (all.take base) who)
          (all.drop base) z.2.principal z.2 = .cached (z.1 + 1)) ∧
      (v.turnAt z.1).ringAtCopy = envelope z.2 ∧
      (v.turnAt z.1).out.req.nullifierId = z.2.nullifier := by
  obtain ⟨cold, legal, once, ids, budget, sent⟩ := durable_appliance h
  obtain ⟨loop, bytes⟩ := accepted_loop v legal boot
  refine ⟨cold, once, ids, budget, loop, ?_⟩
  intro z hz
  obtain ⟨atIndex, cached⟩ := sent z hz
  exact ⟨atIndex, cached, bytes _ _ atIndex⟩

/-- Restore the cold outbox gatekeeper high-water nullifier from both the `cSHAKE256`-authenticated
superblock checkpoint high-water mark AND the recovered active WAL records. -/
def restoreOutbox (st : OutboxState) (sb : Superblock) (active : List Record) : OutboxState :=
  { st with highWaterNullifier := max st.highWaterNullifier (max sb.highWaterNullifier.toNat (maxNullifier active)) }

theorem cold_outbox_refuses {pol permit d p all base tx issues}
    (h : Run pol permit d p all base tx issues)
    (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent) (st : OutboxState)
    (req : OutboxEffectReq) (r : Record) (hr : r ∈ all) (eq : req.nullifierId = r.nullifier)
    (effect : req.effectClass ≠ .idempotentRead) :
    (recoverFull pol d).bind (fun sr => stepOutbox P part sent (restoreOutbox st sr.1 sr.2) req) = none := by
  obtain ⟨sb, hrec, hhw⟩ := cold_recover_highWater h
  rw [hrec]
  apply stepOutbox_refuses_spent_nullifier _ _ _ _ _ effect
  have hle : r.nullifier ≤ max sb.highWaterNullifier.toNat (maxNullifier (all.drop base)) :=
    Nat.le_trans (maxNullifier_le_of_mem hr) hhw
  unfold restoreOutbox
  rw [eq]
  exact Nat.le_trans hle (Nat.le_max_right _ _)

end Obend.OS.DragonStyleAppliance
