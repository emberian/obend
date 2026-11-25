module
public import Obend.OS.NvmeDurablePersist
public import Obend.OS.SddfOwnership
import all Obend.OS.Sel4MicrokitKernel
import all Obend.OS.SmmuDmaConfinement
import Obend.Tactic.Tooth

public section
namespace Obend.OS.DragonStyleAppliance

open Sel4MicrokitKernel SmmuDmaConfinement NvmeDurablePersist
open Obend.Consensus.SimplexProtocol
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (SeL4MicrokitPartition)
open Obend.Digest.Cshake256.Native (bytesOfList)

/-- The verifier signs the fixed slot image, including its width. Recovery
retains the original binary body. The four leading octets are part of that body. -/
def envelope (body : ByteArray) : ByteArray :=
  bytesOfList (UInt8.ofNat body.size :: body.data.toList ++ List.replicate (99-body.size) 0)

def ofBody (body : ByteArray) : Option Record := do
  guard (10 ≤ body.size && body.size ≤ 99)
  let principal ← body[0]?
  let nonce ← body[1]?
  let effect ← body[2]?
  let cost ← body[3]?
  return ⟨principal.toNat, nonce.toNat, effect.toNat, cost.toNat, body⟩

structure Ports where
  nicDriver : PdId
  nvmeDriver : PdId
  descriptorFrames : List Nat

def Ports.layout (ports : Ports) (cfg : IngressCfg) (io : ChokepointSmmuConfig) :
    SddfOwnership.Layout :=
  ⟨[ports.nicDriver,ports.nvmeDriver], cfg.vpd, ports.descriptorFrames,
    io.partition.ingressRingFrames, io.partition.commitPrivateFrames⟩

private def settle (P : Protocol) (t : OutboxTurn) (st : OutboxState) :=
  match t.reconcileCert? with
  | none => some st
  | some cert => reconcileEscrowsWithCert P t.nextSent cert st

/-- Validate the candidate against the mapped private copy and the actual two authority gates. -/
def checkTurn (P : Protocol) (part : SeL4MicrokitPartition) (cfg : IngressCfg)
    (io : ChokepointSmmuConfig) (ports : Ports) (s : LoopState) (t : SmmuVerifierTurn) :
    Option LoopState := do
  let k := copyState s.kernel t.toVerifierTurn
  let k' := dispatchState cfg s.kernel t.toVerifierTurn
  if (verifyChokepointSmmuConfig io).isOk ∧ Obend.Trailblaze.Polis.checkMicrokitIsolation part ∧
      t.preEvents.all (fun e => e.actor != some cfg.vpd) ∧
      t.midEvents.all (fun e => e.actor != some cfg.vpd) ∧
      SddfOwnership.cpuLayout (ports.layout cfg io) k.maps ∧
      SddfOwnership.cpuLayout (ports.layout cfg io) k'.maps ∧
      readVia k cfg.vpd cfg.sharedV cfg.len = some t.ringAtCopy ∧
      (translate k.maps (.cpu cfg.vpd) cfg.privV true).isSome = true ∧
      readVia k' cfg.vpd (dispatchVaddr cfg) cfg.len = some t.out.req.spsc.sharedRingBeforeCopy then
    let host ← Obend.Polis.GrainPowerbox.stepPowerboxHost s.host (invokeOf t.toVerifierTurn)
    let mid ← stepOutbox P part t.out.nextSent s.outbox t.out.req
    let next ← settle P t.out mid
    return ⟨k',t.out.nextSent,next,host⟩
  else none

theorem checked_refines {P part cfg io ports s t f}
    (h : checkTurn P part cfg io ports s t = some f) (hr : Reach P s.sent)
    (network : SentSteps P s.sent t.out.nextSent) :
    ValidSmmuVerifierLoop io P part cfg s [t] f ∧
    SddfOwnership.cpuLayout (ports.layout cfg io) (copyState s.kernel t.toVerifierTurn).maps = true := by
  unfold checkTurn at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i accepted
  obtain ⟨hw,iso,pre,midEvents,cpu,_,ring,priv,disp⟩ := accepted
  simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
  obtain ⟨host,hostOk,st,gateOk,next,rec,rfl⟩ := h
  have ioOk : verifyChokepointSmmuConfig io = .ok () := by
    cases eq : verifyChokepointSmmuConfig io with
    | error err => rw [eq] at hw; contradiction
    | ok u => cases u; rfl
  simp only [List.all_eq_true,bne_iff_ne] at pre midEvents
  refine ⟨⟨ioOk,pre,midEvents,ring,priv,disp,hr,network,host,st,next,hostOk,gateOk,?_,
    rfl,sentSteps_reach hr network,iso,ioOk⟩,cpu⟩
  cases eq : t.out.reconcileCert? <;> simp_all [settle]

theorem checked_confinement {P part cfg io ports s t f}
    (h : checkTurn P part cfg io ports s t = some f) (hr : Reach P s.sent)
    (network : SentSteps P s.sent t.out.nextSent) :
    (∀ pd ∈ [ports.nicDriver,ports.nvmeDriver], ∀ va wr pa,
      translate (copyState s.kernel t.toVerifierTurn).maps (.cpu pd) va wr = some pa →
      pa / pageSize ∈ ports.descriptorFrames ∧ pa / pageSize ∉ io.partition.ingressRingFrames ∧
        pa / pageSize ∉ io.partition.commitPrivateFrames) ∧
    ∀ ops mem pa, pa / pageSize ∈ io.partition.commitPrivateFrames →
      (execStage2DmaBurst io.manifest mem ops).1 pa = mem pa := by
  obtain ⟨loop,cpu⟩ := checked_refines h hr network
  constructor
  · intro pd driver va wr pa access
    exact SddfOwnership.driver_descriptor_only cpu driver access
  · intro ops mem pa privateFrame
    exact (dma_burst_preserves_private_pd_frames loop.1 ops mem mem
      (fun _ _ _ => rfl)).1 pa (.inl privateFrame)

#tooth checked_refines by mutation checkTurn := fun _ _ _ _ _ s _ => some s

/-- The verifier advances once per installed generation. A volatile candidate
may be checked repeatedly against the same entry state until FUA succeeds. -/
structure Verifier where
  protocol : Protocol
  partition : SeL4MicrokitPartition
  ingress : IngressCfg
  iommu : ChokepointSmmuConfig
  ports : Ports
  stateAt : Nat → LoopState
  turnAt : Nat → SmmuVerifierTurn

/-- Bind the candidate's metadata to the bytes copied by the kernel before
consulting the two authority gates. The hosted ticket producer calls this entry. -/
def authorizeBody (P : Protocol) (part : SeL4MicrokitPartition) (cfg : IngressCfg)
    (io : ChokepointSmmuConfig) (ports : Ports) (s : LoopState) (t : SmmuVerifierTurn)
    (r : Record) : Option LoopState :=
  if ofBody r.payload = some r ∧ t.ringAtCopy = envelope r.payload ∧
      t.out.req.spsc.sharedRingBeforeCopy = t.ringAtCopy ∧ t.grain = r.principal ∧
      t.out.req.nullifierId = r.nullifier ∧ t.out.req.effectClass = .irreversibleActuation
  then checkTurn P part cfg io ports s t else none

def permits (v : Verifier) (xs : List Record) (r : Record) : Prop :=
  let i := xs.length
  let t := v.turnAt i
  Reach v.protocol (v.stateAt i).sent ∧ SentSteps v.protocol (v.stateAt i).sent t.out.nextSent ∧
  authorizeBody v.protocol v.partition v.ingress v.iommu v.ports (v.stateAt i) t r = some (v.stateAt (i+1))

private theorem loop_append {P part cfg s m f} {as bs : List VerifierTurn}
    (a : ValidVerifierLoop P part cfg s as m) (b : ValidVerifierLoop P part cfg m bs f) :
    ValidVerifierLoop P part cfg s (as ++ bs) f := by
  induction as generalizing s with
  | nil => exact a.1 ▸ b
  | cons t ts ih =>
    obtain ⟨pre,mid,ring,priv,disp,reach,steps,host,st₁,st₂,inv,gate,rec,rest⟩ := a
    exact ⟨pre,mid,ring,priv,disp,reach,steps,host,st₁,st₂,inv,gate,rec,ih rest⟩

def turns (v : Verifier) (n : Nat) := (List.range n).map fun i => (v.turnAt i).toVerifierTurn

private theorem accepted_loop (v : Verifier) {xs} (h : Accepted (permits v) xs)
    (boot : ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) [] (v.stateAt 0)) :
    ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) (turns v xs.length)
      (v.stateAt xs.length) ∧
    ∀ i r, xs[i]? = some r → (v.turnAt i).ringAtCopy = envelope r.payload ∧
      (v.turnAt i).out.req.nullifierId = r.nullifier := by
  induction h with
  | nil => exact ⟨boot, by simp⟩
  | @snoc xs r _ admitted _ ih =>
    obtain ⟨hr,advance,checked⟩ := admitted
    unfold authorizeBody at checked
    split at checked <;> try contradiction
    rename_i bound
    obtain ⟨_,bytes,_,_,effect,_⟩ := bound
    have single := (checked_refines checked hr advance).1
    have step := (validSmmuVerifierLoop_to_kernelLoop single).2
    constructor
    · simpa [turns,List.range_succ] using loop_append ih.1 step
    · intro i old atIndex
      by_cases lt : i < xs.length
      · rw [List.getElem?_append_left lt] at atIndex
        exact ih.2 i old atIndex
      · rw [List.getElem?_append_right (by omega)] at atIndex
        cases eq : i-xs.length with
        | zero =>
          have : i = xs.length := by omega
          subst i
          simp at atIndex
          subst old
          exact ⟨bytes,effect⟩
        | succ n => simp [eq] at atIndex

/-- A committed physical prefix refines the kernel loop from the actual verifier
turns. Even TX retransmissions after multiple resets name the same canonical
payload and irreversible identifier at the original generation. -/
theorem dragonstyle_appliance (v : Verifier) {d p xs tx issues}
    (boot : ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) [] (v.stateAt 0))
    (h : Run (permits v) d p xs tx issues) :
    recover d = some xs ∧ issues.Nodup ∧ (xs.map Record.nullifier).Nodup ∧
    ValidVerifierLoop v.protocol v.partition v.ingress (v.stateAt 0) (turns v xs.length)
      (v.stateAt xs.length) ∧
    ∀ z ∈ tx, xs[z.1]? = some z.2 ∧
      request d.image z.2.principal z.2 = .cached (z.1+1) ∧
      (v.turnAt z.1).ringAtCopy = envelope z.2.payload ∧
      (v.turnAt z.1).out.req.nullifierId = z.2.nullifier := by
  obtain ⟨cold,legal,once,ids,sent⟩ := durable_appliance h
  obtain ⟨loop,bytes⟩ := accepted_loop v legal boot
  refine ⟨cold,once,ids,loop,?_⟩
  intro z hz
  obtain ⟨atIndex,cached⟩ := sent z hz
  exact ⟨atIndex,cached,bytes _ _ atIndex⟩

/-- The cold outbox gatekeeper needs the high-water mark before processing any
new certificate. Other outbox fields cannot make a spent identifier admissible. -/
def restoreOutbox (st : OutboxState) (xs : List Record) : OutboxState :=
  {st with highWaterNullifier := xs.foldr (fun r mark => max r.nullifier mark) st.highWaterNullifier}

private theorem restored_ge (st : OutboxState) (xs : List Record) (r : Record) (mem : r ∈ xs) :
    r.nullifier ≤ (restoreOutbox st xs).highWaterNullifier := by
  change r.nullifier ≤ xs.foldr _ _
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp mem with rfl | rest
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih rest) (Nat.le_max_right _ _)

theorem cold_outbox_refuses {permit d p xs tx issues} (h : Run permit d p xs tx issues)
    (P : Protocol) (part : SeL4MicrokitPartition) (sent : Sent) (st : OutboxState)
    (req : OutboxEffectReq) (r : Record) (hr : r ∈ xs) (eq : req.nullifierId = r.nullifier)
    (effect : req.effectClass ≠ .idempotentRead) :
    (recover d).bind (fun records => stepOutbox P part sent (restoreOutbox st records) req) = none := by
  rw [(durable_appliance h).1]
  apply stepOutbox_refuses_spent_nullifier _ _ _ _ _ effect
  rw [eq]
  exact restored_ge st xs r hr

end Obend.OS.DragonStyleAppliance
