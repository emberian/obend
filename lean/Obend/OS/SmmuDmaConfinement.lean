module
/-
# Obend.OS.SmmuDmaConfinement — SMMUv3 / RISC-V IOMMU Stage-2 DMA chokepoint confinement

Closes SHE Gap #2 (`StreamId → Stage2IoPageTable`, `FaultOnUnmappedStream`, `dma_burst_preserves_private_pd_frames`,
`smmu_verifier_loop_dma_safe`, `smmuManifestDigest_binds`, `smmuChokepointJudge`).
-/
public import Obend.Judge.Class
public import Obend.OS.Sel4MicrokitKernel
public import Obend.Polis.SandboxDomainTags
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.OS.Sel4MicrokitKernel
import all Obend.Polis.SandboxDomainTags

public section
namespace Obend.OS.SmmuDmaConfinement

open Obend Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes
open Obend.Consensus.SimplexProtocol Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (SeL4MicrokitPartition checkMicrokitIsolation Sel4CapDlNonInterfering)
open Obend.Polis.GrainPowerbox (PowerboxHost GrainId Accountable actionDigest)
open Obend.Polis.SandboxDomainTags (asciiTagBytes encodeSandboxFields encodeSandboxFields_injective
  sandboxDomainHash u64ToBe8 u64ToBe8_length u64ToBe8_injective)
open Obend.OS.Sel4MicrokitKernel
set_option autoImplicit false

/-! ## 1. Hardware Bus-Masters, Stage-2 Page Tables, & 4-PD Chokepoint Classification -/
abbrev StreamId := UInt32
def wildcardStreamId : StreamId := 0xFFFFFFFF
def maxRootServerSpanBytes : Nat := 10 * 1024 * 1024
def stockMicrokitLoaderBase : Nat := 0x70000000

inductive SmmuArch where | armSmmuV3 | riscvIommu deriving DecidableEq, Repr
def SmmuArch.tagByte : SmmuArch → UInt8 | .armSmmuV3 => 1 | .riscvIommu => 2
theorem SmmuArch.tagByte_injective {a b : SmmuArch} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive DeviceRole where
  | ingressNic | persistNvme | egressNic | displayScanout | cameraCsi2 | gpu
  deriving DecidableEq, Repr
def DeviceRole.tagByte : DeviceRole → UInt8
  | .ingressNic => 1 | .persistNvme => 2 | .egressNic => 3
  | .displayScanout => 4 | .cameraCsi2 => 5 | .gpu => 6
theorem DeviceRole.tagByte_injective {a b : DeviceRole} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive ChokepointPdRole where | ingress | commit | persist | txEgress deriving DecidableEq, Repr
def ChokepointPdRole.tagByte : ChokepointPdRole → UInt8
  | .ingress => 0 | .commit => 1 | .persist => 2 | .txEgress => 3
def ChokepointPdRole.toPdId : ChokepointPdRole → PdId
  | .ingress => 0 | .commit => 1 | .persist => 2 | .txEgress => 3
theorem ChokepointPdRole.tagByte_injective {a b : ChokepointPdRole}
    (h : a.tagByte = b.tagByte) : a = b := by cases a <;> cases b <;> first | rfl | cases h
inductive PageGranule where | page4KiB | huge2MiB deriving DecidableEq, Repr
def PageGranule.byteSize : PageGranule → Nat | .page4KiB => 4096 | .huge2MiB => 2097152
def PageGranule.tagByte : PageGranule → UInt8 | .page4KiB => 1 | .huge2MiB => 2
theorem PageGranule.byteSize_pos (g : PageGranule) : 0 < g.byteSize := by cases g <;> decide
theorem PageGranule.tagByte_injective {a b : PageGranule} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive IoPerm where | readOnly | writeOnly | readWrite deriving DecidableEq, Repr
def IoPerm.tagByte : IoPerm → UInt8 | .readOnly => 1 | .writeOnly => 2 | .readWrite => 3
def IoPerm.allowsRead : IoPerm → Bool | .readOnly => true | .writeOnly => false | .readWrite => true
def IoPerm.allowsWrite : IoPerm → Bool | .readOnly => false | .writeOnly => true | .readWrite => true
theorem IoPerm.tagByte_injective {a b : IoPerm} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive DmaAccess where | dmaRead | dmaWrite deriving DecidableEq, Repr
def IoPerm.permits (p : IoPerm) : DmaAccess → Bool
  | .dmaRead => p.allowsRead | .dmaWrite => p.allowsWrite
inductive ProtectedFrameClass where
  | commitPrivate | pdCodeStackCspace | trngMmio | kernelPageTable deriving DecidableEq, Repr
def ProtectedFrameClass.tagByte : ProtectedFrameClass → UInt8
  | .commitPrivate => 1 | .pdCodeStackCspace => 2 | .trngMmio => 3 | .kernelPageTable => 4
theorem ProtectedFrameClass.tagByte_injective {a b : ProtectedFrameClass}
    (h : a.tagByte = b.tagByte) : a = b := by cases a <;> cases b <;> first | rfl | cases h
inductive DmaRegionKind where
  | ingressRing | commitPrivateFrame | pdCodeStackCspace | trngMmio | persistWalPool
  | egressOutboxRing | displayFramebuffer | cameraRing | gpuScratchPool deriving DecidableEq, Repr
def DmaRegionKind.tagByte : DmaRegionKind → UInt8
  | .ingressRing => 1 | .commitPrivateFrame => 2 | .pdCodeStackCspace => 3
  | .trngMmio => 4 | .persistWalPool => 5 | .egressOutboxRing => 6
  | .displayFramebuffer => 7 | .cameraRing => 8 | .gpuScratchPool => 9
theorem DmaRegionKind.tagByte_injective {a b : DmaRegionKind}
    (h : a.tagByte = b.tagByte) : a = b := by cases a <;> cases b <;> first | rfl | cases h

structure ProtectedPhysRange where
  classTag : ProtectedFrameClass
  basePaddr : UInt64
  size : UInt64
  deriving DecidableEq, Repr
structure Stage2DmaRegion where
  iova : UInt64
  paddr : UInt64
  size : UInt64
  granule : PageGranule
  perm : IoPerm
  kind : DmaRegionKind
  deriving DecidableEq, Repr
structure Stage2IoPageTable where
  streamId : StreamId
  role : DeviceRole
  ownerPd : ChokepointPdRole
  regions : List Stage2DmaRegion
  deriving DecidableEq, Repr
structure SmmuManifest where
  arch : SmmuArch
  defaultDeny : Bool
  rootserverPhysStart : UInt64
  rootserverPhysEnd : UInt64
  dmaPoolBase : UInt64
  dmaPoolSize : UInt64
  protectedRanges : List ProtectedPhysRange
  streams : List Stage2IoPageTable
  deriving DecidableEq, Repr
/-- Physical `4 KiB` frame classification across the 4-PD Microkit chokepoint. -/
structure ChokepointFramePartition where
  rootServerBootSpan : UInt64 × UInt64
  ingressRingFrames : List Nat
  commitPrivateFrames : List Nat
  kernelAndCodeFrames : List Nat
  persistFrames : List Nat
  egressOutboxFrames : List Nat
  deriving DecidableEq, Repr
structure ChokepointSmmuConfig where
  manifest : SmmuManifest
  partition : ChokepointFramePartition
  deriving DecidableEq, Repr

/-! ## 2. Stage-2 Address Translation, Default-Deny, & Environment Completeness -/

inductive SmmuDmaFault where
  | bypassModeDisabled | invalidStreamId (sid : StreamId) | faultOnUnmappedStream (sid : StreamId)
  | zeroOrUnmappedIova (sid : StreamId) (iova len : Nat)
  | permissionFault (sid : StreamId) (acc : DmaAccess) (granted : IoPerm)
  deriving DecidableEq, Repr

def lookupStream (streams : List Stage2IoPageTable) (sid : StreamId) : Option Stage2IoPageTable :=
  streams.find? fun pt => pt.streamId == sid

def lookupDmaRegion (regions : List Stage2DmaRegion) (iova len : Nat) : Option Stage2DmaRegion :=
  regions.find? fun r => decide (r.iova.toNat ≤ iova ∧ iova + len ≤ r.iova.toNat + r.size.toNat)

/-- Operational Stage-2 IOMMU translator enforcing `FaultOnUnmappedStream` (`defaultDeny = true`). -/
def translateStage2Dma (m : SmmuManifest) (sid : StreamId)
    (iova len : Nat) (acc : DmaAccess) : Except SmmuDmaFault Nat :=
  if !m.defaultDeny then .error .bypassModeDisabled
  else if sid == 0 || sid == wildcardStreamId then .error (.invalidStreamId sid)
  else if len == 0 then .error (.zeroOrUnmappedIova sid iova len)
  else match lookupStream m.streams sid with
    | none => .error (.faultOnUnmappedStream sid)
    | some pt => match lookupDmaRegion pt.regions iova len with
      | none => .error (.zeroOrUnmappedIova sid iova len)
      | some reg =>
        if reg.perm.permits acc then .ok (reg.paddr.toNat + (iova - reg.iova.toNat))
        else .error (.permissionFault sid acc reg.perm)

theorem lookupStream_some {streams : List Stage2IoPageTable} {sid : StreamId} {pt : Stage2IoPageTable}
    (h : lookupStream streams sid = some pt) : pt ∈ streams ∧ pt.streamId = sid := by
  induction streams with
  | nil => simp [lookupStream] at h
  | cons x xs ih =>
    unfold lookupStream at h; simp only [List.find?_cons] at h; split at h
    · rename_i hx; cases h; exact ⟨List.mem_cons_self, beq_iff_eq.mp hx⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem lookupDmaRegion_some {regions : List Stage2DmaRegion} {iova len : Nat} {reg : Stage2DmaRegion}
    (h : lookupDmaRegion regions iova len = some reg) :
    reg ∈ regions ∧ reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat := by
  induction regions with
  | nil => simp [lookupDmaRegion] at h
  | cons x xs ih =>
    unfold lookupDmaRegion at h; simp only [List.find?_cons] at h; split at h
    · rename_i hx; cases h; obtain ⟨h1, h2⟩ := decide_eq_true_eq.mp hx; exact ⟨List.mem_cons_self, h1, h2⟩
    · obtain ⟨hm, h1, h2⟩ := ih h; exact ⟨List.mem_cons_of_mem _ hm, h1, h2⟩

theorem translateStage2Dma_ok {m : SmmuManifest} {sid : StreamId} {iova len : Nat}
    {acc : DmaAccess} {pa : Nat} (h : translateStage2Dma m sid iova len acc = .ok pa) :
    m.defaultDeny = true ∧ sid ≠ 0 ∧ sid ≠ wildcardStreamId ∧ 0 < len ∧
      ∃ pt ∈ m.streams, pt.streamId = sid ∧ ∃ reg ∈ pt.regions,
        reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat ∧
        reg.perm.permits acc = true ∧ pa = reg.paddr.toNat + (iova - reg.iova.toNat) := by
  unfold translateStage2Dma at h
  split at h; · cases h
  rename_i hd; split at h; · cases h
  rename_i hs; split at h; · cases h
  rename_i hl
  cases hst : lookupStream m.streams sid with
  | none => simp only [hst] at h; cases h
  | some pt =>
    simp only [hst] at h
    cases hrg : lookupDmaRegion pt.regions iova len with
    | none => simp only [hrg] at h; cases h
    | some reg =>
      simp only [hrg] at h; split at h
      · rename_i hp; cases h
        obtain ⟨hptMem, hptSid⟩ := lookupStream_some hst
        obtain ⟨hrgMem, hlo, hhi⟩ := lookupDmaRegion_some hrg
        have hdef : m.defaultDeny = true := by cases hdd : m.defaultDeny <;> simp_all
        have hs0 : sid ≠ 0 ∧ sid ≠ wildcardStreamId := by
          simpa only [Bool.or_eq_true, beq_iff_eq, not_or] using hs
        have hne : len ≠ 0 := by simpa only [beq_iff_eq] using hl
        exact ⟨hdef, hs0.1, hs0.2, Nat.pos_of_ne_zero hne, pt, hptMem, hptSid, reg, hrgMem, hlo, hhi, hp, rfl⟩
      · cases h

/-- **`FaultOnUnmappedStream`**: non-sentinel `StreamId`s absent from `m.streams` fault. -/
theorem unmapped_stream_dma_faults (m : SmmuManifest) (sid : StreamId) (iova len : Nat)
    (acc : DmaAccess) (hDeny : m.defaultDeny = true) (hNe0 : sid ≠ 0)
    (hNeWild : sid ≠ wildcardStreamId) (hLen : 0 < len)
    (hUnmapped : ∀ pt ∈ m.streams, pt.streamId ≠ sid) :
    translateStage2Dma m sid iova len acc = .error (.faultOnUnmappedStream sid) := by
  have hNone : lookupStream m.streams sid = none :=
    List.find?_eq_none.mpr fun pt hpt => by simp [hUnmapped pt hpt]
  have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hSidB : (sid == 0 || sid == wildcardStreamId) = false := by simp [hNe0, hNeWild]
  simp [translateStage2Dma, hDeny, hSidB, hLenB, hNone]

def RegionsIovaDisjoint (regions : List Stage2DmaRegion) : Prop :=
  ∀ a ∈ regions, ∀ b ∈ regions,
    a.iova.toNat < b.iova.toNat + b.size.toNat → b.iova.toNat < a.iova.toNat + a.size.toNat → a = b

def ValidStage2DmaContract (m : SmmuManifest) (sid : StreamId) (iova len : Nat)
    (acc : DmaAccess) : Prop :=
  m.defaultDeny = true ∧ sid ≠ 0 ∧ sid ≠ wildcardStreamId ∧ 0 < len ∧
    ∃ pt ∈ m.streams, pt.streamId = sid ∧ ∃ reg ∈ pt.regions,
      reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat ∧
      reg.perm.permits acc = true

private theorem nodup_streamId_eq {xs : List Stage2IoPageTable}
    (hnd : (xs.map Stage2IoPageTable.streamId).Nodup) {a b : Stage2IoPageTable}
    (ha : a ∈ xs) (hb : b ∈ xs) (heq : a.streamId = b.streamId) : a = b := by
  induction xs with
  | nil => cases ha
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (heq ▸ List.mem_map_of_mem hb') hnd.1
    · exact absurd (heq.symm ▸ List.mem_map_of_mem ha') hnd.1
    · exact ih hnd.2 ha' hb'

/-- **Translator completeness (`skip_implies_contract_violation`)**. -/
theorem translateStage2Dma_skip_implies_contract_violation {m : SmmuManifest}
    (hUniqueSid : (m.streams.map Stage2IoPageTable.streamId).Nodup)
    (hDisjIova : ∀ pt ∈ m.streams, RegionsIovaDisjoint pt.regions)
    {sid : StreamId} {iova len : Nat} {acc : DmaAccess} {err : SmmuDmaFault}
    (hErr : translateStage2Dma m sid iova len acc = .error err) :
    ¬ ValidStage2DmaContract m sid iova len acc := by
  rintro ⟨hDeny, hs0, hsw, hlen, pt, hptMem, rfl, reg, hregMem, hlo, hhi, hperm⟩
  have hFindSt : lookupStream m.streams pt.streamId = some pt := by
    cases hf : lookupStream m.streams pt.streamId with
    | none => unfold lookupStream at hf; exact absurd (by simp) (List.find?_eq_none.mp hf pt hptMem)
    | some pt' =>
      obtain ⟨hMem', hEqSid⟩ := lookupStream_some hf
      rw [nodup_streamId_eq hUniqueSid hMem' hptMem hEqSid]
  have hFindReg : lookupDmaRegion pt.regions iova len = some reg := by
    cases hf : lookupDmaRegion pt.regions iova len with
    | none =>
      unfold lookupDmaRegion at hf
      exact absurd (decide_eq_true ⟨hlo, hhi⟩) (List.find?_eq_none.mp hf reg hregMem)
    | some reg' =>
      obtain ⟨hMem', hlo', hhi'⟩ := lookupDmaRegion_some hf
      rw [hDisjIova pt hptMem reg' hMem' reg hregMem (by omega) (by omega)]
  have hSidB : (pt.streamId == 0 || pt.streamId == wildcardStreamId) = false := by simp [hs0, hsw]
  have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [translateStage2Dma, hDeny, hSidB, hLenB, hFindSt, hFindReg, hperm] at hErr

/-! ## 3. Chokepoint SMMU Policy Validation & Adversarial DMA Non-Interference -/

def rangesDisjointB (b1 s1 b2 s2 : Nat) : Bool :=
  decide (b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1 ∨ s1 = 0 ∨ s2 = 0)

def regionTouchesFrame (reg : Stage2DmaRegion) (pfn : Nat) : Bool :=
  decide (reg.paddr.toNat < (pfn + 1) * pageSize ∧ pfn * pageSize < reg.paddr.toNat + reg.size.toNat)

theorem addr_in_region_touches_frame {reg : Stage2DmaRegion} {pa : Nat}
    (hlo : reg.paddr.toNat ≤ pa) (hhi : pa < reg.paddr.toNat + reg.size.toNat) :
    regionTouchesFrame reg (pa / pageSize) = true := by
  unfold regionTouchesFrame pageSize; exact decide_eq_true ⟨by omega, by omega⟩

def checkRegionsIovaDisjoint : List Stage2DmaRegion → Bool
  | [] => true
  | r :: rs =>
    rs.all (fun r' => decide (r.iova.toNat + r.size.toNat ≤ r'.iova.toNat ∨
      r'.iova.toNat + r'.size.toNat ≤ r.iova.toNat)) && checkRegionsIovaDisjoint rs

theorem checkRegionsIovaDisjoint_sound {regions : List Stage2DmaRegion}
    (h : checkRegionsIovaDisjoint regions = true) : RegionsIovaDisjoint regions := by
  induction regions with
  | nil => intro a ha; cases ha
  | cons r rs ih =>
    simp only [checkRegionsIovaDisjoint, Bool.and_eq_true, List.all_eq_true] at h
    intro a ha b hb h1 h2
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · rcases decide_eq_true_eq.mp (h.1 b hb') with hd | hd <;> omega
    · rcases decide_eq_true_eq.mp (h.1 a ha') with hd | hd <;> omega
    · exact ih h.2 a ha' b hb' h1 h2

def roleRegionPermAllowed (pt : Stage2IoPageTable) (reg : Stage2DmaRegion)
    (part : ChokepointFramePartition) : Bool :=
  match pt.role, pt.ownerPd, reg.kind with
  | .ingressNic, .ingress, .ingressRing =>
    part.egressOutboxFrames.all fun pfn => !regionTouchesFrame reg pfn
  | .persistNvme, .persist, .persistWalPool =>
    part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
      part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .egressNic, .txEgress, .egressOutboxRing =>
    reg.perm == .readOnly && part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .displayScanout, .txEgress, .displayFramebuffer =>
    reg.perm == .readOnly &&
      part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
      part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .cameraCsi2, .ingress, .cameraRing =>
    !reg.perm.allowsRead && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .gpu, .ingress, .gpuScratchPool =>
    part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | _, _, _ => false

inductive SmmuRefusalClause where
  | defaultDenyDisabled | spanExceedsBudget | wildcardStreamId | unalignedOrOutOfPoolRegion
  | overlappingCommitFrame | writableCodeOrOutbox | forbiddenRoleRegionPerm | certDigestMismatch
  deriving DecidableEq, Repr

def regionAlignedInPoolB (m : SmmuManifest) (reg : Stage2DmaRegion) : Bool :=
  decide (0 < reg.size.toNat) && decide (reg.iova.toNat + reg.size.toNat < 2 ^ 64) &&
  decide (reg.paddr.toNat + reg.size.toNat < 2 ^ 64) &&
  (reg.iova.toNat % reg.granule.byteSize == 0) && (reg.paddr.toNat % reg.granule.byteSize == 0) &&
  (reg.size.toNat % reg.granule.byteSize == 0) &&
  decide (m.dmaPoolBase.toNat ≤ reg.paddr.toNat ∧
    reg.paddr.toNat + reg.size.toNat ≤ m.dmaPoolBase.toNat + m.dmaPoolSize.toNat)

def spanBudgetOkB (cfg : ChokepointSmmuConfig) : Bool :=
  let m := cfg.manifest
  (cfg.partition.rootServerBootSpan == (m.rootserverPhysStart, m.rootserverPhysEnd)) &&
  decide (m.rootserverPhysStart.toNat < m.rootserverPhysEnd.toNat) &&
  decide (0 < m.dmaPoolSize.toNat) &&
  decide (m.dmaPoolBase.toNat + m.dmaPoolSize.toNat < 2 ^ 64) &&
  decide ((m.rootserverPhysEnd.toNat - m.rootserverPhysStart.toNat) + m.dmaPoolSize.toNat <
    maxRootServerSpanBytes) &&
  decide (stockMicrokitLoaderBase ≤ m.rootserverPhysStart.toNat ∨
    m.rootserverPhysEnd.toNat ≤ stockMicrokitLoaderBase) &&
  rangesDisjointB m.rootserverPhysStart.toNat
    (m.rootserverPhysEnd.toNat - m.rootserverPhysStart.toNat)
    m.dmaPoolBase.toNat m.dmaPoolSize.toNat

def streamsNoWildcardB (m : SmmuManifest) : Bool :=
  decide (m.streams.map Stage2IoPageTable.streamId).Nodup &&
  m.streams.all fun pt => pt.streamId != 0 && pt.streamId != wildcardStreamId

def streamsAlignedInPoolB (m : SmmuManifest) : Bool :=
  m.streams.all fun pt =>
    checkRegionsIovaDisjoint pt.regions && pt.regions.all (regionAlignedInPoolB m)

def commitFramesIsolatedB (cfg : ChokepointSmmuConfig) : Bool :=
  !cfg.partition.commitPrivateFrames.isEmpty &&
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg =>
    (reg.kind != .commitPrivateFrame) &&
    cfg.partition.commitPrivateFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
    cfg.manifest.protectedRanges.all fun pr =>
      pr.classTag != .commitPrivate ||
        rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat

def codeAndOutboxProtectedB (cfg : ChokepointSmmuConfig) : Bool :=
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg =>
    (reg.kind != .pdCodeStackCspace) && (reg.kind != .trngMmio) &&
    cfg.partition.kernelAndCodeFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
    cfg.manifest.protectedRanges.all (fun pr =>
      pr.classTag == .commitPrivate ||
        rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat) &&
    (!(cfg.partition.egressOutboxFrames.any (fun pfn => regionTouchesFrame reg pfn) ||
        reg.kind == .egressOutboxRing) ||
      (pt.role == .egressNic && pt.ownerPd == .txEgress && reg.perm == .readOnly))

def allRolesPermittedB (cfg : ChokepointSmmuConfig) : Bool :=
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg => roleRegionPermAllowed pt reg cfg.partition

/-- Fail-closed validator for a 4-PD Microkit + Stage-2 SMMU chokepoint configuration. -/
def verifyChokepointSmmuConfig (cfg : ChokepointSmmuConfig) :
    Except SmmuRefusalClause Unit :=
  if !cfg.manifest.defaultDeny then .error .defaultDenyDisabled
  else if !spanBudgetOkB cfg then .error .spanExceedsBudget
  else if !streamsNoWildcardB cfg.manifest then .error .wildcardStreamId
  else if !streamsAlignedInPoolB cfg.manifest then .error .unalignedOrOutOfPoolRegion
  else if !commitFramesIsolatedB cfg then .error .overlappingCommitFrame
  else if !codeAndOutboxProtectedB cfg then .error .writableCodeOrOutbox
  else if !allRolesPermittedB cfg then .error .forbiddenRoleRegionPerm
  else .ok ()

/-- Declarative semantic safety specification of a valid 4-PD Stage-2 SMMU configuration. -/
structure ChokepointSmmuSafeSpec (cfg : ChokepointSmmuConfig) : Prop where
  defaultDeny : cfg.manifest.defaultDeny = true
  spanOk : cfg.partition.rootServerBootSpan =
      (cfg.manifest.rootserverPhysStart, cfg.manifest.rootserverPhysEnd) ∧
    cfg.manifest.rootserverPhysStart.toNat < cfg.manifest.rootserverPhysEnd.toNat ∧
    0 < cfg.manifest.dmaPoolSize.toNat ∧
    cfg.manifest.dmaPoolBase.toNat + cfg.manifest.dmaPoolSize.toNat < 2 ^ 64 ∧
    (cfg.manifest.rootserverPhysEnd.toNat - cfg.manifest.rootserverPhysStart.toNat) +
      cfg.manifest.dmaPoolSize.toNat < maxRootServerSpanBytes ∧
    (stockMicrokitLoaderBase ≤ cfg.manifest.rootserverPhysStart.toNat ∨
      cfg.manifest.rootserverPhysEnd.toNat ≤ stockMicrokitLoaderBase) ∧
    rangesDisjointB cfg.manifest.rootserverPhysStart.toNat
      (cfg.manifest.rootserverPhysEnd.toNat - cfg.manifest.rootserverPhysStart.toNat)
      cfg.manifest.dmaPoolBase.toNat cfg.manifest.dmaPoolSize.toNat = true
  noWildcard : (cfg.manifest.streams.map Stage2IoPageTable.streamId).Nodup ∧
    ∀ pt ∈ cfg.manifest.streams, pt.streamId ≠ 0 ∧ pt.streamId ≠ wildcardStreamId
  alignedInPool : ∀ pt ∈ cfg.manifest.streams,
    checkRegionsIovaDisjoint pt.regions = true ∧
    ∀ reg ∈ pt.regions, regionAlignedInPoolB cfg.manifest reg = true
  commitIsolated : cfg.partition.commitPrivateFrames ≠ [] ∧
    ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions,
      reg.kind ≠ .commitPrivateFrame ∧
      (∀ pfn ∈ cfg.partition.commitPrivateFrames, regionTouchesFrame reg pfn = false) ∧
      (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag = .commitPrivate →
        rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true)
  codeAndOutboxSafe : ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions,
    reg.kind ≠ .pdCodeStackCspace ∧ reg.kind ≠ .trngMmio ∧
    (∀ pfn ∈ cfg.partition.kernelAndCodeFrames, regionTouchesFrame reg pfn = false) ∧
    (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag ≠ .commitPrivate →
      rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) ∧
    (((∃ pfn ∈ cfg.partition.egressOutboxFrames, regionTouchesFrame reg pfn = true) ∨
        reg.kind = .egressOutboxRing) →
      pt.role = .egressNic ∧ pt.ownerPd = .txEgress ∧ reg.perm = .readOnly)
  roleMatrix : ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions,
    roleRegionPermAllowed pt reg cfg.partition = true

private theorem commitFramesIsolatedB_iff (cfg : ChokepointSmmuConfig) :
    commitFramesIsolatedB cfg = true ↔
      cfg.partition.commitPrivateFrames ≠ [] ∧
        ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions,
          reg.kind ≠ .commitPrivateFrame ∧
          (∀ pfn ∈ cfg.partition.commitPrivateFrames, regionTouchesFrame reg pfn = false) ∧
          (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag = .commitPrivate →
            rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) := by
  unfold commitFramesIsolatedB; rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hne, hall⟩
    refine ⟨by cases hc : cfg.partition.commitPrivateFrames <;> simp_all, fun pt hpt reg hreg => ?_⟩
    have hr := List.all_eq_true.mp (hall pt hpt) reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true'] at hr
    refine ⟨hr.1.1, hr.1.2, fun pr hpr htag => ?_⟩
    have hp := hr.2 pr hpr; simp [htag] at hp; exact hp
  · rintro ⟨hne, hall⟩
    refine ⟨by cases hc : cfg.partition.commitPrivateFrames <;> simp_all, fun pt hpt => ?_⟩
    rw [List.all_eq_true]; intro reg hreg
    obtain ⟨hk, hc, hp⟩ := hall pt hpt reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true']
    refine ⟨⟨hk, hc⟩, fun pr hpr => ?_⟩
    by_cases htag : pr.classTag = .commitPrivate <;> simp [htag, hp pr hpr]

private theorem codeAndOutboxProtectedB_iff (cfg : ChokepointSmmuConfig) :
    codeAndOutboxProtectedB cfg = true ↔
      ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions,
        reg.kind ≠ .pdCodeStackCspace ∧ reg.kind ≠ .trngMmio ∧
        (∀ pfn ∈ cfg.partition.kernelAndCodeFrames, regionTouchesFrame reg pfn = false) ∧
        (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag ≠ .commitPrivate →
          rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) ∧
        (((∃ pfn ∈ cfg.partition.egressOutboxFrames, regionTouchesFrame reg pfn = true) ∨
            reg.kind = .egressOutboxRing) →
          pt.role = .egressNic ∧ pt.ownerPd = .txEgress ∧ reg.perm = .readOnly) := by
  unfold codeAndOutboxProtectedB; rw [List.all_eq_true]
  constructor
  · intro h pt hpt reg hreg
    have hr := List.all_eq_true.mp (h pt hpt) reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, beq_iff_eq] at hr
    obtain ⟨⟨⟨⟨hk1, hk2⟩, hkern⟩, hprot⟩, hout⟩ := hr
    refine ⟨hk1, hk2, hkern, fun pr hpr hne => (hprot pr hpr).resolve_left hne, fun hor => ?_⟩
    rcases hout with hnot | hok
    · exfalso
      simp only [Bool.or_eq_false_iff, List.any_eq_false, beq_eq_false_iff_ne, Bool.not_eq_true] at hnot
      rcases hor with ⟨pfn, hpfn, ht⟩ | hkind
      · exact absurd ht (by rw [hnot.1 pfn hpfn]; decide)
      · exact hnot.2 hkind
    · exact ⟨hok.1.1, hok.1.2, hok.2⟩
  · intro h pt hpt; rw [List.all_eq_true]; intro reg hreg
    obtain ⟨hk1, hk2, hkern, hprot, hout⟩ := h pt hpt reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨hk1, hk2⟩, hkern⟩, fun pr hpr => ?_⟩, ?_⟩
    · by_cases htag : pr.classTag = .commitPrivate <;> simp [htag, hprot pr hpr]
    · cases hcond : (cfg.partition.egressOutboxFrames.any (fun pfn => regionTouchesFrame reg pfn) ||
          reg.kind == .egressOutboxRing)
      · rfl
      · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hcond
        obtain ⟨h1, h2, h3⟩ := hout hcond; simp [h1, h2, h3]

theorem verifyChokepointSmmuConfig_sound {cfg : ChokepointSmmuConfig}
    (h : verifyChokepointSmmuConfig cfg = .ok ()) : ChokepointSmmuSafeSpec cfg := by
  unfold verifyChokepointSmmuConfig at h
  cases h1 : cfg.manifest.defaultDeny; · simp [h1] at h
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h2 : spanBudgetOkB cfg; · simp [h2] at h
  simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h3 : streamsNoWildcardB cfg.manifest; · simp [h3] at h
  simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h4 : streamsAlignedInPoolB cfg.manifest; · simp [h4] at h
  simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h5 : commitFramesIsolatedB cfg; · simp [h5] at h
  simp only [h5, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h6 : codeAndOutboxProtectedB cfg; · simp [h6] at h
  simp only [h6, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases h7 : allRolesPermittedB cfg; · simp [h7] at h
  exact ⟨h1,
    by simpa [spanBudgetOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h2,
    by simpa [streamsNoWildcardB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] using h3,
    by simpa [streamsAlignedInPoolB, Bool.and_eq_true, List.all_eq_true] using h4,
    (commitFramesIsolatedB_iff cfg).mp h5, (codeAndOutboxProtectedB_iff cfg).mp h6,
    by simpa [allRolesPermittedB, List.all_eq_true] using h7⟩
theorem verifyChokepointSmmuConfig_complete {cfg : ChokepointSmmuConfig}
    (h : ChokepointSmmuSafeSpec cfg) : verifyChokepointSmmuConfig cfg = .ok () := by
  have h2 : spanBudgetOkB cfg = true := by
    simpa [spanBudgetOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h.spanOk
  have h3 : streamsNoWildcardB cfg.manifest = true := by
    simpa [streamsNoWildcardB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] using h.noWildcard
  have h4 : streamsAlignedInPoolB cfg.manifest = true := by
    simpa [streamsAlignedInPoolB, Bool.and_eq_true, List.all_eq_true] using h.alignedInPool
  have h5 := (commitFramesIsolatedB_iff cfg).mpr h.commitIsolated
  have h6 := (codeAndOutboxProtectedB_iff cfg).mpr h.codeAndOutboxSafe
  have h7 : allRolesPermittedB cfg = true := by simpa [allRolesPermittedB, List.all_eq_true] using h.roleMatrix
  simp [verifyChokepointSmmuConfig, h.defaultDeny, h2, h3, h4, h5, h6, h7]
inductive PeripheralDmaOp where
  | read (sid : StreamId) (iova len : Nat) | write (sid : StreamId) (iova : Nat) (payload : ByteArray)
  deriving DecidableEq
def writePhys (mem : Nat → UInt8) (pa : Nat) (payload : ByteArray) : Nat → UInt8 :=
  fun a => if pa ≤ a ∧ a < pa + payload.size then payload.data[a - pa]?.getD (mem a) else mem a

def execStage2DmaOp (m : SmmuManifest) (mem : Nat → UInt8) :
    PeripheralDmaOp → (Nat → UInt8) × Option ByteArray
  | .read sid iova len =>
    match translateStage2Dma m sid iova len .dmaRead with
    | .ok pa => (mem, some (readPhys mem pa len)) | .error _ => (mem, none)
  | .write sid iova payload =>
    match translateStage2Dma m sid iova payload.size .dmaWrite with
    | .ok pa => (writePhys mem pa payload, none) | .error _ => (mem, none)

def execStage2DmaBurst (m : SmmuManifest) (mem : Nat → UInt8) :
    List PeripheralDmaOp → (Nat → UInt8) × List (Option ByteArray)
  | [] => (mem, [])
  | op :: ops =>
    let (mem₁, obs₁) := execStage2DmaOp m mem op
    let (mem₂, obsRest) := execStage2DmaBurst m mem₁ ops
    (mem₂, obs₁ :: obsRest)

private theorem execStage2DmaOp_preserves_and_noninterfering {cfg : ChokepointSmmuConfig}
    (hSafe : ChokepointSmmuSafeSpec cfg) (op : PeripheralDmaOp) (mem₁ mem₂ : Nat → UInt8)
    (hAgree : ∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames →
      pa / pageSize ∉ cfg.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa) :
    (∀ pa, (pa / pageSize ∈ cfg.partition.commitPrivateFrames ∨
        pa / pageSize ∈ cfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ cfg.partition.egressOutboxFrames) →
      (execStage2DmaOp cfg.manifest mem₁ op).1 pa = mem₁ pa) ∧
    (execStage2DmaOp cfg.manifest mem₁ op).2 = (execStage2DmaOp cfg.manifest mem₂ op).2 ∧
    (∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames →
      pa / pageSize ∉ cfg.partition.kernelAndCodeFrames →
      (execStage2DmaOp cfg.manifest mem₁ op).1 pa = (execStage2DmaOp cfg.manifest mem₂ op).1 pa) := by
  cases op with
  | read sid iova len =>
    dsimp only [execStage2DmaOp]
    cases ht : translateStage2Dma cfg.manifest sid iova len .dmaRead with
    | error _ => exact ⟨fun _ _ => rfl, rfl, hAgree⟩
    | ok basePa =>
      obtain ⟨-, -, -, -, pt, hpt, -, reg, hreg, hlo, hhi, -, rfl⟩ := translateStage2Dma_ok ht
      refine ⟨fun _ _ => rfl, ?_, hAgree⟩
      dsimp only []; congr 1; unfold readPhys
      refine congrArg Obend.Digest.Cshake256.Native.bytesOfList (List.map_congr_left fun i hi => ?_)
      have hiLt := List.mem_range.mp hi
      have hTouch : regionTouchesFrame reg ((reg.paddr.toNat + (iova - reg.iova.toNat) + i) / pageSize) = true :=
        addr_in_region_touches_frame (by omega) (by omega)
      have hNotCommit : (reg.paddr.toNat + (iova - reg.iova.toNat) + i) / pageSize ∉
          cfg.partition.commitPrivateFrames := fun hMem => by
        rw [(hSafe.commitIsolated.2 pt hpt reg hreg).2.1 _ hMem] at hTouch; cases hTouch
      have hNotKern : (reg.paddr.toNat + (iova - reg.iova.toNat) + i) / pageSize ∉
          cfg.partition.kernelAndCodeFrames := fun hMem => by
        rw [(hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.1 _ hMem] at hTouch; cases hTouch
      exact hAgree _ hNotCommit hNotKern
  | write sid iova payload =>
    dsimp only [execStage2DmaOp]
    cases ht : translateStage2Dma cfg.manifest sid iova payload.size .dmaWrite with
    | error _ => exact ⟨fun _ _ => rfl, rfl, hAgree⟩
    | ok basePa =>
      obtain ⟨-, -, -, -, pt, hpt, -, reg, hreg, hlo, hhi, hperm, rfl⟩ := translateStage2Dma_ok ht
      refine ⟨fun pa hProt => ?_, rfl, fun pa hnc hnk => ?_⟩
      · dsimp only []; unfold writePhys
        by_cases hIn : reg.paddr.toNat + (iova - reg.iova.toNat) ≤ pa ∧
            pa < reg.paddr.toNat + (iova - reg.iova.toNat) + payload.size
        · exfalso
          have hTouch : regionTouchesFrame reg (pa / pageSize) = true :=
            addr_in_region_touches_frame (by omega) (by omega)
          rcases hProt with hCom | hKern | hOut
          · rw [(hSafe.commitIsolated.2 pt hpt reg hreg).2.1 _ hCom] at hTouch; cases hTouch
          · rw [(hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.1 _ hKern] at hTouch; cases hTouch
          · have hRo := ((hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.2.2 (.inl ⟨_, hOut, hTouch⟩)).2.2
            rw [hRo] at hperm; cases hperm
        · simp [hIn]
      · dsimp only []; unfold writePhys
        by_cases hIn : reg.paddr.toNat + (iova - reg.iova.toNat) ≤ pa ∧
            pa < reg.paddr.toNat + (iova - reg.iova.toNat) + payload.size
        · simp only [hIn, and_self, ↓reduceIte]
          cases payload.data[pa - (reg.paddr.toNat + (iova - reg.iova.toNat))]? with
          | some _ => rfl | none => exact hAgree pa hnc hnk
        · simp [hIn, hAgree pa hnc hnk]

/-- **Adversarial Peripheral DMA Integrity & Read Non-Interference**:
Arbitrary peripheral DMA bursts across all `StreamId`s leave `commit-pd` private frames, kernel
CSpace/page-table/code frames, and finalized `tx-egress-pd` outbox frames untouched
(`mem' pa = mem pa`), and `commit-pd` private bytes cannot be DMA-read (`obs₁ = obs₂`)! -/
theorem dma_burst_preserves_private_pd_frames {cfg : ChokepointSmmuConfig}
    (hValid : verifyChokepointSmmuConfig cfg = .ok ())
    (ops : List PeripheralDmaOp) (mem₁ mem₂ : Nat → UInt8)
    (hAgree : ∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames →
      pa / pageSize ∉ cfg.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa) :
    (∀ pa, (pa / pageSize ∈ cfg.partition.commitPrivateFrames ∨
        pa / pageSize ∈ cfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ cfg.partition.egressOutboxFrames) →
      (execStage2DmaBurst cfg.manifest mem₁ ops).1 pa = mem₁ pa) ∧
    (execStage2DmaBurst cfg.manifest mem₁ ops).2 =
      (execStage2DmaBurst cfg.manifest mem₂ ops).2 := by
  have hSafe := verifyChokepointSmmuConfig_sound hValid
  induction ops generalizing mem₁ mem₂ with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons op ops ih =>
    simp only [execStage2DmaBurst]
    obtain ⟨hPres₁, hObs₁, hAgree₁⟩ :=
      execStage2DmaOp_preserves_and_noninterfering hSafe op mem₁ mem₂ hAgree
    obtain ⟨hPresRest, hObsRest⟩ := ih (execStage2DmaOp cfg.manifest mem₁ op).1
      (execStage2DmaOp cfg.manifest mem₂ op).1 hAgree₁
    refine ⟨fun pa hProt => (hPresRest pa hProt).trans (hPres₁ pa hProt), ?_⟩
    rw [hObs₁, hObsRest]

/-! ## 4. Coupling Stage-2 DMA Bursts to `Sel4MicrokitKernel.ValidVerifierLoop` -/

def dmaOpToKernelEvents : PeripheralDmaOp → List KEvent
  | .read _ _ _ => []
  | .write sid iova payload =>
    (List.range payload.size).map fun i => .dma sid.toNat (iova + i) (payload.data[i]?.getD 0)

def dmaBurstToKernelEvents (ops : List PeripheralDmaOp) : List KEvent :=
  ops.flatMap dmaOpToKernelEvents

theorem dmaBurstToKernelEvents_actor_ne {ops : List PeripheralDmaOp} {vpd : PdId} :
    ∀ ev ∈ dmaBurstToKernelEvents ops, ev.actor ≠ some vpd := by
  intro ev hev
  obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hev
  cases op with
  | read _ _ _ => cases hop
  | write sid iova payload => obtain ⟨i, -, rfl⟩ := List.mem_map.mp hop; simp [KEvent.actor]

def SmmuWriteProtected (k : KState) (vpd : PdId) (protectedWriteFrames : List Nat) : Prop :=
  (∀ i n, capAt k.cspace i = some n → n.cap.rights.write = true →
    (∃ f ∈ protectedWriteFrames, n.cap.obj.touches f = true) → n.owner = vpd) ∧
  (∀ e ∈ k.maps, ∀ sid, e.space = .dev sid → e.writable = true → e.pfn ∉ protectedWriteFrames)

theorem smmuWriteProtected_step {k : KState} {vpd : PdId} {frames : List Nat} {ev : KEvent}
    (hK : KInv k) (hProt : SmmuWriteProtected k vpd frames) (hAdv : ev.actor ≠ some vpd) :
    SmmuWriteProtected (kstep k ev) vpd frames := by
  obtain ⟨hCaps, hMaps⟩ := hProt
  rcases kstep_frame k ev with ⟨pd, call, k', rfl, hk, hstep⟩ | ⟨hc, hm⟩
  · rw [hstep]
    have hpd : pd ≠ vpd := fun e => hAdv (by simp [KEvent.actor, e])
    obtain ⟨-, -, hE⟩ := ksyscall_effect hk
    rcases hE with ⟨src, n, dst, cap, hn, hown, hle, hcs, hm⟩ | ⟨hS, hm⟩ |
      ⟨hcs, e, hm, hown, -, f, a, hf, hfo, hfobj, hfw, -, -, -⟩ | ⟨hcs, hsub⟩
    · refine ⟨?_, hm ▸ hMaps⟩
      intro i x hx xw ⟨fr, hfr, htouch⟩; rw [hcs] at hx
      rcases capAt_mintCap hx with hx | rfl
      · exact hCaps i x hx xw ⟨fr, hfr, htouch⟩
      · obtain ⟨ho, hrs, -⟩ := Cap.le_iff.mp hle
        exact absurd ((hCaps src n hn ((Rights.sub_iff.mp hrs).2.1 xw)
          ⟨fr, hfr, CapObj.touches_mono ho htouch⟩).symm.trans hown) (fun e => hpd e.symm)
    · have hin : ∀ e ∈ k'.maps, e ∈ k.maps := fun e he => (List.mem_filter.mp (hm ▸ he)).1
      exact ⟨fun i x hx => hCaps i x ((hS hK.1).1 i x hx), fun e he => hMaps e (hin e he)⟩
    · refine ⟨hcs ▸ hCaps, ?_⟩
      intro x hx sid hs hw hmem; rw [hm] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hft : f.cap.obj.touches x.pfn = true := by rw [hfobj]; simp [CapObj.touches]
        exact hpd (hown.symm.trans (hfo.symm.trans (hCaps _ f hf (hfw hw) ⟨x.pfn, hmem, hft⟩)))
      · exact hMaps x hx sid hs hw hmem
    · exact ⟨hcs ▸ hCaps, fun e he => hMaps e (hsub e he)⟩
  · exact ⟨hc ▸ hCaps, hm ▸ hMaps⟩

theorem smmuWriteProtected_run {k : KState} {vpd : PdId} {frames : List Nat} (evs : List KEvent)
    (hK : KInv k) (hProt : SmmuWriteProtected k vpd frames)
    (hAdv : ∀ ev ∈ evs, ev.actor ≠ some vpd) :
    SmmuWriteProtected (runK k evs) vpd frames := by
  induction evs generalizing k with
  | nil => exact hProt
  | cons ev evs ih =>
    exact ih (kstep_inv hK ev) (smmuWriteProtected_step hK hProt (hAdv ev List.mem_cons_self))
      (fun e he => hAdv e (List.mem_cons_of_mem _ he))

theorem smmuWriteProtected_dma_preserves_mem {k : KState} {vpd : PdId} {frames : List Nat}
    (hProt : SmmuWriteProtected k vpd frames) (ops : List PeripheralDmaOp)
    (pa : Nat) (hpa : pa / pageSize ∈ frames) :
    (runK k (dmaBurstToKernelEvents ops)).mem pa = k.mem pa := by
  have key : ∀ (evs : List KEvent) (k' : KState),
      k'.maps = k.maps → (∀ ev ∈ evs, ∃ s v b, ev = .dma s v b) →
      (runK k' evs).mem pa = k'.mem pa := by
    intro evs; induction evs with
    | nil => intro _ _ _; rfl
    | cons ev evs ih =>
      intro k' hm hall
      obtain ⟨sid, va, val, rfl⟩ := hall ev List.mem_cons_self
      have hm1 : (kstep k' (.dma sid va val)).maps = k'.maps :=
        (storeVia_frame k' (.dev sid) va val).2.1
      have hmem1 : (kstep k' (.dma sid va val)).mem pa = k'.mem pa := by
        by_cases hEq : (kstep k' (.dma sid va val)).mem pa = k'.mem pa
        · exact hEq
        · obtain ⟨sp, e, hsp, he, hes, hw, hpfn⟩ := kstep_mem_changed hEq
          cases hsp; exact absurd (hpfn ▸ hpa) (hProt.2 e (hm ▸ he) sid hes hw)
      exact (ih _ (hm1.trans hm) (fun e he => hall e (List.mem_cons_of_mem _ he))).trans hmem1
  refine key (dmaBurstToKernelEvents ops) k rfl fun ev hev => ?_
  obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hev
  cases op with
  | read _ _ _ => cases hop
  | write sid iova payload => obtain ⟨i, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, _, _, rfl⟩
structure SmmuVerifierTurn where
  preEvents : List KEvent
  preDma : List PeripheralDmaOp
  midEvents : List KEvent
  midDma : List PeripheralDmaOp
  ringAtCopy : ByteArray
  out : OutboxTurn
  grain : GrainId
  slot : Nat
  need : UInt64
def SmmuVerifierTurn.toVerifierTurn (t : SmmuVerifierTurn) : VerifierTurn :=
  ⟨t.preEvents ++ dmaBurstToKernelEvents t.preDma, t.midEvents ++ dmaBurstToKernelEvents t.midDma,
    t.ringAtCopy, t.out, t.grain, t.slot, t.need⟩
def ValidSmmuVerifierLoop (smmuCfg : ChokepointSmmuConfig) (P : Protocol)
    (part : SeL4MicrokitPartition) (inCfg : IngressCfg) :
    LoopState → List SmmuVerifierTurn → LoopState → Prop
  | s, [], f =>
    f = s ∧ Reach P s.sent ∧ checkMicrokitIsolation part = true ∧
      verifyChokepointSmmuConfig smmuCfg = .ok ()
  | s, t :: ts, f =>
    verifyChokepointSmmuConfig smmuCfg = .ok () ∧
    (∀ ev ∈ t.preEvents, ev.actor ≠ some inCfg.vpd) ∧ (∀ ev ∈ t.midEvents, ev.actor ≠ some inCfg.vpd) ∧
    readVia (copyState s.kernel t.toVerifierTurn) inCfg.vpd inCfg.sharedV inCfg.len = some t.ringAtCopy ∧
    (translate (copyState s.kernel t.toVerifierTurn).maps (.cpu inCfg.vpd) inCfg.privV true).isSome = true ∧
    readVia (dispatchState inCfg s.kernel t.toVerifierTurn) inCfg.vpd (dispatchVaddr inCfg)
      inCfg.len = some t.out.req.spsc.sharedRingBeforeCopy ∧
    Reach P s.sent ∧ SentSteps P s.sent t.out.nextSent ∧
    ∃ (h₁ : PowerboxHost) (stMid st₁ : OutboxState),
      Obend.Polis.GrainPowerbox.stepPowerboxHost s.host (invokeOf t.toVerifierTurn) = some h₁ ∧
      stepOutbox P part t.out.nextSent s.outbox t.out.req = some stMid ∧
      (match t.out.reconcileCert? with
       | none => st₁ = stMid
       | some cert => reconcileEscrowsWithCert P t.out.nextSent cert stMid = some st₁) ∧
      ValidSmmuVerifierLoop smmuCfg P part inCfg
        ⟨dispatchState inCfg s.kernel t.toVerifierTurn, t.out.nextSent, st₁, h₁⟩ ts f

theorem validSmmuVerifierLoop_to_kernelLoop {smmuCfg : ChokepointSmmuConfig} {P : Protocol}
    {part : SeL4MicrokitPartition} {inCfg : IngressCfg}
    {turns : List SmmuVerifierTurn} {s f : LoopState}
    (h : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) :
    verifyChokepointSmmuConfig smmuCfg = .ok () ∧
      ValidVerifierLoop P part inCfg s (turns.map SmmuVerifierTurn.toVerifierTurn) f := by
  induction turns generalizing s with
  | nil =>
    simp only [ValidSmmuVerifierLoop, List.map_nil, ValidVerifierLoop] at h ⊢
    exact ⟨h.2.2.2, h.1, h.2.1, h.2.2.1⟩
  | cons t ts ih =>
    simp only [ValidSmmuVerifierLoop] at h
    obtain ⟨hCfg, hPreC, hMidC, hRing, hCopy, hDisp, hR, hSt, h₁, stMid, st₁, hPb, hOb, hRec, hRest⟩ := h
    exact ⟨hCfg,
      fun ev hev => (List.mem_append.mp hev).elim (hPreC ev) (dmaBurstToKernelEvents_actor_ne ev),
      fun ev hev => (List.mem_append.mp hev).elim (hMidC ev) (dmaBurstToKernelEvents_actor_ne ev),
      hRing, hCopy, hDisp, hR, hSt, h₁, stMid, st₁, hPb, hOb, hRec, (ih hRest).2⟩

theorem validSmmuVerifierLoop_preserves_writeProtected {smmuCfg : ChokepointSmmuConfig}
    {P : Protocol} {part : SeL4MicrokitPartition} {inCfg : IngressCfg} {frames : List Nat}
    {turns : List SmmuVerifierTurn} {s f : LoopState}
    (hK : KInv s.kernel) (hProt : SmmuWriteProtected s.kernel inCfg.vpd frames)
    (h : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) :
    SmmuWriteProtected f.kernel inCfg.vpd frames := by
  induction turns generalizing s with
  | nil => simp only [ValidSmmuVerifierLoop] at h; rw [h.1]; exact hProt
  | cons t ts ih =>
    simp only [ValidSmmuVerifierLoop] at h
    obtain ⟨-, hPreC, hMidC, -, -, -, -, -, h₁, stMid, st₁, -, -, -, hRest⟩ := h
    have hPreAll : ∀ ev ∈ t.toVerifierTurn.pre, ev.actor ≠ some inCfg.vpd := fun ev hev =>
      (List.mem_append.mp hev).elim (hPreC ev) (dmaBurstToKernelEvents_actor_ne ev)
    have hMidAll : ∀ ev ∈ t.toVerifierTurn.mid, ev.actor ≠ some inCfg.vpd := fun ev hev =>
      (List.mem_append.mp hev).elim (hMidC ev) (dmaBurstToKernelEvents_actor_ne ev)
    have hProt₁ := smmuWriteProtected_run t.toVerifierTurn.pre hK hProt hPreAll
    have hK₁ := runK_inv hK t.toVerifierTurn.pre
    obtain ⟨hc, hm, -⟩ := copyVia_frame (copyState s.kernel t.toVerifierTurn)
      inCfg.vpd inCfg.sharedV inCfg.privV inCfg.len
    have hK₂ : KInv (ingressCopy inCfg (copyState s.kernel t.toVerifierTurn)) := kstep_inv hK₁ _
    exact ih (runK_inv hK₂ t.toVerifierTurn.mid)
      (smmuWriteProtected_run t.toVerifierTurn.mid hK₂ ⟨hc ▸ hProt₁.1, hm ▸ hProt₁.2⟩ hMidAll) hRest

/-- **Multi-turn SMMU + `seL4` Microkit Verifier Loop Safety (`smmu_verifier_loop_dma_safe`)**. -/
theorem smmu_verifier_loop_dma_safe {smmuCfg : ChokepointSmmuConfig} {P : Protocol}
    {part : SeL4MicrokitPartition} {inCfg : IngressCfg}
    {turns : List SmmuVerifierTurn} {s f : LoopState} {da₀ : Nat}
    (hK : KInv s.kernel) (hS : KSched s.kernel)
    (hP₀ : translate s.kernel.maps (.cpu inCfg.vpd) inCfg.privV true = some da₀)
    (hEx : Exclusive s.kernel inCfg.vpd (da₀ / pageSize))
    (hProt : SmmuWriteProtected s.kernel inCfg.vpd
      (smmuCfg.partition.kernelAndCodeFrames ++ smmuCfg.partition.egressOutboxFrames))
    (hClean : s.outbox.dispatchedActuations = []) (hAcc : Accountable s.host)
    (hLoop : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) :
    (KInv f.kernel ∧ Exclusive f.kernel inCfg.vpd (da₀ / pageSize) ∧ KSched f.kernel ∧
      SmmuWriteProtected f.kernel inCfg.vpd
        (smmuCfg.partition.kernelAndCodeFrames ++ smmuCfg.partition.egressOutboxFrames) ∧
      ∀ i n, capAt f.kernel.cspace i = some n →
        ∃ j r, capAt s.kernel.cspace j = some r ∧ n.cap.le r.cap = true) ∧
    (∀ t ∈ turns, ∀ mem : Nat → UInt8, ∀ pa,
      (pa / pageSize ∈ smmuCfg.partition.commitPrivateFrames ∨
        pa / pageSize ∈ smmuCfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ smmuCfg.partition.egressOutboxFrames) →
      (execStage2DmaBurst smmuCfg.manifest mem t.midDma).1 pa = mem pa) ∧
    Accountable f.host ∧ Sel4CapDlNonInterfering part ∧
    (f.outbox.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    ∀ a ∈ f.outbox.dispatchedActuations,
      Finalized P f.sent a.view a.chain ∧
      (∀ (vCanon : Nat) (cCanon : Chain),
        Finalized P f.sent vCanon cCanon → a.view ≤ vCanon → a.chain <+: cCanon) ∧
      ∃ t ∈ turns, t.out.req.effectClass = .irreversibleActuation ∧
        a.nullifierId = t.out.req.nullifierId ∧ a.dispatchedPayload = t.ringAtCopy ∧
        ∃ entry ∈ f.host.audit, entry.whoInvoked = .grain t.grain ∧
          entry.actionDigest = actionDigest a.dispatchedPayload := by
  obtain ⟨hValidCfg, hVLoop⟩ := validSmmuVerifierLoop_to_kernelLoop hLoop
  obtain ⟨⟨hKFin, hExFin, hSFin, hAmp⟩, hAccFin, hIso, hNodup, hActs⟩ :=
    sel4_microkit_verifier_loop_safe hK hS hP₀ hEx hClean hAcc hVLoop
  refine ⟨⟨hKFin, hExFin, hSFin, validSmmuVerifierLoop_preserves_writeProtected hK hProt hLoop, hAmp⟩,
    fun t _ mem pa hFrame =>
      (dma_burst_preserves_private_pd_frames hValidCfg t.midDma mem mem (fun _ _ _ => rfl)).1 pa hFrame,
    hAccFin, hIso, hNodup, fun a ha => ?_⟩
  obtain ⟨hFin, hCanon, tv, htv, hEff, hNull, hPay, entry, hEnt, hWho, hDig⟩ := hActs a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htv
  exact ⟨hFin, hCanon, t, ht, hEff, hNull, hPay, entry, hEnt, hWho, hDig⟩

/-! ## 5. 256-Bit `OBEND.SHE.SMMU_MANIFEST/v1` Wire Commitment & Scoped `CollisionAmong` Binding -/

def u32ToBe4 (w : UInt32) : List UInt8 := be 4 w.toNat
theorem u32ToBe4_length (w : UInt32) : (u32ToBe4 w).length = 4 := length_be ..
theorem u32ToBe4_injective {w₁ w₂ : UInt32} (h : u32ToBe4 w₁ = u32ToBe4 w₂) : w₁ = w₂ :=
  UInt32.toNat_inj.mp (be_injective (w := 4) w₁.toBitVec.isLt w₂.toBitVec.isLt h)

private theorem flatMap_fixed_injective {α : Type} (f : α → List UInt8) (k : Nat) (hkPos : 0 < k)
    (hk : ∀ x, (f x).length = k) (hinj : ∀ {x y}, f x = f y → x = y) :
    ∀ {xs ys : List α}, xs.flatMap f = ys.flatMap f → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have hl : ((y :: ys).flatMap f).length = 0 := by rw [← h]; rfl
    simp only [List.flatMap_cons, List.length_append, hk y] at hl; omega
  | x :: xs, [], h => by
    have hl : ((x :: xs).flatMap f).length = 0 := by rw [h]; rfl
    simp only [List.flatMap_cons, List.length_append, hk x] at hl; omega
  | a :: as, b :: bs, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h ((hk a).trans (hk b).symm)
    rw [hinj h1, flatMap_fixed_injective f k hkPos hk hinj h2]

def encodeProtectedRange17 (pr : ProtectedPhysRange) : List UInt8 :=
  pr.classTag.tagByte :: (u64ToBe8 pr.basePaddr ++ u64ToBe8 pr.size)
theorem encodeProtectedRange17_length (pr : ProtectedPhysRange) :
    (encodeProtectedRange17 pr).length = 17 := by simp [encodeProtectedRange17, u64ToBe8_length]
theorem encodeProtectedRange17_injective {a b : ProtectedPhysRange}
    (h : encodeProtectedRange17 a = encodeProtectedRange17 b) : a = b := by
  obtain ⟨hTag, hRest⟩ := List.cons.inj h
  obtain ⟨hBase, hSz⟩ := List.append_inj hRest ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  cases a; cases b; simp only [ProtectedPhysRange.mk.injEq]
  exact ⟨ProtectedFrameClass.tagByte_injective hTag, u64ToBe8_injective hBase, u64ToBe8_injective hSz⟩

def encodeProtectedRanges (xs : List ProtectedPhysRange) : List UInt8 :=
  be 8 xs.length ++ xs.flatMap encodeProtectedRange17
theorem encodeProtectedRanges_injective {xs ys : List ProtectedPhysRange}
    (h : encodeProtectedRanges xs = encodeProtectedRanges ys) : xs = ys := by
  obtain ⟨-, hBody⟩ := List.append_inj h (by simp only [length_be])
  exact flatMap_fixed_injective encodeProtectedRange17 17 (by decide)
    encodeProtectedRange17_length encodeProtectedRange17_injective hBody

def encodeDmaRegion27 (r : Stage2DmaRegion) : List UInt8 :=
  u64ToBe8 r.iova ++ (u64ToBe8 r.paddr ++ (u64ToBe8 r.size ++
    [r.granule.tagByte, r.perm.tagByte, r.kind.tagByte]))
theorem encodeDmaRegion27_length (r : Stage2DmaRegion) :
    (encodeDmaRegion27 r).length = 27 := by simp [encodeDmaRegion27, u64ToBe8_length]
theorem encodeDmaRegion27_injective {a b : Stage2DmaRegion}
    (h : encodeDmaRegion27 a = encodeDmaRegion27 b) : a = b := by
  obtain ⟨hIova, h1⟩ := List.append_inj h ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  obtain ⟨hPa, h2⟩ := List.append_inj h1 ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  obtain ⟨hSz, hTags⟩ := List.append_inj h2 ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  simp only [List.cons.injEq, and_true] at hTags; cases a; cases b; simp only [Stage2DmaRegion.mk.injEq]
  exact ⟨u64ToBe8_injective hIova, u64ToBe8_injective hPa, u64ToBe8_injective hSz,
    PageGranule.tagByte_injective hTags.1, IoPerm.tagByte_injective hTags.2.1,
    DmaRegionKind.tagByte_injective hTags.2.2⟩

private theorem flatMap_dmaRegion27_length (rs : List Stage2DmaRegion) :
    (rs.flatMap encodeDmaRegion27).length = 27 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.flatMap_cons, List.length_append, encodeDmaRegion27_length, List.length_cons, ih]; omega

def encodeStreamEntry (pt : Stage2IoPageTable) : List UInt8 :=
  u32ToBe4 pt.streamId ++ ([pt.role.tagByte, pt.ownerPd.tagByte] ++
    (be 8 pt.regions.length ++ pt.regions.flatMap encodeDmaRegion27))
def encodeSmmuStreams (streams : List Stage2IoPageTable) : List UInt8 :=
  be 8 streams.length ++ streams.flatMap encodeStreamEntry
def SmmuManifest.Fit (m : SmmuManifest) : Prop :=
  m.protectedRanges.length < 2 ^ 64 ∧ m.streams.length < 2 ^ 64 ∧ ∀ pt ∈ m.streams, pt.regions.length < 2 ^ 64

private theorem flatMap_streamEntry_injective :
    ∀ {xs ys : List Stage2IoPageTable}, xs.length = ys.length →
      (∀ pt ∈ xs, pt.regions.length < 2 ^ 64) → (∀ pt ∈ ys, pt.regions.length < 2 ^ 64) →
      xs.flatMap encodeStreamEntry = ys.flatMap encodeStreamEntry → xs = ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hc, _, _, _ => nomatch hc
  | _ :: _, [], hc, _, _, _ => nomatch hc
  | a :: as, b :: bs, hc, hfa, hfb, h => by
    simp only [List.flatMap_cons, encodeStreamEntry, List.append_assoc] at h
    obtain ⟨hSid, h⟩ := List.append_inj h ((u32ToBe4_length _).trans (u32ToBe4_length _).symm)
    obtain ⟨hHdr, h⟩ := List.append_inj h (rfl : ([a.role.tagByte, a.ownerPd.tagByte]).length = 2)
    obtain ⟨hRegCnt, h⟩ := List.append_inj h (by simp only [length_be])
    have hCntEq := be_injective (w := 8) (hfa a List.mem_cons_self) (hfb b List.mem_cons_self) hRegCnt
    have hBodyLen : (a.regions.flatMap encodeDmaRegion27).length =
        (b.regions.flatMap encodeDmaRegion27).length := by
      rw [flatMap_dmaRegion27_length, flatMap_dmaRegion27_length, hCntEq]
    obtain ⟨hRegs, hRest⟩ := List.append_inj h hBodyLen
    simp only [List.cons.injEq, and_true] at hHdr
    have hPtEq : a = b := by
      cases a; cases b; simp only [Stage2IoPageTable.mk.injEq]
      exact ⟨u32ToBe4_injective hSid, DeviceRole.tagByte_injective hHdr.1,
        ChokepointPdRole.tagByte_injective hHdr.2,
        flatMap_fixed_injective encodeDmaRegion27 27 (by decide)
          encodeDmaRegion27_length encodeDmaRegion27_injective hRegs⟩
    rw [hPtEq, flatMap_streamEntry_injective (Nat.succ.inj hc)
      (fun p hp => hfa p (List.mem_cons_of_mem _ hp))
      (fun p hp => hfb p (List.mem_cons_of_mem _ hp)) hRest]

theorem encodeSmmuStreams_injective {xs ys : List Stage2IoPageTable}
    (hxLen : xs.length < 2 ^ 64) (hyLen : ys.length < 2 ^ 64)
    (hxReg : ∀ pt ∈ xs, pt.regions.length < 2 ^ 64) (hyReg : ∀ pt ∈ ys, pt.regions.length < 2 ^ 64)
    (h : encodeSmmuStreams xs = encodeSmmuStreams ys) : xs = ys := by
  obtain ⟨hCnt, hBody⟩ := List.append_inj h (by simp only [length_be])
  exact flatMap_streamEntry_injective (be_injective (w := 8) hxLen hyLen hCnt) hxReg hyReg hBody

def smmuManifestWire (m : SmmuManifest) : String × List (List UInt8) :=
  Prod.mk "OBEND.SHE.SMMU_MANIFEST/v1"
    [ [m.arch.tagByte], [if m.defaultDeny then (1 : UInt8) else 0]
    , u64ToBe8 m.rootserverPhysStart, u64ToBe8 m.rootserverPhysEnd
    , u64ToBe8 m.dmaPoolBase, u64ToBe8 m.dmaPoolSize
    , encodeProtectedRanges m.protectedRanges, encodeSmmuStreams m.streams ]
def SmmuManifest.preimage (m : SmmuManifest) : List UInt8 := encodeSandboxFields (smmuManifestWire m).2

/-- Compute the 32-byte `cSHAKE256` commitment under `"OBEND.SHE.SMMU_MANIFEST/v1"`. -/
def smmuManifestDigest (m : SmmuManifest) : ByteArray :=
  let wire := smmuManifestWire m; sandboxDomainHash wire.1 wire.2

private theorem bool_of_byte {a b : Bool}
    (h : (if a then (1 : UInt8) else 0) = (if b then (1 : UInt8) else 0)) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem smmuManifestPreimage_injective {m₁ m₂ : SmmuManifest}
    (hw₁ : m₁.Fit) (hw₂ : m₂.Fit) (h : m₁.preimage = m₂.preimage) : m₁ = m₂ := by
  have hf := encodeSandboxFields_injective h
  simp only [smmuManifestWire, List.cons.injEq, and_true] at hf
  obtain ⟨hArch, hDeny, hRsStart, hRsEnd, hPoolB, hPoolS, hProt, hStr⟩ := hf
  cases m₁; cases m₂; simp only [SmmuManifest.mk.injEq]
  exact ⟨SmmuArch.tagByte_injective hArch, bool_of_byte hDeny,
    u64ToBe8_injective hRsStart, u64ToBe8_injective hRsEnd,
    u64ToBe8_injective hPoolB, u64ToBe8_injective hPoolS,
    encodeProtectedRanges_injective hProt,
    encodeSmmuStreams_injective hw₁.2.1 hw₂.2.1 hw₁.2.2 hw₂.2.2 hStr⟩

/-- **8-Field SMMU Manifest Commitment Binding (`0 Classical`, Scoped `CollisionAmong`)**. -/
theorem smmuManifestDigest_binds {m₁ m₂ : SmmuManifest}
    (hw₁ : m₁.Fit) (hw₂ : m₂.Fit) (h : smmuManifestDigest m₁ = smmuManifestDigest m₂) :
    m₁ = m₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1"))
      (fun x => x = m₁.preimage ∨ x = m₂.preimage) := by
  if hp : m₁.preimage = m₂.preimage then
    exact .inl (smmuManifestPreimage_injective hw₁ hw₂ hp)
  else
    right
    have hl : (cshake32ByteArray (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1") m₁.preimage).data.toList =
        (cshake32ByteArray (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1") m₂.preimage).data.toList :=
      congrArg (fun b => b.data.toList) h
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl
    exact ⟨m₁.preimage, m₂.preimage, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩

/-! ## 6. `smmuChokepointJudge` & Canonical Inhabitedness Witnesses -/

structure SmmuManifestQuery where
  config : ChokepointSmmuConfig
  expectedDigest? : Option ByteArray
  deriving DecidableEq
structure SmmuManifestCert where
  manifestDigest : ByteArray
  deriving DecidableEq
structure SmmuManifestMeaning (q : SmmuManifestQuery) (c : SmmuManifestCert) : Prop where
  safe : ChokepointSmmuSafeSpec q.config
  digestEq : c.manifestDigest = smmuManifestDigest q.config.manifest
  pinnedOk : ∀ exp, q.expectedDigest? = some exp → smmuManifestDigest q.config.manifest = exp

def smmuRequiredGrade (q : SmmuManifestQuery) : Nat :=
  q.config.manifest.streams.length + q.config.manifest.protectedRanges.length
def manifestFitB (m : SmmuManifest) : Bool :=
  decide (m.protectedRanges.length < 2 ^ 64) && decide (m.streams.length < 2 ^ 64) &&
  m.streams.all fun pt => decide (pt.regions.length < 2 ^ 64)
private theorem manifestFitB_iff (m : SmmuManifest) : manifestFitB m = true ↔ m.Fit := by
  simp [manifestFitB, SmmuManifest.Fit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

def smmuChokepointCheck (grade : Nat) (q : SmmuManifestQuery) (c : SmmuManifestCert) :
    Judge.Verdict SmmuRefusalClause :=
  if grade < smmuRequiredGrade q || !manifestFitB q.config.manifest then .uncovered
  else match verifyChokepointSmmuConfig q.config with
    | .error clause => .refused clause []
    | .ok () =>
      let actual := smmuManifestDigest q.config.manifest
      if c.manifestDigest != actual then .refused .certDigestMismatch []
      else match q.expectedDigest? with
        | none => .ok
        | some exp => if actual == exp then .ok else .refused .certDigestMismatch []

def smmuRefusalRefutes : SmmuRefusalClause → Bool
  | .defaultDenyDisabled | .spanExceedsBudget | .wildcardStreamId
  | .unalignedOrOutOfPoolRegion | .overlappingCommitFrame
  | .writableCodeOrOutbox | .forbiddenRoleRegionPerm => true
  | .certDigestMismatch => false

theorem smmuChokepointCheck_sound {r : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert}
    (h : smmuChokepointCheck r q c = .ok) : SmmuManifestMeaning q c := by
  unfold smmuChokepointCheck at h
  split at h; · cases h
  cases hv : verifyChokepointSmmuConfig q.config with
  | error _ => simp only [hv] at h; cases h
  | ok _ =>
    simp only [hv] at h
    cases hd : (c.manifestDigest != smmuManifestDigest q.config.manifest)
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      have hcEq : c.manifestDigest = smmuManifestDigest q.config.manifest := by
        simpa only [bne_eq_false_iff_eq] using hd
      refine ⟨verifyChokepointSmmuConfig_sound hv, hcEq, fun exp hexp => ?_⟩
      simp only [hexp] at h
      cases hEq : (smmuManifestDigest q.config.manifest == exp)
      · simp [hEq] at h
      · exact beq_iff_eq.mp hEq
    · simp [hd] at h

theorem smmuChokepointCheck_refuted {r : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert}
    {k : SmmuRefusalClause} {p : List Nat}
    (h : smmuChokepointCheck r q c = .refused k p) (hk : smmuRefusalRefutes k = true) :
    ∀ c', ¬ SmmuManifestMeaning q c' := by
  intro c' hMean
  have hOkCfg := verifyChokepointSmmuConfig_complete hMean.safe
  unfold smmuChokepointCheck at h; split at h; · cases h
  simp only [hOkCfg] at h
  cases hd : (c.manifestDigest != smmuManifestDigest q.config.manifest)
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    cases hexp : q.expectedDigest? with
    | none => simp [hexp] at h
    | some exp =>
      simp only [hexp] at h
      cases hEq : (smmuManifestDigest q.config.manifest == exp) <;>
        simp only [hEq, ↓reduceIte, Bool.false_eq_true] at h <;> (cases h; try cases hk)
  · simp only [hd, ↓reduceIte] at h; cases h; cases hk

theorem smmuChokepointCheck_complete {q : SmmuManifestQuery}
    (hFrag : q.config.manifest.Fit) (hInh : ∃ c, SmmuManifestMeaning q c) :
    ∃ c r, smmuChokepointCheck r q c = .ok := by
  obtain ⟨_, hMean⟩ := hInh
  refine ⟨⟨smmuManifestDigest q.config.manifest⟩, smmuRequiredGrade q, ?_⟩
  have hOkCfg := verifyChokepointSmmuConfig_complete hMean.safe
  have hFitB := (manifestFitB_iff q.config.manifest).mpr hFrag
  have hNotLt : ¬ (smmuRequiredGrade q < smmuRequiredGrade q) := Nat.lt_irrefl _
  simp only [smmuChokepointCheck, hNotLt, decide_false, hFitB, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hOkCfg, bne_self_eq_false]
  cases hexp : q.expectedDigest? with
  | none => rfl
  | some exp => simp [hMean.pinnedOk exp hexp]

theorem smmuChokepointCheck_mono {r r' : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert}
    (hle : r ≤ r') (hDec : smmuChokepointCheck r q c ≠ .uncovered) :
    smmuChokepointCheck r' q c = smmuChokepointCheck r q c := by
  unfold smmuChokepointCheck at hDec ⊢
  cases hFit : manifestFitB q.config.manifest <;> simp only [hFit] at hDec ⊢
  · simp at hDec
  · by_cases hlt : r < smmuRequiredGrade q
    · simp [hlt] at hDec
    · have hlt' : ¬ (r' < smmuRequiredGrade q) := by omega
      simp [hlt, hlt']

instance smmuChokepointJudge : Judge SmmuManifestQuery SmmuManifestCert where
  Clause := SmmuRefusalClause
  Meaning := SmmuManifestMeaning
  check := smmuChokepointCheck
  sound := smmuChokepointCheck_sound
  refutes := smmuRefusalRefutes
  refuted := smmuChokepointCheck_refuted
  Fragment q := q.config.manifest.Fit
  complete := smmuChokepointCheck_complete
  mono := smmuChokepointCheck_mono

def canonicalSmmuManifest : SmmuManifest :=
  { arch := .armSmmuV3, defaultDeny := true
    rootserverPhysStart := 0x60246000, rootserverPhysEnd := 0x60846000
    dmaPoolBase := 0x60846000, dmaPoolSize := 0x00100000
    protectedRanges :=
      [ { classTag := .commitPrivate, basePaddr := 0x60300000, size := 0x1000 }
      , { classTag := .pdCodeStackCspace, basePaddr := 0x60246000, size := 0x000ba000 } ]
    streams :=
      [ { streamId := 0x10, role := .ingressNic, ownerPd := .ingress, regions :=
          [⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩] }
      , { streamId := 0x20, role := .persistNvme, ownerPd := .persist, regions :=
          [⟨0x80010000, 0x60847000, 0x2000, .page4KiB, .readWrite, .persistWalPool⟩] }
      , { streamId := 0x30, role := .egressNic, ownerPd := .txEgress, regions :=
          [⟨0x80020000, 0x60849000, 0x1000, .page4KiB, .readOnly, .egressOutboxRing⟩] } ] }

def canonicalSmmuConfig : ChokepointSmmuConfig :=
  ⟨canonicalSmmuManifest, ⟨(0x60246000, 0x60846000), [0x60846], [0x60300],
    [0x60246, 0x60247], [0x60847, 0x60848], [0x60849]⟩⟩

def canonicalSmmuQuery : SmmuManifestQuery := ⟨canonicalSmmuConfig, none⟩
def canonicalSmmuCert : SmmuManifestCert := ⟨smmuManifestDigest canonicalSmmuManifest⟩

theorem smmuChokepointCheck_inhabited (grade : Nat) (hGrade : 5 ≤ grade) :
    verifyChokepointSmmuConfig canonicalSmmuConfig = .ok () ∧
      checkRegionsIovaDisjoint
        [⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩] = true ∧
      smmuChokepointCheck grade canonicalSmmuQuery canonicalSmmuCert = .ok := by
  have hCfgB : (verifyChokepointSmmuConfig canonicalSmmuConfig).toOption == some () := by decide
  have hCfg : verifyChokepointSmmuConfig canonicalSmmuConfig = .ok () := by
    cases hv : verifyChokepointSmmuConfig canonicalSmmuConfig with
    | error _ => rw [hv] at hCfgB; cases hCfgB
    | ok u => cases u; rfl
  have hDisj : checkRegionsIovaDisjoint
      [⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩] = true := by decide
  have hFit : manifestFitB canonicalSmmuManifest = true := by decide
  have hNotLt : ¬ (grade < 5) := by omega
  have hReq : smmuRequiredGrade canonicalSmmuQuery = 5 := by decide
  refine ⟨hCfg, hDisj, ?_⟩
  unfold smmuChokepointCheck
  have hqCfg : canonicalSmmuQuery.config = canonicalSmmuConfig := rfl
  have hcMan : canonicalSmmuConfig.manifest = canonicalSmmuManifest := rfl
  have hcDig : canonicalSmmuCert.manifestDigest = smmuManifestDigest canonicalSmmuManifest := rfl
  have hqExp : canonicalSmmuQuery.expectedDigest? = none := rfl
  rw [hReq, hqCfg, hCfg, hcMan, hFit, hcDig, hqExp]
  simp [hNotLt]

end Obend.OS.SmmuDmaConfinement
end
