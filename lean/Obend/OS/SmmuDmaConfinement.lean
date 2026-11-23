module
/-
# Obend.OS.SmmuDmaConfinement — Hardware-Real SMMUv3 / RISC-V IOMMU Confinement, Multi-Page
  4-Level Stage-2 Radix Refinement, and `CMD_CFGI_STE`/`CMD_TLBI_S2_IPA`/`CMD_SYNC` Epoch Safety
-/
public import Obend.Judge.Class
public import Obend.OS.Sel4MicrokitKernel
public import Obend.OS.SmmuRadixTables
public import Obend.Polis.SandboxDomainTags
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.OS.Sel4MicrokitKernel
import all Obend.OS.SmmuRadixTables
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

/-! ## 1. Chokepoint SMMU Policy Validation & Adversarial DMA Non-Interference -/
def regionTouchesFrame (reg : Stage2DmaRegion) (pfn : Nat) : Bool :=
  decide (reg.paddr.toNat < (pfn + 1) * pageSize ∧ pfn * pageSize < reg.paddr.toNat + reg.size.toNat)
theorem addr_in_region_touches_frame {reg : Stage2DmaRegion} {pa : Nat}
    (hlo : reg.paddr.toNat ≤ pa) (hhi : pa < reg.paddr.toNat + reg.size.toNat) :
    regionTouchesFrame reg (pa / pageSize) = true := by
  unfold regionTouchesFrame pageSize; exact decide_eq_true ⟨by omega, by omega⟩
def roleRegionPermAllowed (pt : Stage2IoPageTable) (reg : Stage2DmaRegion) (part : ChokepointFramePartition) : Bool :=
  match pt.role, pt.ownerPd, reg.kind with
  | .ingressNic, .ingress, .ingressRing => part.egressOutboxFrames.all fun pfn => !regionTouchesFrame reg pfn
  | .persistNvme, .persist, .persistWalPool =>
    part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .egressNic, .txEgress, .egressOutboxRing => reg.perm == .readOnly && part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .displayScanout, .txEgress, .displayFramebuffer =>
    reg.perm == .readOnly && part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .cameraCsi2, .ingress, .cameraRing => !reg.perm.allowsRead && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .gpu, .txEgress, .gpuScratchPool =>
    part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | .gpu, .txEgress, .displayFramebuffer =>
    reg.perm == .readOnly && part.ingressRingFrames.all (fun pfn => !regionTouchesFrame reg pfn) && part.egressOutboxFrames.all (fun pfn => !regionTouchesFrame reg pfn)
  | _, _, _ => false
inductive SmmuRefusalClause where
  | defaultDenyDisabled | spanExceedsBudget | wildcardStreamId | unalignedOrOutOfPoolRegion
  | overlappingCommitFrame | writableCodeOrOutbox | forbiddenRoleRegionPerm | certDigestMismatch
  deriving DecidableEq, Repr
def spanBudgetOkB (cfg : ChokepointSmmuConfig) : Bool :=
  let m := cfg.manifest
  (cfg.partition.rootServerBootSpan == (m.rootserverPhysStart, m.rootserverPhysEnd)) &&
  decide (m.rootserverPhysStart.toNat < m.rootserverPhysEnd.toNat) && decide (0 < m.dmaPoolSize.toNat) &&
  decide (m.dmaPoolBase.toNat + m.dmaPoolSize.toNat < 2 ^ 64) &&
  decide ((m.rootserverPhysEnd.toNat - m.rootserverPhysStart.toNat) + m.dmaPoolSize.toNat < maxRootServerSpanBytes) &&
  decide (stockMicrokitLoaderBase ≤ m.rootserverPhysStart.toNat ∨ m.rootserverPhysEnd.toNat ≤ stockMicrokitLoaderBase) &&
  rangesDisjointB m.rootserverPhysStart.toNat (m.rootserverPhysEnd.toNat - m.rootserverPhysStart.toNat) m.dmaPoolBase.toNat m.dmaPoolSize.toNat
def commitFramesIsolatedB (cfg : ChokepointSmmuConfig) : Bool :=
  !cfg.partition.commitPrivateFrames.isEmpty &&
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg =>
    (reg.kind != .commitPrivateFrame) && cfg.partition.commitPrivateFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
    cfg.manifest.protectedRanges.all fun pr =>
      pr.classTag != .commitPrivate || rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat
def codeAndOutboxProtectedB (cfg : ChokepointSmmuConfig) : Bool :=
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg =>
    (reg.kind != .pdCodeStackCspace) && (reg.kind != .trngMmio) &&
    cfg.partition.kernelAndCodeFrames.all (fun pfn => !regionTouchesFrame reg pfn) &&
    cfg.manifest.protectedRanges.all (fun pr =>
      pr.classTag == .commitPrivate || rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat) &&
    (!(cfg.partition.egressOutboxFrames.any (fun pfn => regionTouchesFrame reg pfn) || reg.kind == .egressOutboxRing) ||
      (pt.role == .egressNic && pt.ownerPd == .txEgress && reg.perm == .readOnly))
def allRolesPermittedB (cfg : ChokepointSmmuConfig) : Bool :=
  cfg.manifest.streams.all fun pt => pt.regions.all fun reg => roleRegionPermAllowed pt reg cfg.partition
def verifyChokepointSmmuConfig (cfg : ChokepointSmmuConfig) : Except SmmuRefusalClause Unit :=
  if !cfg.manifest.defaultDeny then .error .defaultDenyDisabled
  else if !spanBudgetOkB cfg then .error .spanExceedsBudget
  else if !streamsNoWildcardB cfg.manifest then .error .wildcardStreamId
  else if !streamsAlignedInPoolB cfg.manifest then .error .unalignedOrOutOfPoolRegion
  else if !commitFramesIsolatedB cfg then .error .overlappingCommitFrame
  else if !codeAndOutboxProtectedB cfg then .error .writableCodeOrOutbox
  else if !allRolesPermittedB cfg then .error .forbiddenRoleRegionPerm else .ok ()
structure ChokepointSmmuSafeSpec (cfg : ChokepointSmmuConfig) : Prop where
  defaultDeny : cfg.manifest.defaultDeny = true
  spanOk : cfg.partition.rootServerBootSpan = (cfg.manifest.rootserverPhysStart, cfg.manifest.rootserverPhysEnd) ∧
    cfg.manifest.rootserverPhysStart.toNat < cfg.manifest.rootserverPhysEnd.toNat ∧
    0 < cfg.manifest.dmaPoolSize.toNat ∧ cfg.manifest.dmaPoolBase.toNat + cfg.manifest.dmaPoolSize.toNat < 2 ^ 64 ∧
    (cfg.manifest.rootserverPhysEnd.toNat - cfg.manifest.rootserverPhysStart.toNat) + cfg.manifest.dmaPoolSize.toNat < maxRootServerSpanBytes ∧
    (stockMicrokitLoaderBase ≤ cfg.manifest.rootserverPhysStart.toNat ∨ cfg.manifest.rootserverPhysEnd.toNat ≤ stockMicrokitLoaderBase) ∧
    rangesDisjointB cfg.manifest.rootserverPhysStart.toNat (cfg.manifest.rootserverPhysEnd.toNat - cfg.manifest.rootserverPhysStart.toNat)
      cfg.manifest.dmaPoolBase.toNat cfg.manifest.dmaPoolSize.toNat = true
  noWildcard : (cfg.manifest.streams.map Stage2IoPageTable.streamId).Nodup ∧ ∀ pt ∈ cfg.manifest.streams, pt.streamId ≠ 0 ∧ pt.streamId ≠ wildcardStreamId
  alignedInPool : ∀ pt ∈ cfg.manifest.streams, checkRegionsIovaDisjoint pt.regions = true ∧ ∀ reg ∈ pt.regions, regionAlignedInPoolB cfg.manifest reg = true
  commitIsolated : cfg.partition.commitPrivateFrames ≠ [] ∧ ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions, reg.kind ≠ .commitPrivateFrame ∧
    (∀ pfn ∈ cfg.partition.commitPrivateFrames, regionTouchesFrame reg pfn = false) ∧
    (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag = .commitPrivate → rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true)
  codeAndOutboxSafe : ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions, reg.kind ≠ .pdCodeStackCspace ∧ reg.kind ≠ .trngMmio ∧
    (∀ pfn ∈ cfg.partition.kernelAndCodeFrames, regionTouchesFrame reg pfn = false) ∧
    (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag ≠ .commitPrivate → rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) ∧
    (((∃ pfn ∈ cfg.partition.egressOutboxFrames, regionTouchesFrame reg pfn = true) ∨ reg.kind = .egressOutboxRing) →
      pt.role = .egressNic ∧ pt.ownerPd = .txEgress ∧ reg.perm = .readOnly)
  roleMatrix : ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions, roleRegionPermAllowed pt reg cfg.partition = true
private theorem commitFramesIsolatedB_iff (cfg : ChokepointSmmuConfig) :
    commitFramesIsolatedB cfg = true ↔ cfg.partition.commitPrivateFrames ≠ [] ∧
      ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions, reg.kind ≠ .commitPrivateFrame ∧
        (∀ pfn ∈ cfg.partition.commitPrivateFrames, regionTouchesFrame reg pfn = false) ∧
        (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag = .commitPrivate → rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) := by
  unfold commitFramesIsolatedB; rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun ⟨hne, hall⟩ => ⟨by cases hc : cfg.partition.commitPrivateFrames <;> simp_all, fun pt hpt reg hreg => ?_⟩,
    fun ⟨hne, hall⟩ => ⟨by cases hc : cfg.partition.commitPrivateFrames <;> simp_all, fun pt hpt => ?_⟩⟩
  · have hr := List.all_eq_true.mp (hall pt hpt) reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true'] at hr
    exact ⟨hr.1.1, hr.1.2, fun pr hpr htag => by have hp := hr.2 pr hpr; simp [htag] at hp; exact hp⟩
  · rw [List.all_eq_true]; intro reg hreg; obtain ⟨hk, hc, hp⟩ := hall pt hpt reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true']
    exact ⟨⟨hk, hc⟩, fun pr hpr => by by_cases htag : pr.classTag = .commitPrivate <;> simp [htag, hp pr hpr]⟩
private theorem codeAndOutboxProtectedB_iff (cfg : ChokepointSmmuConfig) :
    codeAndOutboxProtectedB cfg = true ↔
      ∀ pt ∈ cfg.manifest.streams, ∀ reg ∈ pt.regions, reg.kind ≠ .pdCodeStackCspace ∧ reg.kind ≠ .trngMmio ∧
        (∀ pfn ∈ cfg.partition.kernelAndCodeFrames, regionTouchesFrame reg pfn = false) ∧
        (∀ pr ∈ cfg.manifest.protectedRanges, pr.classTag ≠ .commitPrivate →
          rangesDisjointB reg.paddr.toNat reg.size.toNat pr.basePaddr.toNat pr.size.toNat = true) ∧
        (((∃ pfn ∈ cfg.partition.egressOutboxFrames, regionTouchesFrame reg pfn = true) ∨ reg.kind = .egressOutboxRing) →
          pt.role = .egressNic ∧ pt.ownerPd = .txEgress ∧ reg.perm = .readOnly) := by
  unfold codeAndOutboxProtectedB; rw [List.all_eq_true]
  constructor
  · intro h pt hpt reg hreg
    have hr := List.all_eq_true.mp (h pt hpt) reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hr
    obtain ⟨⟨⟨⟨hk1, hk2⟩, hkern⟩, hprot⟩, hout⟩ := hr
    refine ⟨hk1, hk2, hkern, fun pr hpr hne => (hprot pr hpr).resolve_left hne, fun hor => ?_⟩
    rcases hout with hnot | hok
    · exfalso; simp only [Bool.or_eq_false_iff, List.any_eq_false, beq_eq_false_iff_ne, Bool.not_eq_true] at hnot
      rcases hor with ⟨pfn, hpfn, ht⟩ | hkind
      · exact absurd ht (by rw [hnot.1 pfn hpfn]; decide)
      · exact hnot.2 hkind
    · exact ⟨hok.1.1, hok.1.2, hok.2⟩
  · intro h pt hpt; rw [List.all_eq_true]; intro reg hreg
    obtain ⟨hk1, hk2, hkern, hprot, hout⟩ := h pt hpt reg hreg
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨hk1, hk2⟩, hkern⟩, fun pr hpr => by by_cases htag : pr.classTag = .commitPrivate <;> simp [htag, hprot pr hpr]⟩, ?_⟩
    cases hcond : (cfg.partition.egressOutboxFrames.any (fun pfn => regionTouchesFrame reg pfn) || reg.kind == .egressOutboxRing)
    · rfl
    · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hcond
      obtain ⟨h1, h2, h3⟩ := hout hcond; simp [h1, h2, h3]
theorem verifyChokepointSmmuConfig_sound {cfg : ChokepointSmmuConfig} (h : verifyChokepointSmmuConfig cfg = .ok ()) : ChokepointSmmuSafeSpec cfg := by
  unfold verifyChokepointSmmuConfig at h
  cases h1 : cfg.manifest.defaultDeny; · simp [h1] at h
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h2 : spanBudgetOkB cfg; · simp [h2] at h
  simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h3 : streamsNoWildcardB cfg.manifest; · simp [h3] at h
  simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h4 : streamsAlignedInPoolB cfg.manifest; · simp [h4] at h
  simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h5 : commitFramesIsolatedB cfg; · simp [h5] at h
  simp only [h5, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h6 : codeAndOutboxProtectedB cfg; · simp [h6] at h
  simp only [h6, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h7 : allRolesPermittedB cfg; · simp [h7] at h
  exact ⟨h1, by simpa [spanBudgetOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h2,
    by simpa [streamsNoWildcardB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] using h3,
    by simpa [streamsAlignedInPoolB, Bool.and_eq_true, List.all_eq_true] using h4,
    (commitFramesIsolatedB_iff cfg).mp h5, (codeAndOutboxProtectedB_iff cfg).mp h6,
    by simpa [allRolesPermittedB, List.all_eq_true] using h7⟩
theorem verifyChokepointSmmuConfig_complete {cfg : ChokepointSmmuConfig}
    (h : ChokepointSmmuSafeSpec cfg) : verifyChokepointSmmuConfig cfg = .ok () := by
  have h2 : spanBudgetOkB cfg = true := by simpa [spanBudgetOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h.spanOk
  have h3 : streamsNoWildcardB cfg.manifest = true := by simpa [streamsNoWildcardB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] using h.noWildcard
  have h4 : streamsAlignedInPoolB cfg.manifest = true := by simpa [streamsAlignedInPoolB, Bool.and_eq_true, List.all_eq_true] using h.alignedInPool
  have h7 : allRolesPermittedB cfg = true := by simpa [allRolesPermittedB, List.all_eq_true] using h.roleMatrix
  simp [verifyChokepointSmmuConfig, h.defaultDeny, h2, h3, h4,
    (commitFramesIsolatedB_iff cfg).mpr h.commitIsolated, (codeAndOutboxProtectedB_iff cfg).mpr h.codeAndOutboxSafe, h7]
private theorem authorized_dma_read_congr_bytes {cfg : ChokepointSmmuConfig} (hSafe : ChokepointSmmuSafeSpec cfg) (basePa len : Nat)
    (hBytes : ∀ i < len, ∃ pt ∈ cfg.manifest.streams, ∃ reg ∈ pt.regions, reg.paddr.toNat ≤ basePa + i ∧ basePa + i < reg.paddr.toNat + reg.size.toNat)
    {mem₁ mem₂ : Nat → UInt8}
    (hAgree : ∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames → pa / pageSize ∉ cfg.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa) :
    readPhys mem₁ basePa len = readPhys mem₂ basePa len := by
  unfold readPhys; refine congrArg Obend.Digest.Cshake256.Native.bytesOfList (List.map_congr_left fun i hi => ?_)
  obtain ⟨pt, hpt, reg, hreg, hlo, hhi⟩ := hBytes i (List.mem_range.mp hi); have hTouch := addr_in_region_touches_frame hlo hhi
  exact hAgree _ (fun hm => by rw [(hSafe.commitIsolated.2 pt hpt reg hreg).2.1 _ hm] at hTouch; cases hTouch)
    (fun hm => by rw [(hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.1 _ hm] at hTouch; cases hTouch)
private theorem authorized_dma_write_preserves_bytes {cfg : ChokepointSmmuConfig} (hSafe : ChokepointSmmuSafeSpec cfg) (basePa : Nat) (payload : ByteArray)
    (hBytes : ∀ i < payload.size, ∃ pt ∈ cfg.manifest.streams, ∃ reg ∈ pt.regions,
      reg.perm.permits .dmaWrite = true ∧ reg.paddr.toNat ≤ basePa + i ∧ basePa + i < reg.paddr.toNat + reg.size.toNat)
    (mem : Nat → UInt8) {pa : Nat}
    (hProt : pa / pageSize ∈ cfg.partition.commitPrivateFrames ∨ pa / pageSize ∈ cfg.partition.kernelAndCodeFrames ∨ pa / pageSize ∈ cfg.partition.egressOutboxFrames) :
    writePhys mem basePa payload pa = mem pa := by
  unfold writePhys; by_cases hIn : basePa ≤ pa ∧ pa < basePa + payload.size
  · exfalso; obtain ⟨pt, hpt, reg, hreg, hperm, hlo, hhi⟩ := hBytes (pa - basePa) (by omega)
    rw [show basePa + (pa - basePa) = pa by omega] at hlo hhi; have hTouch := addr_in_region_touches_frame hlo hhi
    rcases hProt with hCom | hKern | hOut
    · rw [(hSafe.commitIsolated.2 pt hpt reg hreg).2.1 _ hCom] at hTouch; cases hTouch
    · rw [(hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.1 _ hKern] at hTouch; cases hTouch
    · rw [((hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.2.2 (.inl ⟨_, hOut, hTouch⟩)).2.2] at hperm; cases hperm
  · simp [hIn]
private theorem authorized_dma_write_disjoint_range {cfg : ChokepointSmmuConfig} (hSafe : ChokepointSmmuSafeSpec cfg) {pr : ProtectedPhysRange}
    (hprMem : pr ∈ cfg.manifest.protectedRanges) (hprTag : pr.classTag ≠ .commitPrivate) (basePa : Nat) (payload : ByteArray)
    (hBytes : ∀ i < payload.size, ∃ pt ∈ cfg.manifest.streams, ∃ reg ∈ pt.regions, reg.paddr.toNat ≤ basePa + i ∧ basePa + i < reg.paddr.toNat + reg.size.toNat)
    (mem : Nat → UInt8) {pa : Nat} (hInPr : pr.basePaddr.toNat ≤ pa ∧ pa < pr.basePaddr.toNat + pr.size.toNat) :
    writePhys mem basePa payload pa = mem pa := by
  unfold writePhys; by_cases hIn : basePa ≤ pa ∧ pa < basePa + payload.size
  · exfalso; obtain ⟨pt, hpt, reg, hreg, hlo, hhi⟩ := hBytes (pa - basePa) (by omega)
    have hDisj := (hSafe.codeAndOutboxSafe pt hpt reg hreg).2.2.2.1 pr hprMem hprTag
    simp only [rangesDisjointB, decide_eq_true_eq] at hDisj; omega
  · simp [hIn]
private theorem writePhys_agree {P : Nat → Prop} {mem₁ mem₂ : Nat → UInt8}
    (hAg : ∀ pa, P pa → mem₁ pa = mem₂ pa) (basePa : Nat) (payload : ByteArray) :
    ∀ pa, P pa → writePhys mem₁ basePa payload pa = writePhys mem₂ basePa payload pa := by
  intro pa hp; unfold writePhys
  by_cases hIn : basePa ≤ pa ∧ pa < basePa + payload.size
  · simp only [hIn, and_self, ↓reduceIte]; cases payload.data[pa - basePa]? with | some _ => rfl | none => exact hAg pa hp
  · simp [hIn, hAg pa hp]
theorem dma_burst_preserves_private_pd_frames {cfg : ChokepointSmmuConfig}
    (hValid : verifyChokepointSmmuConfig cfg = .ok ()) (ops : List PeripheralDmaOp) (mem₁ mem₂ : Nat → UInt8)
    (hAgree : ∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames → pa / pageSize ∉ cfg.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa) :
    (∀ pa, (pa / pageSize ∈ cfg.partition.commitPrivateFrames ∨ pa / pageSize ∈ cfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ cfg.partition.egressOutboxFrames) → (execStage2DmaBurst cfg.manifest mem₁ ops).1 pa = mem₁ pa) ∧
    (execStage2DmaBurst cfg.manifest mem₁ ops).2 = (execStage2DmaBurst cfg.manifest mem₂ ops).2 := by
  have hSafe := verifyChokepointSmmuConfig_sound hValid
  induction ops generalizing mem₁ mem₂ with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons op ops ih =>
    simp only [execStage2DmaBurst]; cases op with
    | read sid iova len =>
      dsimp only [execStage2DmaOp]; cases ht : translateStage2Dma cfg.manifest sid iova len .dmaRead with
      | error _ => obtain ⟨hP, hO⟩ := ih mem₁ mem₂ hAgree; dsimp only []; exact ⟨hP, by rw [hO]⟩
      | ok basePa =>
        obtain ⟨-, -, -, -, pt, hpt, -, reg, hreg, hlo, hhi, -, hPa⟩ := translateStage2Dma_ok ht
        have hEq := authorized_dma_read_congr_bytes hSafe basePa len (fun i hi => ⟨pt, hpt, reg, hreg, by omega, by omega⟩) hAgree
        obtain ⟨hP, hO⟩ := ih mem₁ mem₂ hAgree; dsimp only []; exact ⟨hP, by rw [hEq, hO]⟩
    | write sid iova payload =>
      dsimp only [execStage2DmaOp]; cases ht : translateStage2Dma cfg.manifest sid iova payload.size .dmaWrite with
      | error _ => obtain ⟨hP, hO⟩ := ih mem₁ mem₂ hAgree; exact ⟨hP, by rw [hO]⟩
      | ok basePa =>
        obtain ⟨-, -, -, -, pt, hpt, -, reg, hreg, hlo, hhi, hperm, hPa⟩ := translateStage2Dma_ok ht
        have hAg₁ : ∀ pa, pa / pageSize ∉ cfg.partition.commitPrivateFrames → pa / pageSize ∉ cfg.partition.kernelAndCodeFrames →
            writePhys mem₁ basePa payload pa = writePhys mem₂ basePa payload pa := fun pa hc hk =>
          writePhys_agree (P := fun x => x / pageSize ∉ cfg.partition.commitPrivateFrames ∧ x / pageSize ∉ cfg.partition.kernelAndCodeFrames)
            (fun x ⟨c, k⟩ => hAgree x c k) basePa payload pa ⟨hc, hk⟩
        obtain ⟨hPRest, hORest⟩ := ih _ _ hAg₁
        exact ⟨fun pa hProt => (hPRest pa hProt).trans (authorized_dma_write_preserves_bytes hSafe basePa payload
          (fun i hi => ⟨pt, hpt, reg, hreg, hperm, by omega, by omega⟩) mem₁ hProt), by rw [hORest]⟩

/-! ## 2. Coupling Stage-2 DMA Bursts to `Sel4MicrokitKernel.ValidVerifierLoop` -/
def dmaOpToKernelEvents : PeripheralDmaOp → List KEvent
  | .read _ _ _ => [] | .write sid iova payload => (List.range payload.size).map fun i => .dma sid.toNat (iova + i) (payload.data[i]?.getD 0)
def dmaBurstToKernelEvents (ops : List PeripheralDmaOp) : List KEvent := ops.flatMap dmaOpToKernelEvents
theorem dmaBurstToKernelEvents_actor_ne {ops : List PeripheralDmaOp} {vpd : PdId} :
    ∀ ev ∈ dmaBurstToKernelEvents ops, ev.actor ≠ some vpd := by
  intro ev hev; obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hev
  cases op with | read _ _ _ => cases hop | write _ _ _ => obtain ⟨_, -, rfl⟩ := List.mem_map.mp hop; simp [KEvent.actor]
def SmmuWriteProtected (k : KState) (vpd : PdId) (protectedWriteFrames : List Nat) : Prop :=
  (∀ i n, capAt k.cspace i = some n → n.cap.rights.write = true → (∃ f ∈ protectedWriteFrames, n.cap.obj.touches f = true) → n.owner = vpd) ∧
  (∀ e ∈ k.maps, ∀ sid, e.space = .dev sid → e.writable = true → e.pfn ∉ protectedWriteFrames)
theorem smmuWriteProtected_step {k : KState} {vpd : PdId} {frames : List Nat} {ev : KEvent}
    (hK : KInv k) (hProt : SmmuWriteProtected k vpd frames) (hAdv : ev.actor ≠ some vpd) : SmmuWriteProtected (kstep k ev) vpd frames := by
  obtain ⟨hCaps, hMaps⟩ := hProt
  rcases kstep_frame k ev with ⟨pd, call, k', rfl, hk, hstep⟩ | ⟨hc, hm⟩
  · rw [hstep]; have hpd : pd ≠ vpd := fun e => hAdv (by simp [KEvent.actor, e])
    obtain ⟨-, -, hE⟩ := ksyscall_effect hk
    rcases hE with ⟨src, n, dst, cap, hn, hown, hle, hcs, hm⟩ | ⟨hS, hm⟩ |
      ⟨hcs, e, hm, hown, -, f, a, hf, hfo, hfobj, hfw, -, -, -⟩ | ⟨hcs, hsub⟩
    · refine ⟨?_, hm ▸ hMaps⟩; intro i x hx xw ⟨fr, hfr, htouch⟩; rw [hcs] at hx
      rcases capAt_mintCap hx with hx | rfl
      · exact hCaps i x hx xw ⟨fr, hfr, htouch⟩
      · obtain ⟨ho, hrs, -⟩ := Cap.le_iff.mp hle
        exact absurd ((hCaps src n hn ((Rights.sub_iff.mp hrs).2.1 xw) ⟨fr, hfr, CapObj.touches_mono ho htouch⟩).symm.trans hown) (fun e => hpd e.symm)
    · have hin : ∀ e ∈ k'.maps, e ∈ k.maps := fun e he => (List.mem_filter.mp (hm ▸ he)).1
      exact ⟨fun i x hx => hCaps i x ((hS hK.1).1 i x hx), fun e he => hMaps e (hin e he)⟩
    · refine ⟨hcs ▸ hCaps, ?_⟩; intro x hx sid hs hw hmem; rw [hm] at hx; rcases List.mem_cons.mp hx with rfl | hx
      · have hft : f.cap.obj.touches x.pfn = true := by rw [hfobj]; simp [CapObj.touches]
        exact hpd (hown.symm.trans (hfo.symm.trans (hCaps _ f hf (hfw hw) ⟨x.pfn, hmem, hft⟩)))
      · exact hMaps x hx sid hs hw hmem
    · exact ⟨hcs ▸ hCaps, fun e he => hMaps e (hsub e he)⟩
  · exact ⟨hc ▸ hCaps, hm ▸ hMaps⟩
theorem smmuWriteProtected_run {k : KState} {vpd : PdId} {frames : List Nat} (evs : List KEvent)
    (hK : KInv k) (hProt : SmmuWriteProtected k vpd frames) (hAdv : ∀ ev ∈ evs, ev.actor ≠ some vpd) : SmmuWriteProtected (runK k evs) vpd frames := by
  induction evs generalizing k with
  | nil => exact hProt
  | cons ev evs ih => exact ih (kstep_inv hK ev) (smmuWriteProtected_step hK hProt (hAdv ev List.mem_cons_self)) (fun e he => hAdv e (List.mem_cons_of_mem _ he))
theorem smmuWriteProtected_dma_preserves_mem {k : KState} {vpd : PdId} {frames : List Nat}
    (hProt : SmmuWriteProtected k vpd frames) (ops : List PeripheralDmaOp) (pa : Nat) (hpa : pa / pageSize ∈ frames) :
    (runK k (dmaBurstToKernelEvents ops)).mem pa = k.mem pa := by
  have key : ∀ (evs : List KEvent) (k' : KState), k'.maps = k.maps → (∀ ev ∈ evs, ∃ s v b, ev = .dma s v b) → (runK k' evs).mem pa = k'.mem pa := by
    intro evs; induction evs with
    | nil => intro _ _ _; rfl
    | cons ev evs ih =>
      intro k' hm hall; obtain ⟨sid, va, val, rfl⟩ := hall ev List.mem_cons_self
      have hm1 : (kstep k' (.dma sid va val)).maps = k'.maps := (storeVia_frame k' (.dev sid) va val).2.1
      have hmem1 : (kstep k' (.dma sid va val)).mem pa = k'.mem pa := by
        by_cases hEq : (kstep k' (.dma sid va val)).mem pa = k'.mem pa; · exact hEq
        obtain ⟨sp, e, hsp, he, hes, hw, hpfn⟩ := kstep_mem_changed hEq
        cases hsp; exact absurd (hpfn ▸ hpa) (hProt.2 e (hm ▸ he) sid hes hw)
      exact (ih _ (hm1.trans hm) (fun e he => hall e (List.mem_cons_of_mem _ he))).trans hmem1
  refine key (dmaBurstToKernelEvents ops) k rfl fun ev hev => ?_
  obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hev
  cases op with | read _ _ _ => cases hop | write _ _ _ => obtain ⟨_, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, _, _, rfl⟩
structure SmmuVerifierTurn where
  (preEvents : List KEvent) (preDma : List PeripheralDmaOp) (midEvents : List KEvent) (midDma : List PeripheralDmaOp)
  (ringAtCopy : ByteArray) (out : OutboxTurn) (grain : GrainId) (slot : Nat) (need : UInt64)
def SmmuVerifierTurn.toVerifierTurn (t : SmmuVerifierTurn) : VerifierTurn :=
  ⟨t.preEvents ++ dmaBurstToKernelEvents t.preDma, t.midEvents ++ dmaBurstToKernelEvents t.midDma, t.ringAtCopy, t.out, t.grain, t.slot, t.need⟩
def ValidSmmuVerifierLoop (smmuCfg : ChokepointSmmuConfig) (P : Protocol) (part : SeL4MicrokitPartition) (inCfg : IngressCfg) :
    LoopState → List SmmuVerifierTurn → LoopState → Prop
  | s, [], f => f = s ∧ Reach P s.sent ∧ checkMicrokitIsolation part = true ∧ verifyChokepointSmmuConfig smmuCfg = .ok ()
  | s, t :: ts, f =>
    verifyChokepointSmmuConfig smmuCfg = .ok () ∧ (∀ ev ∈ t.preEvents, ev.actor ≠ some inCfg.vpd) ∧ (∀ ev ∈ t.midEvents, ev.actor ≠ some inCfg.vpd) ∧
    readVia (copyState s.kernel t.toVerifierTurn) inCfg.vpd inCfg.sharedV inCfg.len = some t.ringAtCopy ∧
    (translate (copyState s.kernel t.toVerifierTurn).maps (.cpu inCfg.vpd) inCfg.privV true).isSome = true ∧
    readVia (dispatchState inCfg s.kernel t.toVerifierTurn) inCfg.vpd (dispatchVaddr inCfg) inCfg.len = some t.out.req.spsc.sharedRingBeforeCopy ∧
    Reach P s.sent ∧ SentSteps P s.sent t.out.nextSent ∧
    ∃ (h₁ : PowerboxHost) (stMid st₁ : OutboxState),
      Obend.Polis.GrainPowerbox.stepPowerboxHost s.host (invokeOf t.toVerifierTurn) = some h₁ ∧
      stepOutbox P part t.out.nextSent s.outbox t.out.req = some stMid ∧
      (match t.out.reconcileCert? with | none => st₁ = stMid | some cert => reconcileEscrowsWithCert P t.out.nextSent cert stMid = some st₁) ∧
      ValidSmmuVerifierLoop smmuCfg P part inCfg ⟨dispatchState inCfg s.kernel t.toVerifierTurn, t.out.nextSent, st₁, h₁⟩ ts f
theorem validSmmuVerifierLoop_to_kernelLoop {smmuCfg : ChokepointSmmuConfig} {P : Protocol}
    {part : SeL4MicrokitPartition} {inCfg : IngressCfg} {turns : List SmmuVerifierTurn} {s f : LoopState}
    (h : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) :
    verifyChokepointSmmuConfig smmuCfg = .ok () ∧ ValidVerifierLoop P part inCfg s (turns.map SmmuVerifierTurn.toVerifierTurn) f := by
  induction turns generalizing s with
  | nil => simp only [ValidSmmuVerifierLoop, List.map_nil, ValidVerifierLoop] at h ⊢; exact ⟨h.2.2.2, h.1, h.2.1, h.2.2.1⟩
  | cons t ts ih =>
    simp only [ValidSmmuVerifierLoop] at h; obtain ⟨hCfg, hPreC, hMidC, hRing, hCopy, hDisp, hR, hSt, h₁, stMid, st₁, hPb, hOb, hRec, hRest⟩ := h
    exact ⟨hCfg, fun ev hev => (List.mem_append.mp hev).elim (hPreC ev) (dmaBurstToKernelEvents_actor_ne ev),
      fun ev hev => (List.mem_append.mp hev).elim (hMidC ev) (dmaBurstToKernelEvents_actor_ne ev),
      hRing, hCopy, hDisp, hR, hSt, h₁, stMid, st₁, hPb, hOb, hRec, (ih hRest).2⟩
theorem validSmmuVerifierLoop_preserves_writeProtected {smmuCfg : ChokepointSmmuConfig} {P : Protocol}
    {part : SeL4MicrokitPartition} {inCfg : IngressCfg} {frames : List Nat} {turns : List SmmuVerifierTurn} {s f : LoopState}
    (hK : KInv s.kernel) (hProt : SmmuWriteProtected s.kernel inCfg.vpd frames)
    (h : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) : SmmuWriteProtected f.kernel inCfg.vpd frames := by
  induction turns generalizing s with
  | nil => simp only [ValidSmmuVerifierLoop] at h; rw [h.1]; exact hProt
  | cons t ts ih =>
    simp only [ValidSmmuVerifierLoop] at h; obtain ⟨-, hPreC, hMidC, -, -, -, -, -, _, _, _, -, -, -, hRest⟩ := h
    have hPreAll : ∀ ev ∈ t.toVerifierTurn.pre, ev.actor ≠ some inCfg.vpd := fun ev hev => (List.mem_append.mp hev).elim (hPreC ev) (dmaBurstToKernelEvents_actor_ne ev)
    have hMidAll : ∀ ev ∈ t.toVerifierTurn.mid, ev.actor ≠ some inCfg.vpd := fun ev hev => (List.mem_append.mp hev).elim (hMidC ev) (dmaBurstToKernelEvents_actor_ne ev)
    have hProt₁ := smmuWriteProtected_run t.toVerifierTurn.pre hK hProt hPreAll; have hK₁ := runK_inv hK t.toVerifierTurn.pre
    obtain ⟨hc, hm, -⟩ := copyVia_frame (copyState s.kernel t.toVerifierTurn) inCfg.vpd inCfg.sharedV inCfg.privV inCfg.len
    have hK₂ : KInv (ingressCopy inCfg (copyState s.kernel t.toVerifierTurn)) := kstep_inv hK₁ _
    exact ih (runK_inv hK₂ t.toVerifierTurn.mid) (smmuWriteProtected_run t.toVerifierTurn.mid hK₂ ⟨hc ▸ hProt₁.1, hm ▸ hProt₁.2⟩ hMidAll) hRest
theorem smmu_verifier_loop_dma_safe {smmuCfg : ChokepointSmmuConfig} {P : Protocol} {part : SeL4MicrokitPartition}
    {inCfg : IngressCfg} {turns : List SmmuVerifierTurn} {s f : LoopState} {da₀ : Nat} (hK : KInv s.kernel) (hS : KSched s.kernel)
    (hP₀ : translate s.kernel.maps (.cpu inCfg.vpd) inCfg.privV true = some da₀) (hEx : Exclusive s.kernel inCfg.vpd (da₀ / pageSize))
    (hProt : SmmuWriteProtected s.kernel inCfg.vpd (smmuCfg.partition.kernelAndCodeFrames ++ smmuCfg.partition.egressOutboxFrames))
    (hClean : s.outbox.dispatchedActuations = []) (hAcc : Accountable s.host) (hLoop : ValidSmmuVerifierLoop smmuCfg P part inCfg s turns f) :
    (KInv f.kernel ∧ Exclusive f.kernel inCfg.vpd (da₀ / pageSize) ∧ KSched f.kernel ∧
      SmmuWriteProtected f.kernel inCfg.vpd (smmuCfg.partition.kernelAndCodeFrames ++ smmuCfg.partition.egressOutboxFrames) ∧
      ∀ i n, capAt f.kernel.cspace i = some n → ∃ j r, capAt s.kernel.cspace j = some r ∧ n.cap.le r.cap = true) ∧
    (∀ t ∈ turns, ∀ mem : Nat → UInt8, ∀ pa,
      (pa / pageSize ∈ smmuCfg.partition.commitPrivateFrames ∨ pa / pageSize ∈ smmuCfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ smmuCfg.partition.egressOutboxFrames) → (execStage2DmaBurst smmuCfg.manifest mem t.midDma).1 pa = mem pa) ∧
    Accountable f.host ∧ Sel4CapDlNonInterfering part ∧ (f.outbox.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    ∀ a ∈ f.outbox.dispatchedActuations, Finalized P f.sent a.view a.chain ∧
      (∀ (vCanon : Nat) (cCanon : Chain), Finalized P f.sent vCanon cCanon → a.view ≤ vCanon → a.chain <+: cCanon) ∧
      ∃ t ∈ turns, t.out.req.effectClass = .irreversibleActuation ∧ a.nullifierId = t.out.req.nullifierId ∧ a.dispatchedPayload = t.ringAtCopy ∧
        ∃ entry ∈ f.host.audit, entry.whoInvoked = .grain t.grain ∧ entry.actionDigest = actionDigest a.dispatchedPayload := by
  obtain ⟨hValidCfg, hVLoop⟩ := validSmmuVerifierLoop_to_kernelLoop hLoop
  obtain ⟨⟨hKFin, hExFin, hSFin, hAmp⟩, hAccFin, hIso, hNodup, hActs⟩ := sel4_microkit_verifier_loop_safe hK hS hP₀ hEx hClean hAcc hVLoop
  refine ⟨⟨hKFin, hExFin, hSFin, validSmmuVerifierLoop_preserves_writeProtected hK hProt hLoop, hAmp⟩,
    fun t _ mem pa hFrame => (dma_burst_preserves_private_pd_frames hValidCfg t.midDma mem mem (fun _ _ _ => rfl)).1 pa hFrame,
    hAccFin, hIso, hNodup, fun a ha => ?_⟩
  obtain ⟨hFin, hCanon, tv, htv, hEff, hNull, hPay, entry, hEnt, hWho, hDig⟩ := hActs a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htv; exact ⟨hFin, hCanon, t, ht, hEff, hNull, hPay, entry, hEnt, hWho, hDig⟩

/-! ## 3. 256-Bit `OBEND.SHE.SMMU_MANIFEST/v1` Wire Commitment & Scoped `CollisionAmong` Binding -/
def u32ToBe4 (w : UInt32) : List UInt8 := be 4 w.toNat
theorem u32ToBe4_length (w : UInt32) : (u32ToBe4 w).length = 4 := length_be ..
theorem u32ToBe4_injective {w₁ w₂ : UInt32} (h : u32ToBe4 w₁ = u32ToBe4 w₂) : w₁ = w₂ :=
  UInt32.toNat_inj.mp (be_injective (w := 4) w₁.toBitVec.isLt w₂.toBitVec.isLt h)
private theorem flatMap_fixed_injective {α : Type} (f : α → List UInt8) (k : Nat) (hkPos : 0 < k)
    (hk : ∀ x, (f x).length = k) (hinj : ∀ {x y}, f x = f y → x = y) : ∀ {xs ys : List α}, xs.flatMap f = ys.flatMap f → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by have hl : ((y :: ys).flatMap f).length = 0 := by rw [← h]; rfl
                         simp only [List.flatMap_cons, List.length_append, hk y] at hl; omega
  | x :: xs, [], h => by have hl : ((x :: xs).flatMap f).length = 0 := by rw [h]; rfl
                         simp only [List.flatMap_cons, List.length_append, hk x] at hl; omega
  | a :: as, b :: bs, h => by
    simp only [List.flatMap_cons] at h; obtain ⟨h1, h2⟩ := List.append_inj h ((hk a).trans (hk b).symm)
    rw [hinj h1, flatMap_fixed_injective f k hkPos hk hinj h2]
def encodeProtectedRange17 (pr : ProtectedPhysRange) : List UInt8 := pr.classTag.tagByte :: (u64ToBe8 pr.basePaddr ++ u64ToBe8 pr.size)
theorem encodeProtectedRange17_length (pr : ProtectedPhysRange) : (encodeProtectedRange17 pr).length = 17 := by simp [encodeProtectedRange17, u64ToBe8_length]
theorem encodeProtectedRange17_injective {a b : ProtectedPhysRange} (h : encodeProtectedRange17 a = encodeProtectedRange17 b) : a = b := by
  obtain ⟨hTag, hRest⟩ := List.cons.inj h; obtain ⟨hBase, hSz⟩ := List.append_inj hRest ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  cases a; cases b; simp only [ProtectedPhysRange.mk.injEq]; exact ⟨ProtectedFrameClass.tagByte_injective hTag, u64ToBe8_injective hBase, u64ToBe8_injective hSz⟩
def encodeProtectedRanges (xs : List ProtectedPhysRange) : List UInt8 := be 8 xs.length ++ xs.flatMap encodeProtectedRange17
theorem encodeProtectedRanges_injective {xs ys : List ProtectedPhysRange} (h : encodeProtectedRanges xs = encodeProtectedRanges ys) : xs = ys := by
  obtain ⟨-, hBody⟩ := List.append_inj h (by simp only [length_be])
  exact flatMap_fixed_injective encodeProtectedRange17 17 (by decide) encodeProtectedRange17_length encodeProtectedRange17_injective hBody
def encodeDmaRegion27 (r : Stage2DmaRegion) : List UInt8 :=
  u64ToBe8 r.iova ++ (u64ToBe8 r.paddr ++ (u64ToBe8 r.size ++ [r.granule.tagByte, r.perm.tagByte, r.kind.tagByte]))
theorem encodeDmaRegion27_length (r : Stage2DmaRegion) : (encodeDmaRegion27 r).length = 27 := by simp [encodeDmaRegion27, u64ToBe8_length]
theorem encodeDmaRegion27_injective {a b : Stage2DmaRegion} (h : encodeDmaRegion27 a = encodeDmaRegion27 b) : a = b := by
  obtain ⟨hIova, h1⟩ := List.append_inj h ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  obtain ⟨hPa, h2⟩ := List.append_inj h1 ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  obtain ⟨hSz, hTags⟩ := List.append_inj h2 ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
  simp only [List.cons.injEq, and_true] at hTags; cases a; cases b; simp only [Stage2DmaRegion.mk.injEq]
  exact ⟨u64ToBe8_injective hIova, u64ToBe8_injective hPa, u64ToBe8_injective hSz,
    PageGranule.tagByte_injective hTags.1, IoPerm.tagByte_injective hTags.2.1, DmaRegionKind.tagByte_injective hTags.2.2⟩
private theorem flatMap_dmaRegion27_length (rs : List Stage2DmaRegion) : (rs.flatMap encodeDmaRegion27).length = 27 * rs.length := by
  induction rs with | nil => rfl | cons _ _ ih => simp only [List.flatMap_cons, List.length_append, encodeDmaRegion27_length, List.length_cons, ih]; omega
def encodeStreamEntry (pt : Stage2IoPageTable) : List UInt8 :=
  u32ToBe4 pt.streamId ++ ([pt.role.tagByte, pt.ownerPd.tagByte] ++ (be 8 pt.regions.length ++ pt.regions.flatMap encodeDmaRegion27))
def encodeSmmuStreams (streams : List Stage2IoPageTable) : List UInt8 := be 8 streams.length ++ streams.flatMap encodeStreamEntry
def SmmuManifest.Fit (m : SmmuManifest) : Prop :=
  m.protectedRanges.length < 2 ^ 64 ∧ m.streams.length < 2 ^ 64 ∧ ∀ pt ∈ m.streams, pt.regions.length < 2 ^ 64
private theorem flatMap_streamEntry_injective : ∀ {xs ys : List Stage2IoPageTable}, xs.length = ys.length →
    (∀ pt ∈ xs, pt.regions.length < 2 ^ 64) → (∀ pt ∈ ys, pt.regions.length < 2 ^ 64) → xs.flatMap encodeStreamEntry = ys.flatMap encodeStreamEntry → xs = ys
  | [], [], _, _, _, _ => rfl | [], _ :: _, hc, _, _, _ => nomatch hc | _ :: _, [], hc, _, _, _ => nomatch hc
  | a :: as, b :: bs, hc, hfa, hfb, h => by
    simp only [List.flatMap_cons, encodeStreamEntry, List.append_assoc] at h
    obtain ⟨hSid, h⟩ := List.append_inj h ((u32ToBe4_length _).trans (u32ToBe4_length _).symm)
    obtain ⟨hHdr, h⟩ := List.append_inj h (rfl : ([a.role.tagByte, a.ownerPd.tagByte]).length = 2)
    obtain ⟨hRegCnt, h⟩ := List.append_inj h (by simp only [length_be])
    have hCntEq := be_injective (w := 8) (hfa a List.mem_cons_self) (hfb b List.mem_cons_self) hRegCnt
    obtain ⟨hRegs, hRest⟩ := List.append_inj h (by rw [flatMap_dmaRegion27_length, flatMap_dmaRegion27_length, hCntEq])
    simp only [List.cons.injEq, and_true] at hHdr
    have hPtEq : a = b := by
      cases a; cases b; simp only [Stage2IoPageTable.mk.injEq]
      exact ⟨u32ToBe4_injective hSid, DeviceRole.tagByte_injective hHdr.1, ChokepointPdRole.tagByte_injective hHdr.2,
        flatMap_fixed_injective encodeDmaRegion27 27 (by decide) encodeDmaRegion27_length encodeDmaRegion27_injective hRegs⟩
    rw [hPtEq, flatMap_streamEntry_injective (Nat.succ.inj hc) (fun p hp => hfa p (List.mem_cons_of_mem _ hp)) (fun p hp => hfb p (List.mem_cons_of_mem _ hp)) hRest]
theorem encodeSmmuStreams_injective {xs ys : List Stage2IoPageTable} (hxLen : xs.length < 2 ^ 64) (hyLen : ys.length < 2 ^ 64)
    (hxReg : ∀ pt ∈ xs, pt.regions.length < 2 ^ 64) (hyReg : ∀ pt ∈ ys, pt.regions.length < 2 ^ 64) (h : encodeSmmuStreams xs = encodeSmmuStreams ys) : xs = ys := by
  obtain ⟨hCnt, hBody⟩ := List.append_inj h (by simp only [length_be])
  exact flatMap_streamEntry_injective (be_injective (w := 8) hxLen hyLen hCnt) hxReg hyReg hBody
def smmuManifestWire (m : SmmuManifest) : String × List (List UInt8) :=
  Prod.mk "OBEND.SHE.SMMU_MANIFEST/v1" [ [m.arch.tagByte], [if m.defaultDeny then (1 : UInt8) else 0]
    , u64ToBe8 m.rootserverPhysStart, u64ToBe8 m.rootserverPhysEnd, u64ToBe8 m.dmaPoolBase, u64ToBe8 m.dmaPoolSize
    , encodeProtectedRanges m.protectedRanges, encodeSmmuStreams m.streams ]
def SmmuManifest.preimage (m : SmmuManifest) : List UInt8 := encodeSandboxFields (smmuManifestWire m).2
def smmuManifestDigest (m : SmmuManifest) : ByteArray := let wire := smmuManifestWire m; sandboxDomainHash wire.1 wire.2
private theorem bool_of_byte {a b : Bool} (h : (if a then (1 : UInt8) else 0) = (if b then (1 : UInt8) else 0)) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
theorem smmuManifestPreimage_injective {m₁ m₂ : SmmuManifest} (hw₁ : m₁.Fit) (hw₂ : m₂.Fit) (h : m₁.preimage = m₂.preimage) : m₁ = m₂ := by
  have hf := encodeSandboxFields_injective h; simp only [smmuManifestWire, List.cons.injEq, and_true] at hf
  obtain ⟨hArch, hDeny, hRsStart, hRsEnd, hPoolB, hPoolS, hProt, hStr⟩ := hf; cases m₁; cases m₂; simp only [SmmuManifest.mk.injEq]
  exact ⟨SmmuArch.tagByte_injective hArch, bool_of_byte hDeny, u64ToBe8_injective hRsStart, u64ToBe8_injective hRsEnd,
    u64ToBe8_injective hPoolB, u64ToBe8_injective hPoolS, encodeProtectedRanges_injective hProt, encodeSmmuStreams_injective hw₁.2.1 hw₂.2.1 hw₁.2.2 hw₂.2.2 hStr⟩
theorem smmuManifestDigest_binds {m₁ m₂ : SmmuManifest} (hw₁ : m₁.Fit) (hw₂ : m₂.Fit) (h : smmuManifestDigest m₁ = smmuManifestDigest m₂) :
    m₁ = m₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1")) (fun x => x = m₁.preimage ∨ x = m₂.preimage) := by
  if hp : m₁.preimage = m₂.preimage then exact .inl (smmuManifestPreimage_injective hw₁ hw₂ hp)
  else
    right; have hl : (cshake32ByteArray (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1") m₁.preimage).data.toList =
        (cshake32ByteArray (asciiTagBytes "OBEND.SHE.SMMU_MANIFEST/v1") m₂.preimage).data.toList := congrArg (fun b => b.data.toList) h
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl; exact ⟨m₁.preimage, m₂.preimage, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩

/-! ## 4. `smmuChokepointJudge` -/
structure SmmuManifestQuery where (config : ChokepointSmmuConfig) (expectedDigest? : Option ByteArray) deriving DecidableEq
structure SmmuManifestCert where (manifestDigest : ByteArray) deriving DecidableEq
structure SmmuManifestMeaning (q : SmmuManifestQuery) (c : SmmuManifestCert) : Prop where
  (safe : ChokepointSmmuSafeSpec q.config) (digestEq : c.manifestDigest = smmuManifestDigest q.config.manifest)
  (pinnedOk : ∀ exp, q.expectedDigest? = some exp → smmuManifestDigest q.config.manifest = exp)
def smmuRequiredGrade (q : SmmuManifestQuery) : Nat := q.config.manifest.streams.length + q.config.manifest.protectedRanges.length
def manifestFitB (m : SmmuManifest) : Bool :=
  decide (m.protectedRanges.length < 2 ^ 64) && decide (m.streams.length < 2 ^ 64) && m.streams.all fun pt => decide (pt.regions.length < 2 ^ 64)
private theorem manifestFitB_iff (m : SmmuManifest) : manifestFitB m = true ↔ m.Fit := by
  simp [manifestFitB, SmmuManifest.Fit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]
def smmuChokepointCheck (grade : Nat) (q : SmmuManifestQuery) (c : SmmuManifestCert) : Judge.Verdict SmmuRefusalClause :=
  if grade < smmuRequiredGrade q || !manifestFitB q.config.manifest then .uncovered
  else match verifyChokepointSmmuConfig q.config with
    | .error clause => .refused clause []
    | .ok () => let actual := smmuManifestDigest q.config.manifest
                if c.manifestDigest != actual then .refused .certDigestMismatch []
                else match q.expectedDigest? with | none => .ok | some exp => if actual == exp then .ok else .refused .certDigestMismatch []
def smmuRefusalRefutes : SmmuRefusalClause → Bool
  | .defaultDenyDisabled | .spanExceedsBudget | .wildcardStreamId
  | .unalignedOrOutOfPoolRegion | .overlappingCommitFrame | .writableCodeOrOutbox | .forbiddenRoleRegionPerm => true
  | .certDigestMismatch => false
theorem smmuChokepointCheck_sound {r : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert} (h : smmuChokepointCheck r q c = .ok) : SmmuManifestMeaning q c := by
  unfold smmuChokepointCheck at h; split at h; · cases h
  cases hv : verifyChokepointSmmuConfig q.config with
  | error _ => simp [hv] at h
  | ok _ =>
    simp only [hv] at h; cases hd : (c.manifestDigest != smmuManifestDigest q.config.manifest)
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨verifyChokepointSmmuConfig_sound hv, by simpa [bne_eq_false_iff_eq] using hd, fun exp hexp => ?_⟩
      simp only [hexp] at h; cases hEq : (smmuManifestDigest q.config.manifest == exp) <;> simp_all
    · simp [hd] at h
theorem smmuChokepointCheck_refuted {r : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert} {k : SmmuRefusalClause} {p : List Nat}
    (h : smmuChokepointCheck r q c = .refused k p) (hk : smmuRefusalRefutes k = true) : ∀ c', ¬ SmmuManifestMeaning q c' := by
  intro _ hMean; have hOkCfg := verifyChokepointSmmuConfig_complete hMean.safe
  unfold smmuChokepointCheck at h; split at h; · cases h
  simp only [hOkCfg] at h; cases hd : (c.manifestDigest != smmuManifestDigest q.config.manifest)
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    cases hexp : q.expectedDigest? with
    | none => simp [hexp] at h
    | some exp => simp only [hexp] at h; cases hEq : (smmuManifestDigest q.config.manifest == exp) <;>
                    simp only [hEq, ↓reduceIte, Bool.false_eq_true] at h <;> (cases h; try cases hk)
  · simp only [hd, ↓reduceIte] at h; cases h; cases hk
theorem smmuChokepointCheck_complete {q : SmmuManifestQuery} (hFrag : q.config.manifest.Fit) (hInh : ∃ c, SmmuManifestMeaning q c) :
    ∃ c r, smmuChokepointCheck r q c = .ok := by
  obtain ⟨_, hMean⟩ := hInh; refine ⟨⟨smmuManifestDigest q.config.manifest⟩, smmuRequiredGrade q, ?_⟩
  have hOkCfg := verifyChokepointSmmuConfig_complete hMean.safe; have hFitB := (manifestFitB_iff q.config.manifest).mpr hFrag
  have hNotLt : ¬ (smmuRequiredGrade q < smmuRequiredGrade q) := Nat.lt_irrefl _
  simp only [smmuChokepointCheck, hNotLt, decide_false, hFitB, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hOkCfg, bne_self_eq_false]
  cases hexp : q.expectedDigest? with | none => rfl | some exp => simp [hMean.pinnedOk exp hexp]
theorem smmuChokepointCheck_mono {r r' : Nat} {q : SmmuManifestQuery} {c : SmmuManifestCert}
    (hle : r ≤ r') (hDec : smmuChokepointCheck r q c ≠ .uncovered) : smmuChokepointCheck r' q c = smmuChokepointCheck r q c := by
  unfold smmuChokepointCheck at hDec ⊢; cases hFit : manifestFitB q.config.manifest <;> simp only [hFit] at hDec ⊢
  · simp at hDec
  · by_cases hlt : r < smmuRequiredGrade q; · simp [hlt] at hDec
    have hlt' : ¬ (r' < smmuRequiredGrade q) := by omega
    simp [hlt, hlt']
instance smmuChokepointJudge : Judge SmmuManifestQuery SmmuManifestCert where
  Clause := SmmuRefusalClause; Meaning := SmmuManifestMeaning; check := smmuChokepointCheck
  sound := smmuChokepointCheck_sound; refutes := smmuRefusalRefutes; refuted := smmuChokepointCheck_refuted
  Fragment q := q.config.manifest.Fit; complete := smmuChokepointCheck_complete; mono := smmuChokepointCheck_mono

/-! ## 5. Multi-Page Hardware 4-Level Radix Refinement & Table Non-Self-Modification -/
private theorem walkSmmuV3Stage2Detail_ok {m : SmmuManifest} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hComp : compileManifestToRadixArena m arenaBase maxFrames = .ok arena)
    {sid : StreamId} {iova len pa₀ : Nat} {acc : DmaAccess} {vmid : UInt16} {gran : PageGranule} {perm : IoPerm}
    (hOk : walkSmmuV3Stage2Detail arena sid iova len acc = .ok (pa₀, vmid, gran, perm)) :
    m.defaultDeny = true ∧ sid ≠ 0 ∧ sid ≠ wildcardStreamId ∧ 0 < len ∧ iova + len ≤ smmuAddrLimit48 ∧
      perm.permits acc = true ∧ vmid = UInt16.ofNat sid.toNat ∧
      ∃ pt ∈ m.streams, pt.streamId = sid ∧
        (∃ reg₀ ∈ pt.regions, perm = reg₀.perm ∧
          reg₀.iova.toNat ≤ (iova / gran.byteSize) * gran.byteSize ∧
          (iova / gran.byteSize) * gran.byteSize + gran.byteSize ≤ reg₀.iova.toNat + reg₀.size.toNat ∧
          pa₀ = reg₀.paddr.toNat + ((iova / gran.byteSize) * gran.byteSize - reg₀.iova.toNat) + iova % gran.byteSize) ∧
        (∀ off < len, ∃ reg ∈ pt.regions, reg.perm = perm ∧
          reg.iova.toNat ≤ iova + off ∧ iova + off < reg.iova.toNat + reg.size.toNat ∧
          reg.paddr.toNat ≤ pa₀ + off ∧ pa₀ + off < reg.paddr.toNat + reg.size.toNat) := by
  obtain ⟨_, hDeny, _, hAlPool, _, _, _, _, _, _, hEn, _⟩ := compileManifestToRadixArena_unpack hComp
  have hRoot := compiledArena_root_and_walk hComp sid
  unfold walkSmmuV3Stage2Detail at hOk; rw [hEn] at hOk
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
  split at hOk; · cases hOk
  rename_i hSidB; split at hOk; · cases hOk
  rename_i hLenB
  have hSidOk : sid ≠ 0 ∧ sid ≠ wildcardStreamId := by simpa only [Bool.or_eq_true, beq_iff_eq, not_or] using hSidB
  have hLenPos : 0 < len := Nat.pos_of_ne_zero (by simpa [beq_iff_eq] using hLenB)
  cases hLookSt : lookupStream m.streams sid with
  | none => rw [hLookSt] at hRoot; rw [hRoot] at hOk; cases hOk
  | some pt =>
    rw [hLookSt] at hRoot; obtain ⟨l0Pa, hDecRoot, hWalk⟩ := hRoot
    obtain ⟨hptMem, hptSid⟩ := lookupStream_some hLookSt
    have hAlPt := List.all_eq_true.mp hAlPool pt hptMem
    have hDisj := checkRegionsIovaDisjoint_sound ((Bool.and_eq_true _ _).mp hAlPt).1
    have hRegs := fun r hr => List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hAlPt).2 r hr
    rw [hDecRoot] at hOk; dsimp only [] at hOk
    split at hOk; · cases hOk
    rename_i hNot48; have hIova48 : iova + len ≤ smmuAddrLimit48 := by simpa using hNot48
    cases hW0 : walkSmmuV3RadixIova arena l0Pa.toNat iova with
    | none => rw [hW0] at hOk; cases hOk
    | some w0 =>
      obtain ⟨paW, granB, permW⟩ := w0; rw [hW0] at hOk; dsimp only [] at hOk
      cases hCont : checkContigPages arena l0Pa.toNat paW permW iova
          (iova / pageSize + 1) ((iova + len - 1) / pageSize - iova / pageSize) with
      | false => rw [hCont] at hOk; cases hOk
      | true =>
        rw [hCont] at hOk; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        by_cases hPerm : permW.permits acc = true
        · simp only [hPerm, ↓reduceIte] at hOk; injection hOk with hTuple
          obtain ⟨rfl, rfl, hGranEq, rfl⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hTuple
          have hW0Spec := hW0; rw [hWalk iova (by omega)] at hW0Spec
          cases htw0 : (regionsTouchWindow pt.regions ((iova / l0WinSize) * l0WinSize) l0WinSize &&
              regionsTouchWindow pt.regions ((iova / l1WinSize) * l1WinSize) l1WinSize) with
          | false => rw [htw0] at hW0Spec; simp at hW0Spec
          | true =>
            rw [htw0] at hW0Spec; simp only [↓reduceIte] at hW0Spec
            obtain ⟨reg₀, hreg₀Mem, gran₀, rfl, rfl, hCovLo, hCovHi, hPaEq⟩ := specLeafAt_some_region hW0Spec
            have hGran0 : (if gran₀.byteSize == hugeBlock2MiB then PageGranule.huge2MiB else .page4KiB) = gran₀ := by cases gran₀ <;> decide
            rw [hGran0] at hGranEq; subst hGranEq
            refine ⟨hDeny, hSidOk.1, hSidOk.2, hLenPos, hIova48, hPerm, rfl, pt, hptMem, hptSid,
              ⟨reg₀, hreg₀Mem, rfl, hCovLo, hCovHi, hPaEq⟩, fun off hoff => ?_⟩
            by_cases hp0 : (iova + off) / pageSize = iova / pageSize
            · have hInGran : (iova / gran₀.byteSize) * gran₀.byteSize ≤ iova ∧
                  iova + off < (iova / gran₀.byteSize) * gran₀.byteSize + gran₀.byteSize := by
                cases gran₀
                · simp only [PageGranule.byteSize] at *
                  have hd1 := Nat.div_add_mod iova 4096; have hd2 := Nat.div_add_mod (iova + off) 4096
                  have hm2 := Nat.mod_lt (iova + off) (by decide : 0 < 4096); simp only [pageSize] at hp0; omega
                · simp only [PageGranule.byteSize] at *
                  have hq1 := radix_step_base iova 4096; have hq2 := radix_step_base (iova + off) 4096
                  have hm1 := Nat.mod_lt (iova / 4096) (by decide : 0 < 512)
                  have hd1 := Nat.div_add_mod iova 4096; have hd2 := Nat.div_add_mod (iova + off) 4096
                  have hm2 := Nat.mod_lt (iova + off) (by decide : 0 < 4096); simp only [pageSize] at hp0; omega
              have hDivG : (iova / gran₀.byteSize) * gran₀.byteSize + iova % gran₀.byteSize = iova := by
                rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
              exact ⟨reg₀, hreg₀Mem, rfl, by omega, by omega, by omega, by omega⟩
            · have hpGe : iova / pageSize < (iova + off) / pageSize := by
                have hd1 := Nat.div_add_mod iova pageSize; have hd2 := Nat.div_add_mod (iova + off) pageSize
                have hm2 := Nat.mod_lt (iova + off) (by decide : 0 < pageSize)
                simp only [pageSize] at hp0 hd1 hd2 hm2 ⊢; omega
              have hpLe : (iova + off) / pageSize ≤ (iova + len - 1) / pageSize := Nat.div_le_div_right (by omega)
              let p := (iova + off) / pageSize
              obtain ⟨granP, hWP⟩ := checkContigPages_at hCont (k := p - (iova / pageSize + 1)) (by omega)
              rw [show iova / pageSize + 1 + (p - (iova / pageSize + 1)) = p by omega] at hWP
              have hp48 : p * pageSize + pageSize ≤ smmuAddrLimit48 := by
                have hd2 := Nat.div_add_mod (iova + off) pageSize; have hpDef : p = (iova + off) / pageSize := rfl
                simp only [hpDef, smmuAddrLimit48, pageSize] at hd2 hoff hIova48 ⊢; omega
              rw [hWalk (p * pageSize) (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hp48),
                specLeafAt_iff_lookup (iova := p * pageSize) (len := pageSize) hDisj hRegs (by decide)
                  (by rw [Nat.mul_mod_left, Nat.zero_add]; exact Nat.le_refl _)] at hWP
              cases hLP : lookupDmaRegion pt.regions (p * pageSize) pageSize with
              | none => rw [hLP] at hWP; cases hWP
              | some rp =>
                rw [hLP] at hWP; injection hWP with hT
                obtain ⟨hPaP, _, hPermEq⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hT
                obtain ⟨hrpMem, hrpLo, hrpHi⟩ := lookupDmaRegion_some hLP
                have hd2 := Nat.div_add_mod (iova + off) pageSize; have hm2 := Nat.mod_lt (iova + off) (by decide : 0 < pageSize)
                have hpDef : p = (iova + off) / pageSize := rfl
                have hGtP : iova ≤ p * pageSize := by have hd1 := Nat.div_add_mod iova pageSize; simp only [hpDef, pageSize] at hpGe hd1 ⊢; omega
                have hInP : p * pageSize ≤ iova + off ∧ iova + off < p * pageSize + pageSize := by simp only [hpDef, pageSize] at hd2 hm2 ⊢; omega
                exact ⟨rp, hrpMem, hPermEq, by omega, by omega, by omega, by omega⟩
        · simp [hPerm] at hOk
theorem walkSmmuV3Stage2_cross_page_escape_refused {m : SmmuManifest} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hComp : compileManifestToRadixArena m arenaBase maxFrames = .ok arena) {pt : Stage2IoPageTable} (hptMem : pt ∈ m.streams)
    {iova len p : Nat} (acc : DmaAccess) (hpLo : iova / pageSize ≤ p) (hpHi : p ≤ (iova + len - 1) / pageSize)
    (hBadPage : ∀ r ∈ pt.regions, r.iova.toNat ≤ p * pageSize → p * pageSize + pageSize ≤ r.iova.toNat + r.size.toNat → r.perm.permits acc = false) :
    (walkSmmuV3Stage2 arena pt.streamId iova len acc).isOk = false := by
  cases hOut : walkSmmuV3Stage2 arena pt.streamId iova len acc with
  | error _ => rfl
  | ok paOut =>
    exfalso; unfold walkSmmuV3Stage2 at hOut
    cases hDet : walkSmmuV3Stage2Detail arena pt.streamId iova len acc with
    | error _ => rw [hDet] at hOut; cases hOut
    | ok det =>
      obtain ⟨pa₀, vmid, gran, perm₀⟩ := det; obtain ⟨_, _, hNoWild, hAlPool, _⟩ := compileManifestToRadixArena_unpack hComp
      have hNodup : (m.streams.map Stage2IoPageTable.streamId).Nodup := decide_eq_true_eq.mp ((Bool.and_eq_true _ _).mp hNoWild).1
      obtain ⟨_, _, _, hLenPos, _, hPermOk, _, pt', hpt'Mem, hpt'Sid, _, hBytes⟩ := walkSmmuV3Stage2Detail_ok hComp hDet
      rw [nodup_streamId_eq hNodup hpt'Mem hptMem hpt'Sid] at hBytes
      let off := max iova (p * pageSize) - iova
      have hOffLt : off < len := by have hd := Nat.div_add_mod (iova + len - 1) pageSize; simp only [off, pageSize] at hd hpHi hLenPos ⊢; omega
      obtain ⟨reg, hregMem, hPermEq, hLoI, hHiI, _, _⟩ := hBytes off hOffLt
      have hrAl := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hAlPool pt hptMem)).2 reg hregMem
      simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrAl
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hrIA⟩, _⟩, hrSA⟩, _⟩ := hrAl
      have hMult : reg.iova.toNat % pageSize = 0 ∧ reg.size.toNat % pageSize = 0 := by
        cases hg : reg.granule <;> simp only [hg, PageGranule.byteSize, pageSize] at hrIA hrSA ⊢ <;> exact ⟨by omega, by omega⟩
      have hInP : p * pageSize ≤ iova + off ∧ iova + off < p * pageSize + pageSize := by
        have hd := Nat.div_add_mod iova pageSize; have hm := Nat.mod_lt iova (by decide : 0 < pageSize)
        simp only [off, pageSize] at hd hm hpLo ⊢; omega
      have hRegCovP : reg.iova.toNat ≤ p * pageSize ∧ p * pageSize + pageSize ≤ reg.iova.toNat + reg.size.toNat := by
        simp only [pageSize] at hMult hInP hLoI hHiI ⊢; exact ⟨by omega, by omega⟩
      rw [← hPermEq, hBadPage reg hregMem hRegCovP.1 hRegCovP.2] at hPermOk; cases hPermOk
/-- **Multi-Page Hardware-to-Spec Equivalence**: for every validated `ChokepointSmmuConfig` and
compiled `SmmuV3RadixArena`, the 4-level (`9+9+9+9+12`) Armv8 Stage-2 multi-page hardware walker
agrees **byte-for-byte** with `translateStage2Dma` across ALL `len : Nat` (no side hypotheses!). -/
theorem walkSmmuV3Stage2_refines_spec {cfg : ChokepointSmmuConfig} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hValid : verifyChokepointSmmuConfig cfg = .ok ())
    (hComp : compileManifestToRadixArena cfg.manifest arenaBase maxFrames = .ok arena)
    (sid : StreamId) (iova len : Nat) (acc : DmaAccess) :
    walkSmmuV3Stage2 arena sid iova len acc = translateStage2Dma cfg.manifest sid iova len acc := by
  have hSafe := verifyChokepointSmmuConfig_sound hValid
  obtain ⟨_, hDeny, _, _, _, _, _, _, _, _, hEn, _, _, hNonCB, _⟩ := compileManifestToRadixArena_unpack hComp
  have hNonCoalesce : ∀ pt ∈ cfg.manifest.streams, RegionsNonCoalescable pt.regions :=
    fun pt hpt => checkRegionsNonCoalescable_sound (List.all_eq_true.mp hNonCB pt hpt)
  by_cases hSidB : (sid == 0 || sid == wildcardStreamId) = true
  · simp [walkSmmuV3Stage2, walkSmmuV3Stage2Detail, translateStage2Dma, hEn, hDeny, hSidB]
  · simp only [Bool.not_eq_true] at hSidB
    by_cases hLen0 : len = 0
    · subst hLen0; simp [walkSmmuV3Stage2, walkSmmuV3Stage2Detail, translateStage2Dma, hEn, hDeny, hSidB]
    · have hLenPos : 0 < len := Nat.pos_of_ne_zero hLen0; have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr hLen0
      have hRoot := compiledArena_root_and_walk hComp sid
      cases hLookSt : lookupStream cfg.manifest.streams sid with
      | none => rw [hLookSt] at hRoot; simp [walkSmmuV3Stage2, walkSmmuV3Stage2Detail, translateStage2Dma, hEn, hDeny, hSidB, hLenB, hRoot, hLookSt]
      | some pt =>
        obtain ⟨hptMem, hptSid⟩ := lookupStream_some hLookSt
        cases hLookReg : lookupDmaRegion pt.regions iova len with
        | some reg => obtain ⟨hregMem, hLo, hHi⟩ := lookupDmaRegion_some hLookReg
                      rw [← hptSid]; exact walkSmmuV3Stage2_agrees_on_region hComp hptMem hregMem hLenPos hLo hHi acc
        | none =>
          rw [hLookSt] at hRoot; obtain ⟨l0Pa, hDecRoot, hWalk⟩ := hRoot
          unfold walkSmmuV3Stage2 walkSmmuV3Stage2Detail translateStage2Dma
          simp only [hEn, hDeny, hSidB, hLenB, hDecRoot, hLookSt, hLookReg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hIova48 : iova + len ≤ smmuAddrLimit48
          · simp only [hIova48, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            have hDisj := checkRegionsIovaDisjoint_sound (hSafe.alignedInPool pt hptMem).1
            have hRegs := (hSafe.alignedInPool pt hptMem).2
            cases hW0 : walkSmmuV3RadixIova arena l0Pa.toNat iova with
            | none => rfl
            | some w0 =>
              obtain ⟨pa₀, granB, perm₀⟩ := w0; dsimp only []
              have hContF : checkContigPages arena l0Pa.toNat pa₀ perm₀ iova
                  (iova / pageSize + 1) ((iova + len - 1) / pageSize - iova / pageSize) = false := by
                refine Bool.eq_false_iff.mpr fun hCont => ?_
                have hW0' := hW0
                rw [hWalk iova (by omega), specLeafAt_iff_lookup (iova := iova) (len := 1) hDisj hRegs (by decide)
                  (Nat.succ_le_of_lt (Nat.mod_lt iova (by decide)))] at hW0'
                cases hL0 : lookupDmaRegion pt.regions iova 1 with
                | none => rw [hL0] at hW0'; cases hW0'
                | some reg₀ =>
                  rw [hL0] at hW0'; injection hW0' with hT
                  obtain ⟨hPa₀Eq, _, hPerm₀Eq⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hT
                  obtain ⟨hr0Mem, hr0Lo, hr0Hi⟩ := lookupDmaRegion_some hL0
                  have hr0Al := hRegs reg₀ hr0Mem
                  simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr0Al
                  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hrIA⟩, _⟩, hrSA⟩, _⟩ := hr0Al
                  have hMult : reg₀.iova.toNat % pageSize = 0 ∧ reg₀.size.toNat % pageSize = 0 := by
                    cases hg : reg₀.granule <;> simp only [hg, PageGranule.byteSize, pageSize] at hrIA hrSA ⊢ <;> exact ⟨by omega, by omega⟩
                  have hNotSub : ¬ (reg₀.iova.toNat ≤ iova ∧ iova + len ≤ reg₀.iova.toNat + reg₀.size.toNat) :=
                    fun hc => absurd (decide_eq_true hc) (List.find?_eq_none.mp hLookReg reg₀ hr0Mem)
                  have hSpill : reg₀.iova.toNat + reg₀.size.toNat < iova + len := by omega
                  let endIova := reg₀.iova.toNat + reg₀.size.toNat
                  let pB := endIova / pageSize
                  have hpBMul : pB * pageSize = endIova := by
                    simp only [pB, endIova, pageSize] at hMult ⊢; omega
                  have hpBGe : iova / pageSize + 1 ≤ pB := by
                    have hd := Nat.div_add_mod iova pageSize
                    simp only [pB, endIova, pageSize] at hd hMult hr0Hi ⊢; omega
                  have hpBLe : pB ≤ (iova + len - 1) / pageSize := by
                    have h2 := Nat.div_le_div_right (c := pageSize) (show pB * pageSize ≤ iova + len - 1 by omega)
                    rw [Nat.mul_div_cancel _ (by decide : 0 < pageSize)] at h2; exact h2
                  obtain ⟨granP, hWP⟩ := checkContigPages_at hCont (k := pB - (iova / pageSize + 1)) (by omega)
                  rw [show iova / pageSize + 1 + (pB - (iova / pageSize + 1)) = pB by omega] at hWP
                  have hpB48 : pB * pageSize + pageSize ≤ smmuAddrLimit48 := by
                    have hdLast := Nat.div_add_mod (iova + len - 1) pageSize
                    simp only [smmuAddrLimit48, pageSize] at hpBMul hSpill hpBLe hdLast hIova48 ⊢; omega
                  rw [hWalk (pB * pageSize) (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hpB48),
                    specLeafAt_iff_lookup (iova := pB * pageSize) (len := pageSize) hDisj hRegs (by decide)
                      (by rw [Nat.mul_mod_left, Nat.zero_add]; exact Nat.le_refl _)] at hWP
                  cases hLP : lookupDmaRegion pt.regions (pB * pageSize) pageSize with
                  | none => rw [hLP] at hWP; cases hWP
                  | some reg₁ =>
                    rw [hLP] at hWP; injection hWP with hTP
                    obtain ⟨hPa₁Eq, _, hPerm₁Eq⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hTP
                    obtain ⟨hr1Mem, hr1Lo, hr1Hi⟩ := lookupDmaRegion_some hLP
                    have hPagePos : 0 < pageSize := by decide
                    have hr1EqEnd : reg₁.iova.toNat = endIova :=
                      if hEq : reg₁.iova.toNat = endIova then hEq else False.elim (by
                        have hSame := hDisj reg₀ hr0Mem reg₁ hr1Mem (by omega) (by omega)
                        subst hSame; dsimp only [endIova] at hpBMul; omega)
                    exact hNonCoalesce pt hptMem reg₀ hr0Mem reg₁ hr1Mem hr1EqEnd.symm (by omega) (hPerm₀Eq.trans hPerm₁Eq.symm)
              rw [hContF]; rfl
          · simp [hIova48]
theorem dma_cannot_write_smmu_tables {cfg : ChokepointSmmuConfig} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hValid : verifyChokepointSmmuConfig cfg = .ok ()) (hComp : compileManifestToRadixArena cfg.manifest arenaBase maxFrames = .ok arena)
    (ops : List PeripheralDmaOp) (mem : Nat → UInt8) (pa : Nat) (hTablePa : SmmuTablePhysAddr arena pa) :
    (∃ pr ∈ cfg.manifest.protectedRanges, pr.classTag = .kernelPageTable ∧ pr.basePaddr.toNat ≤ pa ∧ pa < pr.basePaddr.toNat + pr.size.toNat) ∧
    (execSmmuV3HardwareDmaBurst arena mem ops).1 pa = mem pa ∧ (execStage2DmaBurst cfg.manifest mem ops).1 pa = mem pa := by
  have hSafe := verifyChokepointSmmuConfig_sound hValid
  obtain ⟨_, _, _, _, _, _, _, _, hProtB, _, _, hAbEq, hCap, _⟩ := compileManifestToRadixArena_unpack hComp
  obtain ⟨pr, hprMem, hprOk⟩ := List.any_eq_true.mp hProtB; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hprOk
  have hInArena := smmuTablePhysAddr_in_arena hCap hTablePa; rw [hAbEq] at hInArena
  have hInPr : pr.basePaddr.toNat ≤ pa ∧ pa < pr.basePaddr.toNat + pr.size.toNat := by omega
  have hNeCom : pr.classTag ≠ .commitPrivate := by rw [hprOk.1]; decide
  have hHwPres : ∀ (xs : List PeripheralDmaOp) (m0 : Nat → UInt8), (execSmmuV3HardwareDmaBurst arena m0 xs).1 pa = m0 pa := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons op xs ih =>
      intro m0; simp only [execSmmuV3HardwareDmaBurst]; rw [ih]; cases op with
      | read _ _ _ => simp [execSmmuV3HardwareDmaOp]; split <;> rfl
      | write sid iova payload =>
        dsimp only [execSmmuV3HardwareDmaOp, walkSmmuV3Stage2]
        cases hw : walkSmmuV3Stage2Detail arena sid iova payload.size .dmaWrite with
        | error _ => rfl
        | ok det =>
          obtain ⟨basePa, _, _, _⟩ := det; obtain ⟨-, -, -, -, -, -, -, pt, hpt, -, -, hBytes⟩ := walkSmmuV3Stage2Detail_ok hComp hw
          exact authorized_dma_write_disjoint_range hSafe hprMem hNeCom basePa payload
            (fun i hi => by obtain ⟨reg, hreg, -, _, _, hlo, hhi⟩ := hBytes i hi; exact ⟨pt, hpt, reg, hreg, hlo, hhi⟩) m0 hInPr
  have hSpecPres : ∀ (xs : List PeripheralDmaOp) (m0 : Nat → UInt8), (execStage2DmaBurst cfg.manifest m0 xs).1 pa = m0 pa := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons op xs ih =>
      intro m0; simp only [execStage2DmaBurst]; rw [ih]; cases op with
      | read _ _ _ => simp [execStage2DmaOp]; split <;> rfl
      | write sid iova payload =>
        dsimp only [execStage2DmaOp]
        cases ht : translateStage2Dma cfg.manifest sid iova payload.size .dmaWrite with
        | error _ => rfl
        | ok basePa =>
          obtain ⟨-, -, -, _, pt, hpt, -, reg, hreg, hlo, hhi, -, rfl⟩ := translateStage2Dma_ok ht
          exact authorized_dma_write_disjoint_range hSafe hprMem hNeCom _ payload (fun i hi => ⟨pt, hpt, reg, hreg, by omega, by omega⟩) m0 hInPr
  exact ⟨⟨pr, hprMem, hprOk.1, hInPr.1, hInPr.2⟩, hHwPres ops mem, hSpecPres ops mem⟩

/-! ## 6. Stateful IOTLB & Mechanical `CMD_CFGI_STE`/`CMD_TLBI_S2_IPA`/`CMD_SYNC` Epoch Safety -/
inductive SmmuCmd where
  | cfgiSte (sid : StreamId) (leaf : Bool) | tlbiS2Ipa (vmid : UInt16) (ipa : UInt64) (leaf : Bool)
  | tlbiS12Vmall (vmid : UInt16) | sync deriving DecidableEq, Repr
/-- Arm SMMUv3 IHI 0070 §4.3.1 / §4.4.3.1–2 / §4.7.3 128-bit command encoder (`VMID` in `[47:32]`). -/
def encodeSmmuCmd : SmmuCmd → Option (UInt64 × UInt64)
  | .cfgiSte sid leaf => some (UInt64.ofNat (0x03 + sid.toNat * (2 ^ 32)), if leaf then 1 else 0)
  | .tlbiS2Ipa vmid ipa leaf =>
    if decide (ipa.toNat ≥ smmuAddrLimit48) || ipa.toNat % pageSize != 0 then none
    else some (UInt64.ofNat (0x2a + vmid.toNat * (2 ^ 32)), UInt64.ofNat (ipa.toNat + (if leaf then 1 else 0)))
  | .tlbiS12Vmall vmid => some (UInt64.ofNat (0x28 + vmid.toNat * (2 ^ 32)), 0) | .sync => some (0x46, 0)
def decodeSmmuCmd (w : UInt64 × UInt64) : Option SmmuCmd :=
  let (q0, q1) := w; let op := q0.toNat % 256
  if op == 0x03 then
    if (q0.toNat / 256) % (2 ^ 24) != 0 || q1.toNat > 1 then none else some (.cfgiSte (UInt32.ofNat (q0.toNat / (2 ^ 32))) (q1.toNat == 1))
  else if op == 0x2a then
    if (q0.toNat / 256) % (2 ^ 24) != 0 || q0.toNat / (2 ^ 48) != 0 || decide (q1.toNat ≥ smmuAddrLimit48) || (q1.toNat % pageSize) > 1 then none
    else some (.tlbiS2Ipa (UInt16.ofNat ((q0.toNat / (2 ^ 32)) % (2 ^ 16))) (UInt64.ofNat ((q1.toNat / pageSize) * pageSize)) (q1.toNat % pageSize == 1))
  else if op == 0x28 then
    if (q0.toNat / 256) % (2 ^ 24) != 0 || q0.toNat / (2 ^ 48) != 0 || q1.toNat != 0 then none
    else some (.tlbiS12Vmall (UInt16.ofNat ((q0.toNat / (2 ^ 32)) % (2 ^ 16))))
  else if op == 0x46 then if q0.toNat != 0x46 || q1.toNat != 0 then none else some .sync else none
private theorem u32_toNat_of_lt {n : Nat} (h : n < 4294967296) : (UInt32.ofNat n).toNat = n := UInt32.toNat_ofNat_of_lt h
theorem decodeSmmuCmd_encodeSmmuCmd {c : SmmuCmd} {w : UInt64 × UInt64}
    (hEnc : encodeSmmuCmd c = some w) : decodeSmmuCmd w = some c := by
  cases c with
  | cfgiSte sid leaf =>
    simp only [encodeSmmuCmd, Option.some.injEq] at hEnc; subst hEnc
    have hSidLt : sid.toNat < 4294967296 := sid.toBitVec.isLt
    have hQ0 : (UInt64.ofNat (0x03 + sid.toNat * 2 ^ 32)).toNat = 0x03 + sid.toNat * 2 ^ 32 :=
      u64_toNat_of_lt (by simp only [Nat.reducePow]; omega)
    have hSidId : UInt32.ofNat ((0x03 + sid.toNat * 2 ^ 32) / 2 ^ 32) = sid :=
      UInt32.toNat_inj.mp (by rw [u32_toNat_of_lt (by simp only [Nat.reducePow]; omega)]; simp only [Nat.reducePow]; omega)
    have hOp : ((0x03 + sid.toNat * 2 ^ 32) % 256 == 0x03) = true := beq_iff_eq.mpr (by simp only [Nat.reducePow]; omega)
    have hG : (((0x03 + sid.toNat * 2 ^ 32) / 256) % 2 ^ 24 != 0 || (if leaf then (1 : UInt64) else 0).toNat > 1) = false := by
      cases leaf <;> (simp only [↓reduceIte, Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not, Nat.reducePow]; exact ⟨by omega, by decide⟩)
    have hLf : ((if leaf then (1 : UInt64) else 0).toNat == 1) = leaf := by cases leaf <;> decide
    unfold decodeSmmuCmd; dsimp only []; rw [hQ0, hOp]; simp only [↓reduceIte]; rw [hG, hSidId, hLf]; rfl
  | tlbiS2Ipa vmid ipa leaf =>
    dsimp only [encodeSmmuCmd] at hEnc; split at hEnc; · cases hEnc
    rename_i hIpaOk; simp only [Option.some.injEq] at hEnc; subst hEnc
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, not_or, Nat.not_le, Classical.not_not] at hIpaOk
    obtain ⟨hIpaLt, hIpaAl⟩ := hIpaOk
    have hBit : (if leaf then 1 else 0) ≤ 1 := by cases leaf <;> decide
    have hVmidLt : vmid.toNat < 65536 := vmid.toBitVec.isLt
    have hQ0 : (UInt64.ofNat (0x2a + vmid.toNat * 2 ^ 32)).toNat = 0x2a + vmid.toNat * 2 ^ 32 :=
      u64_toNat_of_lt (by simp only [Nat.reducePow]; omega)
    have hQ1 : (UInt64.ofNat (ipa.toNat + (if leaf then 1 else 0))).toNat = ipa.toNat + (if leaf then 1 else 0) :=
      u64_toNat_of_lt (by simp only [smmuAddrLimit48] at hIpaLt; omega)
    have hVmidId : UInt16.ofNat (((0x2a + vmid.toNat * 2 ^ 32) / 2 ^ 32) % 2 ^ 16) = vmid :=
      UInt16.toNat_inj.mp (by rw [u16_toNat_of_lt (by simp only [Nat.reducePow]; omega)]; simp only [Nat.reducePow]; omega)
    have hOp0 : ((0x2a + vmid.toNat * 2 ^ 32) % 256 == 0x03) = false := beq_eq_false_iff_ne.mpr (by simp only [Nat.reducePow]; omega)
    have hOp1 : ((0x2a + vmid.toNat * 2 ^ 32) % 256 == 0x2a) = true := beq_iff_eq.mpr (by simp only [Nat.reducePow]; omega)
    have hG : ((((0x2a + vmid.toNat * 2 ^ 32) / 256) % 2 ^ 24 != 0 || (0x2a + vmid.toNat * 2 ^ 32) / 2 ^ 48 != 0 ||
        decide (ipa.toNat + (if leaf then 1 else 0) ≥ smmuAddrLimit48)) ||
        (ipa.toNat + (if leaf then 1 else 0)) % pageSize > 1) = false := by
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not, Nat.reducePow]
      simp only [smmuAddrLimit48, pageSize] at hIpaLt hIpaAl ⊢; exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
    have hIpaId : UInt64.ofNat (((ipa.toNat + (if leaf then 1 else 0)) / pageSize) * pageSize) = ipa :=
      UInt64.toNat_inj.mp (by
        rw [u64_toNat_of_lt (by simp only [smmuAddrLimit48, pageSize] at hIpaLt hIpaAl ⊢; omega)]
        simp only [pageSize] at hIpaAl ⊢; omega)
    have hLf : ((ipa.toNat + (if leaf then 1 else 0)) % pageSize == 1) = leaf := by
      cases leaf
      · exact beq_eq_false_iff_ne.mpr (by simp only [Bool.false_eq_true, ↓reduceIte, pageSize] at hIpaAl ⊢; omega)
      · exact beq_iff_eq.mpr (by simp only [↓reduceIte, pageSize] at hIpaAl ⊢; omega)
    unfold decodeSmmuCmd; dsimp only []; rw [hQ0, hQ1, hOp0, hOp1]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hG, hVmidId, hIpaId, hLf]; rfl
  | tlbiS12Vmall vmid =>
    simp only [encodeSmmuCmd, Option.some.injEq] at hEnc; subst hEnc
    have hVmidLt : vmid.toNat < 65536 := vmid.toBitVec.isLt
    have hQ0 : (UInt64.ofNat (0x28 + vmid.toNat * 2 ^ 32)).toNat = 0x28 + vmid.toNat * 2 ^ 32 :=
      u64_toNat_of_lt (by simp only [Nat.reducePow]; omega)
    have hVmidId : UInt16.ofNat (((0x28 + vmid.toNat * 2 ^ 32) / 2 ^ 32) % 2 ^ 16) = vmid :=
      UInt16.toNat_inj.mp (by rw [u16_toNat_of_lt (by simp only [Nat.reducePow]; omega)]; simp only [Nat.reducePow]; omega)
    have hOp0 : ((0x28 + vmid.toNat * 2 ^ 32) % 256 == 0x03) = false := beq_eq_false_iff_ne.mpr (by simp only [Nat.reducePow]; omega)
    have hOp1 : ((0x28 + vmid.toNat * 2 ^ 32) % 256 == 0x2a) = false := beq_eq_false_iff_ne.mpr (by simp only [Nat.reducePow]; omega)
    have hOp2 : ((0x28 + vmid.toNat * 2 ^ 32) % 256 == 0x28) = true := beq_iff_eq.mpr (by simp only [Nat.reducePow]; omega)
    have hG : ((((0x28 + vmid.toNat * 2 ^ 32) / 256) % 2 ^ 24 != 0 ||
        (0x28 + vmid.toNat * 2 ^ 32) / 2 ^ 48 != 0) || ((0 : UInt64).toNat != 0)) = false := by
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, Nat.reducePow]; exact ⟨⟨by omega, by omega⟩, rfl⟩
    unfold decodeSmmuCmd; dsimp only []; rw [hQ0, hOp0, hOp1, hOp2]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hG, hVmidId]; rfl
  | sync => simp only [encodeSmmuCmd, Option.some.injEq] at hEnc; subst hEnc; rfl
structure CachedTlbiEntry where
  (streamId : StreamId) (vmid : UInt16) (iovaBase paddrBase : UInt64) (granule : PageGranule) (perm : IoPerm) (epoch : Nat) deriving DecidableEq, Repr
structure SmmuCmdQueueState where (pending synced : List SmmuCmd) (iotlb : List CachedTlbiEntry) deriving DecidableEq, Repr
/-- Arm SMMUv3 IHI 0070 §4.3.1 / §4.4.3: `CMD_CFGI_STE` flushes STE cache only; `CMD_TLBI_S2_IPA` evicts overlapping leaves (`4 KiB`/`2 MiB`). -/
def cmdEvictsEntry : SmmuCmd → CachedTlbiEntry → Bool
  | .cfgiSte _ _, _ | .sync, _ => false
  | .tlbiS12Vmall vmid, e => e.vmid == vmid
  | .tlbiS2Ipa vmid ipa _, e => e.vmid == vmid && !rangesDisjointB e.iovaBase.toNat e.granule.byteSize ipa.toNat pageSize
def stepSmmuCmd (q : SmmuCmdQueueState) : SmmuCmd → SmmuCmdQueueState
  | .sync => ⟨[], q.synced ++ q.pending ++ [.sync], q.iotlb.filter fun e => !q.pending.any (fun c => cmdEvictsEntry c e)⟩
  | c => ⟨q.pending ++ [c], q.synced, q.iotlb⟩
def runSmmuCmds (q : SmmuCmdQueueState) (cmds : List SmmuCmd) : SmmuCmdQueueState := cmds.foldl stepSmmuCmd q
def runRawSmmuCmds (q : SmmuCmdQueueState) (raw : List (UInt64 × UInt64)) : Option SmmuCmdQueueState :=
  raw.foldlM (fun st w => (decodeSmmuCmd w).map (stepSmmuCmd st)) q
theorem tlbi_sync_evicts_cached_entry (q : SmmuCmdQueueState) (e : CachedTlbiEntry) (ipa : UInt64)
    (hOverlap : rangesDisjointB e.iovaBase.toNat e.granule.byteSize ipa.toNat pageSize = false) :
    e ∉ (runSmmuCmds q [.tlbiS2Ipa e.vmid ipa false, .sync]).iotlb := by
  simp only [runSmmuCmds, List.foldl, stepSmmuCmd, List.mem_filter, Bool.not_eq_true']
  rintro ⟨_, hAny⟩; have hEv : cmdEvictsEntry (.tlbiS2Ipa e.vmid ipa false) e = true := by simp [cmdEvictsEntry, hOverlap]
  have hHit : ((q.pending ++ [SmmuCmd.tlbiS2Ipa e.vmid ipa false]).any fun c => cmdEvictsEntry c e) = true :=
    List.any_eq_true.mpr ⟨SmmuCmd.tlbiS2Ipa e.vmid ipa false, List.mem_append_right _ List.mem_cons_self, hEv⟩
  rw [hHit] at hAny; cases hAny
private theorem runSmmuCmds_evicts_synced (cmds : List SmmuCmd) :
    ∀ (q : SmmuCmdQueueState), (∀ c ∈ q.synced, ∀ e ∈ q.iotlb, cmdEvictsEntry c e = false) →
      let q' := runSmmuCmds q cmds; (∀ e ∈ q'.iotlb, e ∈ q.iotlb) ∧ ∀ c ∈ q'.synced, ∀ e ∈ q'.iotlb, cmdEvictsEntry c e = false := by
  induction cmds with
  | nil => intro q hInv; exact ⟨fun _ h => h, hInv⟩
  | cons cmd cs ih =>
    intro q hInv; simp only [runSmmuCmds, List.foldl_cons]
    have hStep : (∀ e ∈ (stepSmmuCmd q cmd).iotlb, e ∈ q.iotlb) ∧
        ∀ c ∈ (stepSmmuCmd q cmd).synced, ∀ e ∈ (stepSmmuCmd q cmd).iotlb, cmdEvictsEntry c e = false := by
      cases cmd with
      | sync =>
        simp only [stepSmmuCmd, List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true]
        exact ⟨fun _ h => h.1, fun c hc e ⟨heMem, heNoPend⟩ => (List.mem_append.mp hc).elim
          (fun hSP => (List.mem_append.mp hSP).elim (fun hS => hInv c hS e heMem) (fun hP => heNoPend c hP))
          (fun hSy => by rcases List.mem_singleton.mp hSy with rfl; rfl)⟩
      | _ => exact ⟨fun _ h => h, hInv⟩
    obtain ⟨hSub₂, hInv₂⟩ := ih (stepSmmuCmd q cmd) hStep.2; exact ⟨fun e he => hStep.1 e (hSub₂ e he), hInv₂⟩
def syncedHasCfgiSte (synced : List SmmuCmd) (sid : StreamId) : Bool :=
  synced.any fun c => c == .cfgiSte sid false
def cmdsAfterSync : List SmmuCmd → Option (List SmmuCmd)
  | [] => none | .sync :: cs => some cs | _ :: cs => cmdsAfterSync cs
def cmdsAfterCfgi : List SmmuCmd → StreamId → Option (List SmmuCmd)
  | [], _ => none | c :: cs, sid => if c == .cfgiSte sid false then cmdsAfterSync cs else cmdsAfterCfgi cs sid
private theorem sub_of_cmdsAfterSync {cmds tail : List SmmuCmd} (h : cmdsAfterSync cmds = some tail) : ∀ x ∈ tail, x ∈ cmds := by
  induction cmds with
  | nil => cases h
  | cons c cs ih =>
    cases c <;> dsimp only [cmdsAfterSync] at h <;>
      first | (injection h with h'; subst h'; exact fun _ hx => List.mem_cons_of_mem _ hx) | exact fun x hx => List.mem_cons_of_mem _ (ih h x hx)
private theorem mem_of_cmdsAfterCfgi {cmds tail : List SmmuCmd} {sid : StreamId}
    (h : cmdsAfterCfgi cmds sid = some tail) : .cfgiSte sid false ∈ cmds ∧ ∀ x ∈ tail, x ∈ cmds := by
  induction cmds with
  | nil => cases h
  | cons c cs ih =>
    dsimp only [cmdsAfterCfgi] at h; by_cases hEq : c == .cfgiSte sid false
    · rw [hEq] at h; simp only [↓reduceIte] at h
      exact ⟨beq_iff_eq.mp hEq ▸ List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ (sub_of_cmdsAfterSync h x hx)⟩
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := ih h; exact ⟨List.mem_cons_of_mem _ h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx)⟩
def syncedCfgiPrecedesVmall (synced : List SmmuCmd) (sid : StreamId) (vmid : UInt16) : Bool :=
  match cmdsAfterCfgi synced sid with | none => false | some tail => tail.any (· == .tlbiS12Vmall vmid)
def syncedCoversRegionTlbi (synced : List SmmuCmd) (vmid : UInt16) (reg : Stage2DmaRegion) : Bool :=
  let pages := reg.size.toNat / pageSize
  decide (0 < pages) && decide (reg.iova.toNat + reg.size.toNat ≤ smmuAddrLimit48) &&
    (reg.iova.toNat % pageSize == 0) && (reg.size.toNat % pageSize == 0) &&
    (List.range pages).all fun k =>
      synced.any fun c => c == .tlbiS12Vmall vmid || c == .tlbiS2Ipa vmid (UInt64.ofNat (reg.iova.toNat + k * pageSize)) false
def reconfigQueueValidB (iotlb : List CachedTlbiEntry) (cmds : List SmmuCmd) (sid : StreamId) (oldVmid : UInt16) (oldReg : Stage2DmaRegion) : Bool :=
  let qOut := runSmmuCmds ⟨[], [], iotlb⟩ cmds
  qOut.pending.isEmpty && match cmdsAfterCfgi qOut.synced sid with
  | none => false | some tail => syncedCoversRegionTlbi tail oldVmid oldReg
/-- Mechanical Command-Queue Eviction: `reconfigQueueValidB` drains `pending`, orders `CMD_CFGI_STE` before `CMD_TLBI_*`, and evicts `oldReg`. -/
theorem reconfigQueueValidB_evicts_unmapped_region {iotlb : List CachedTlbiEntry} {cmds : List SmmuCmd}
    {sid : StreamId} {oldVmid : UInt16} {oldReg : Stage2DmaRegion}
    (hValidQ : reconfigQueueValidB iotlb cmds sid oldVmid oldReg = true) :
    let qOut := runSmmuCmds ⟨[], [], iotlb⟩ cmds
    qOut.pending = [] ∧ syncedHasCfgiSte qOut.synced sid = true ∧
    (∀ e ∈ qOut.iotlb, e ∈ iotlb ∧ (e.vmid = oldVmid → rangesDisjointB e.iovaBase.toNat e.granule.byteSize oldReg.iova.toNat oldReg.size.toNat = true)) := by
  obtain ⟨hSub, hNoEv⟩ := runSmmuCmds_evicts_synced cmds ⟨[], [], iotlb⟩ (fun _ hc => nomatch hc)
  dsimp only [reconfigQueueValidB] at hValidQ; simp only [Bool.and_eq_true] at hValidQ; obtain ⟨hPend, hAfter⟩ := hValidQ
  cases hTail : cmdsAfterCfgi (runSmmuCmds ⟨[], [], iotlb⟩ cmds).synced sid with
  | none => rw [hTail] at hAfter; cases hAfter
  | some tail =>
    rw [hTail] at hAfter; obtain ⟨hCfgiMem, hTailSub⟩ := mem_of_cmdsAfterCfgi hTail
    have hCfgi : syncedHasCfgiSte (runSmmuCmds ⟨[], [], iotlb⟩ cmds).synced sid = true :=
      List.any_eq_true.mpr ⟨_, hCfgiMem, beq_self_eq_true _⟩
    refine ⟨List.isEmpty_iff.mp hPend, hCfgi, fun e he => ⟨hSub e he, fun hVmidEq => ?_⟩⟩
    by_cases hDisj : rangesDisjointB e.iovaBase.toNat e.granule.byteSize oldReg.iova.toNat oldReg.size.toNat = true
    · exact hDisj
    · exfalso; simp only [rangesDisjointB, Bool.not_eq_true, decide_eq_false_iff_not, not_or, Nat.not_le] at hDisj
      obtain ⟨h1, h2, _, _⟩ := hDisj
      simp only [syncedCoversRegionTlbi, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hAfter
      obtain ⟨⟨⟨⟨_, hI48⟩, hrIA⟩, hrSA⟩, hAllPages⟩ := hAfter
      let x := max e.iovaBase.toNat oldReg.iova.toNat; let k := (x - oldReg.iova.toNat) / pageSize
      have hxLoE : e.iovaBase.toNat ≤ x := Nat.le_max_left _ _; have hxLoR : oldReg.iova.toNat ≤ x := Nat.le_max_right _ _
      have hxHiE : x < e.iovaBase.toNat + e.granule.byteSize := by have := PageGranule.byteSize_pos e.granule; dsimp [x]; omega
      have hxHiR : x < oldReg.iova.toNat + oldReg.size.toNat := by dsimp [x]; omega
      have hkLt : k < oldReg.size.toNat / pageSize := by
        have hkDef : k = (x - oldReg.iova.toNat) / pageSize := rfl; simp only [hkDef, pageSize] at hxLoR hxHiR hrSA ⊢; omega
      obtain ⟨cPage, hcPageMem, hcPageKind⟩ := List.any_eq_true.mp (hAllPages k (List.mem_range.mpr hkLt))
      have hEvF := hNoEv cPage (hTailSub cPage hcPageMem) e he
      rcases (Bool.or_eq_true _ _).mp hcPageKind with hVmall | hIpa
      · rw [beq_iff_eq.mp hVmall] at hEvF; simp [cmdEvictsEntry, hVmidEq] at hEvF
      · rw [beq_iff_eq.mp hIpa] at hEvF; dsimp only [cmdEvictsEntry] at hEvF
        have hIpaNat : (UInt64.ofNat (oldReg.iova.toNat + k * pageSize)).toNat = oldReg.iova.toNat + k * pageSize :=
          u64_toNat_of_lt (by simp only [smmuAddrLimit48, pageSize] at hI48 hkLt ⊢; omega)
        have hPageOv : rangesDisjointB e.iovaBase.toNat e.granule.byteSize (oldReg.iova.toNat + k * pageSize) pageSize = false := by
          have hd := Nat.div_add_mod (x - oldReg.iova.toNat) pageSize; have hm := Nat.mod_lt (x - oldReg.iova.toNat) (by decide : 0 < pageSize)
          have hkDef : k = (x - oldReg.iova.toNat) / pageSize := rfl; have hGPos := PageGranule.byteSize_pos e.granule
          unfold rangesDisjointB; simp only [decide_eq_false_iff_not, not_or]; simp only [hkDef, pageSize] at hd hm hxLoE hxLoR hxHiE hGPos ⊢; omega
        rw [hVmidEq, beq_self_eq_true, Bool.true_and, hIpaNat, hPageOv] at hEvF; cases hEvF
def lookupIotlb (iotlb : List CachedTlbiEntry) (sid : StreamId) (iova len : Nat) : Option CachedTlbiEntry :=
  iotlb.find? fun e => e.streamId == sid && decide (e.iovaBase.toNat ≤ iova ∧ iova + len ≤ e.iovaBase.toNat + e.granule.byteSize)
def translateWithIotlb (iotlb : List CachedTlbiEntry) (arena : SmmuV3RadixArena)
    (epoch : Nat) (sid : StreamId) (iova len : Nat) (acc : DmaAccess) : Except SmmuDmaFault Nat × List CachedTlbiEntry :=
  if !arena.smmuEnabled then (.error .bypassModeDisabled, iotlb)
  else if sid == 0 || sid == wildcardStreamId then (.error (.invalidStreamId sid), iotlb)
  else if len == 0 then (.error (.zeroOrUnmappedIova sid iova len), iotlb)
  else match lookupIotlb iotlb sid iova len with
    | some e => if e.perm.permits acc then (.ok (e.paddrBase.toNat + (iova - e.iovaBase.toNat)), iotlb)
                else (.error (.permissionFault sid acc e.perm), iotlb)
    | none => match walkSmmuV3Stage2Detail arena sid iova len acc with
      | .error err => (.error err, iotlb)
      | .ok (pa, vmid, gran, perm) =>
        let iovaBase := (iova / gran.byteSize) * gran.byteSize
        (.ok pa, ⟨sid, vmid, UInt64.ofNat iovaBase, UInt64.ofNat (pa - (iova % gran.byteSize)), gran, perm, epoch⟩ :: iotlb)
def execIotlbHardwareDmaOp (arena : SmmuV3RadixArena) (epoch : Nat)
    (iotlb : List CachedTlbiEntry) (mem : Nat → UInt8) : PeripheralDmaOp → (Nat → UInt8) × List CachedTlbiEntry × Option ByteArray
  | .read sid iova len =>
    let (res, iotlb') := translateWithIotlb iotlb arena epoch sid iova len .dmaRead
    match res with | .ok pa => (mem, iotlb', some (readPhys mem pa len)) | .error _ => (mem, iotlb', none)
  | .write sid iova payload =>
    let (res, iotlb') := translateWithIotlb iotlb arena epoch sid iova payload.size .dmaWrite
    match res with | .ok pa => (writePhys mem pa payload, iotlb', none) | .error _ => (mem, iotlb', none)
def execIotlbHardwareDmaBurst (arena : SmmuV3RadixArena) (epoch : Nat) (iotlb : List CachedTlbiEntry) (mem : Nat → UInt8) :
    List PeripheralDmaOp → (Nat → UInt8) × List CachedTlbiEntry × List (Option ByteArray)
  | [] => (mem, iotlb, [])
  | op :: ops =>
    let (mem₁, iotlb₁, obs₁) := execIotlbHardwareDmaOp arena epoch iotlb mem op
    let (mem₂, iotlb₂, obsRest) := execIotlbHardwareDmaBurst arena epoch iotlb₁ mem₁ ops
    (mem₂, iotlb₂, obs₁ :: obsRest)
def iotlbEntryAuthorizedB (m : SmmuManifest) (e : CachedTlbiEntry) : Bool :=
  m.defaultDeny && e.streamId != 0 && e.streamId != wildcardStreamId &&
  m.streams.any fun pt => pt.streamId == e.streamId && (e.vmid == UInt16.ofNat pt.streamId.toNat) &&
    pt.regions.any fun reg =>
      decide (reg.iova.toNat ≤ e.iovaBase.toNat ∧ e.iovaBase.toNat + e.granule.byteSize ≤ reg.iova.toNat + reg.size.toNat) &&
      (e.paddrBase.toNat == reg.paddr.toNat + (e.iovaBase.toNat - reg.iova.toNat)) && (e.perm == reg.perm)
def onlyOldRegChangedB (oldM newM : SmmuManifest) (sid : StreamId) (oldReg : Stage2DmaRegion) : Bool :=
  (oldM.streams.any fun pt => pt.streamId == sid && pt.regions.any (· == oldReg)) &&
  (newM.streams.all fun pt' => pt'.streamId == sid || oldM.streams.any (· == pt')) &&
  oldM.streams.all fun pt =>
    if pt.streamId == sid then
      pt.regions.all fun r => r == oldReg || newM.streams.any fun pt' => pt'.streamId == sid && pt'.regions.any (· == r)
    else newM.streams.any (· == pt)
structure SmmuEpochState where
  (epoch : Nat) (cfg : ChokepointSmmuConfig) (arenaBase : UInt64) (maxFrames : Nat)
  (arena : SmmuV3RadixArena) (iotlb : List CachedTlbiEntry) deriving DecidableEq, Repr
inductive TlbiReconfigError where
  | invalidOldStreamVmid | missingTlbiOrSync | unannouncedCrossStreamMutation
  | invalidTargetConfig (c : SmmuRefusalClause) | radixRebuildFailed (e : SmmuRadixBuildError)
  deriving DecidableEq, Repr
def unmapOrReassignDmaRegion (st : SmmuEpochState) (sid : StreamId) (oldVmid : UInt16)
    (oldReg : Stage2DmaRegion) (cfg' : ChokepointSmmuConfig)
    (arenaBase' : UInt64) (maxFrames' : Nat) (cmds : List SmmuCmd) : Except TlbiReconfigError SmmuEpochState :=
  match decodeArenaStreamRoot st.arena sid with
  | none => .error .invalidOldStreamVmid
  | some (actualVmid, _) =>
    if actualVmid != oldVmid then .error .invalidOldStreamVmid
    else if !reconfigQueueValidB st.iotlb cmds sid oldVmid oldReg then .error .missingTlbiOrSync
    else if !onlyOldRegChangedB st.cfg.manifest cfg'.manifest sid oldReg ||
        cfg'.manifest.streams.any (fun pt => pt.streamId == sid && pt.regions.any (· == oldReg)) then
      .error .unannouncedCrossStreamMutation
    else match verifyChokepointSmmuConfig cfg' with
      | .error c => .error (.invalidTargetConfig c)
      | .ok () => match compileManifestToRadixArena cfg'.manifest arenaBase' maxFrames' with
        | .error e => .error (.radixRebuildFailed e)
        | .ok arena' =>
          let qOut := runSmmuCmds ⟨[], [], st.iotlb⟩ cmds
          let targetHasSurvivors := st.cfg.manifest.streams.any fun p => p.streamId == sid && p.regions.any (· != oldReg)
          let targetWalkOk := !targetHasSurvivors || streamSubtreeIdenticalB st.arena arena' sid || syncedCfgiPrecedesVmall qOut.synced sid oldVmid
          let newCoherent := cfg'.manifest.streams.all fun pt =>
            pt.streamId == sid || streamSubtreeIdenticalB st.arena arena' pt.streamId ||
              syncedCfgiPrecedesVmall qOut.synced pt.streamId (UInt16.ofNat pt.streamId.toNat)
          let oldCoherent := st.cfg.manifest.streams.all fun pt =>
            pt.streamId == sid || cfg'.manifest.streams.any (fun p => p.streamId == pt.streamId) ||
              syncedHasCfgiSte qOut.synced pt.streamId
          if !(targetWalkOk && newCoherent && oldCoherent) then .error .missingTlbiOrSync
          else .ok ⟨st.epoch + 1, cfg', arenaBase', maxFrames', arena', qOut.iotlb⟩
private theorem runSmmuCmds_no_sync_preserves_iotlb (cmds : List SmmuCmd)
    (hNoSync : ∀ c ∈ cmds, c ≠ .sync) : ∀ q : SmmuCmdQueueState, (runSmmuCmds q cmds).iotlb = q.iotlb := by
  induction cmds with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro q; simp only [runSmmuCmds, List.foldl_cons]
    have hStep : (stepSmmuCmd q c).iotlb = q.iotlb := by cases c <;> first | rfl | exact absurd rfl (hNoSync _ List.mem_cons_self)
    exact (ih (fun x hx => hNoSync x (List.mem_cons_of_mem _ hx)) (stepSmmuCmd q c)).trans hStep
theorem reconfig_without_tlbi_sync_refused (st : SmmuEpochState) (sid : StreamId)
    (oldVmid : UInt16) (oldReg : Stage2DmaRegion) (cfg' : ChokepointSmmuConfig)
    (arenaBase' : UInt64) (maxFrames' : Nat) (cmds : List SmmuCmd) :
    (reconfigQueueValidB st.iotlb cmds sid oldVmid oldReg = false →
      (unmapOrReassignDmaRegion st sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds).isOk = false) ∧
    ((∀ c ∈ cmds, c ≠ .sync) → (runSmmuCmds ⟨[], [], st.iotlb⟩ cmds).iotlb = st.iotlb) := by
  refine ⟨fun hInvalid => ?_, fun hNoSync => runSmmuCmds_no_sync_preserves_iotlb cmds hNoSync _⟩
  dsimp only [unmapOrReassignDmaRegion]
  cases decodeArenaStreamRoot st.arena sid with
  | none => rfl
  | some root =>
    obtain ⟨actualVmid, _⟩ := root; dsimp only []
    cases (actualVmid != oldVmid) <;> simp [hInvalid, Except.isOk, Except.toBool]
private theorem translateWithIotlb_ok_authorized {cfg : ChokepointSmmuConfig} {arenaBase : UInt64}
    {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hSafe : ChokepointSmmuSafeSpec cfg) (hComp : compileManifestToRadixArena cfg.manifest arenaBase maxFrames = .ok arena)
    {iotlb : List CachedTlbiEntry} (hAuth : ∀ e ∈ iotlb, iotlbEntryAuthorizedB cfg.manifest e = true)
    {epoch : Nat} {sid : StreamId} {iova len : Nat} {acc : DmaAccess} {pa : Nat} {iotlb' : List CachedTlbiEntry}
    (hTr : translateWithIotlb iotlb arena epoch sid iova len acc = (.ok pa, iotlb')) :
    (∀ e ∈ iotlb', iotlbEntryAuthorizedB cfg.manifest e = true) ∧
      0 < len ∧ ∀ off < len, ∃ pt ∈ cfg.manifest.streams, pt.streamId = sid ∧ ∃ reg ∈ pt.regions,
        reg.perm.permits acc = true ∧ reg.paddr.toNat ≤ pa + off ∧ pa + off < reg.paddr.toNat + reg.size.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hEn, _⟩ := compileManifestToRadixArena_unpack hComp
  dsimp only [translateWithIotlb] at hTr; rw [hEn] at hTr
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
  split at hTr; · cases hTr
  split at hTr; · cases hTr
  rename_i hLenB; have hLenPos : 0 < len := Nat.pos_of_ne_zero (by simpa [beq_iff_eq] using hLenB)
  cases hHit : lookupIotlb iotlb sid iova len with
  | some e =>
    rw [hHit] at hTr; dsimp only [] at hTr
    by_cases hPerm : e.perm.permits acc = true
    · simp only [hPerm, ↓reduceIte] at hTr; cases hTr
      obtain ⟨heMem, hePred⟩ := find_some_mem_pred hHit
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hePred
      have heAuth := hAuth e heMem
      simp only [iotlbEntryAuthorizedB, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at heAuth
      obtain ⟨_, pt, hptMem, ⟨hptSid, _⟩, reg, hregMem, ⟨⟨hrLo, hrHi⟩, hPaBase⟩, hPermEq⟩ := heAuth
      rw [hPermEq] at hPerm; obtain ⟨rfl, hlo, hhi⟩ := hePred
      exact ⟨hAuth, hLenPos, fun off hoff => ⟨pt, hptMem, hptSid, reg, hregMem, hPerm, by omega, by omega⟩⟩
    · simp [hPerm] at hTr
  | none =>
    rw [hHit] at hTr; dsimp only [] at hTr
    cases hW : walkSmmuV3Stage2Detail arena sid iova len acc with
    | error _ => rw [hW] at hTr; cases hTr
    | ok det =>
      obtain ⟨paOut, vmid, gran, perm⟩ := det; rw [hW] at hTr; cases hTr
      obtain ⟨hDeny, hs0, hsw, _, hIova48, hPerm, hVmidEq, pt, hptMem, hptSid,
        ⟨reg₀, hreg₀Mem, rfl, hCovLo, hCovHi, hPaEq⟩, hBytes⟩ := walkSmmuV3Stage2Detail_ok hComp hW
      have hrAl := (hSafe.alignedInPool pt hptMem).2 reg₀ hreg₀Mem
      simp only [regionAlignedInPoolB, Bool.and_eq_true, decide_eq_true_eq] at hrAl
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hrP48⟩, _⟩, _⟩, _⟩, _⟩ := hrAl
      have hGPos := PageGranule.byteSize_pos gran
      refine ⟨fun e he => ?_, hLenPos, fun off hoff => ?_⟩
      · rcases List.mem_cons.mp he with rfl | heOld
        · rw [hPaEq, Nat.add_sub_cancel]
          have hrI48 : reg₀.iova.toNat + reg₀.size.toNat ≤ smmuAddrLimit48 := by
            have hrAl' := (hSafe.alignedInPool pt hptMem).2 reg₀ hreg₀Mem
            simp only [regionAlignedInPoolB, Bool.and_eq_true, decide_eq_true_eq] at hrAl'
            exact hrAl'.1.1.1.1.1.2
          have hIovaB : (UInt64.ofNat ((iova / gran.byteSize) * gran.byteSize)).toNat =
              (iova / gran.byteSize) * gran.byteSize :=
            u64_toNat_of_lt (by simp only [smmuAddrLimit48] at hrI48 hCovHi hGPos; omega)
          have hPaB : (UInt64.ofNat (reg₀.paddr.toNat + ((iova / gran.byteSize) * gran.byteSize - reg₀.iova.toNat))).toNat =
              reg₀.paddr.toNat + ((iova / gran.byteSize) * gran.byteSize - reg₀.iova.toNat) :=
            u64_toNat_of_lt (by simp only [smmuAddrLimit48] at hrP48 hCovLo hCovHi hGPos; omega)
          unfold iotlbEntryAuthorizedB
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, List.any_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨hDeny, hs0⟩, hsw⟩, pt, hptMem, ⟨hptSid, hptSid.symm ▸ hVmidEq⟩, reg₀, hreg₀Mem,
            ⟨⟨by rw [hIovaB]; exact hCovLo, by rw [hIovaB]; exact hCovHi⟩, by rw [hPaB, hIovaB]⟩, rfl⟩
        · exact hAuth e heOld
      · obtain ⟨reg, hregMem, hPermEq, _, _, hLoB, hHiB⟩ := hBytes off hoff
        exact ⟨pt, hptMem, hptSid, reg, hregMem, hPermEq ▸ hPerm, hLoB, hHiB⟩
private theorem execIotlbBurst_iotlb_agrees (arena : SmmuV3RadixArena) (ep : Nat) {cF kF : List Nat}
    (ops : List PeripheralDmaOp) (tlb : List CachedTlbiEntry) (m1 m2 : Nat → UInt8)
    (hAg : ∀ pa, pa / pageSize ∉ cF → pa / pageSize ∉ kF → m1 pa = m2 pa) :
    (execIotlbHardwareDmaBurst arena ep tlb m1 ops).2.1 = (execIotlbHardwareDmaBurst arena ep tlb m2 ops).2.1 ∧
    ∀ pa, pa / pageSize ∉ cF → pa / pageSize ∉ kF →
      (execIotlbHardwareDmaBurst arena ep tlb m1 ops).1 pa = (execIotlbHardwareDmaBurst arena ep tlb m2 ops).1 pa := by
  induction ops generalizing tlb m1 m2 with
  | nil => exact ⟨rfl, hAg⟩
  | cons op ops ih =>
    simp only [execIotlbHardwareDmaBurst]; cases op with
    | read s io ln =>
      dsimp only [execIotlbHardwareDmaOp]
      cases translateWithIotlb tlb arena ep s io ln .dmaRead with | mk r tlb₁ => cases r <;> exact ih tlb₁ m1 m2 hAg
    | write s io pay =>
      dsimp only [execIotlbHardwareDmaOp]
      cases translateWithIotlb tlb arena ep s io pay.size .dmaWrite with
      | mk r tlb₁ => cases r with
        | error _ => exact ih tlb₁ m1 m2 hAg
        | ok bPa => exact ih tlb₁ _ _ fun pa hc hk =>
            writePhys_agree (P := fun x => x / pageSize ∉ cF ∧ x / pageSize ∉ kF) (fun x ⟨c, k⟩ => hAg x c k) bPa pay pa ⟨hc, hk⟩
theorem tlbi_synced_reconfig_dma_safe {st : SmmuEpochState} {sid : StreamId} {oldVmid : UInt16}
    {oldReg : Stage2DmaRegion} {cfg' : ChokepointSmmuConfig} {arenaBase' : UInt64} {maxFrames' : Nat} {cmds : List SmmuCmd} {st' : SmmuEpochState}
    (hCompOld : compileManifestToRadixArena st.cfg.manifest st.arenaBase st.maxFrames = .ok st.arena)
    (hPreAuth : ∀ e ∈ st.iotlb, iotlbEntryAuthorizedB st.cfg.manifest e = true)
    (hReconfig : unmapOrReassignDmaRegion st sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds = .ok st')
    (ops : List PeripheralDmaOp) (mem₁ mem₂ : Nat → UInt8)
    (hAgree : ∀ pa, pa / pageSize ∉ cfg'.partition.commitPrivateFrames → pa / pageSize ∉ cfg'.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa) :
    st'.epoch = st.epoch + 1 ∧ st'.cfg = cfg' ∧ verifyChokepointSmmuConfig st'.cfg = .ok () ∧
    compileManifestToRadixArena st'.cfg.manifest st'.arenaBase st'.maxFrames = .ok st'.arena ∧
    (∀ e ∈ st'.iotlb, iotlbEntryAuthorizedB st'.cfg.manifest e = true) ∧
    (∀ e ∈ (execIotlbHardwareDmaBurst st'.arena st'.epoch st'.iotlb mem₁ ops).2.1, iotlbEntryAuthorizedB st'.cfg.manifest e = true) ∧
    (∀ pa, (pa / pageSize ∈ st'.cfg.partition.commitPrivateFrames ∨ pa / pageSize ∈ st'.cfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ st'.cfg.partition.egressOutboxFrames ∨ SmmuTablePhysAddr st'.arena pa) →
      (execIotlbHardwareDmaBurst st'.arena st'.epoch st'.iotlb mem₁ ops).1 pa = mem₁ pa) ∧
    (execIotlbHardwareDmaBurst st'.arena st'.epoch st'.iotlb mem₁ ops).2.2 =
      (execIotlbHardwareDmaBurst st'.arena st'.epoch st'.iotlb mem₂ ops).2.2 := by
  dsimp only [unmapOrReassignDmaRegion] at hReconfig
  cases hRoot : decodeArenaStreamRoot st.arena sid with
  | none => rw [hRoot] at hReconfig; cases hReconfig
  | some root =>
    rw [hRoot] at hReconfig; dsimp only [] at hReconfig; split at hReconfig; · cases hReconfig
    rename_i hNotVmid; have hVmidMatch : root.1 = oldVmid := by simpa [bne_iff_ne] using hNotVmid
    split at hReconfig; · cases hReconfig
    rename_i hNotQ; have hValidQ : reconfigQueueValidB st.iotlb cmds sid oldVmid oldReg = true := by simpa using hNotQ
    split at hReconfig; · cases hReconfig
    rename_i hNotOnly
    have hOnly : onlyOldRegChangedB st.cfg.manifest cfg'.manifest sid oldReg = true := by
      cases hO : onlyOldRegChangedB st.cfg.manifest cfg'.manifest sid oldReg; · simp [hO] at hNotOnly
      · rfl
    cases hv : verifyChokepointSmmuConfig cfg' with
    | error _ => simp [hv] at hReconfig
    | ok _ =>
      simp only [hv] at hReconfig
      cases hc : compileManifestToRadixArena cfg'.manifest arenaBase' maxFrames' with
      | error _ => simp [hc] at hReconfig
      | ok arena' =>
        simp only [hc] at hReconfig; split at hReconfig; · cases hReconfig
        cases hReconfig; have hSafe := verifyChokepointSmmuConfig_sound hv
        have hOldVmid : oldVmid = UInt16.ofNat sid.toNat := by
          have hRO := compiledArena_root_and_walk hCompOld sid
          cases hLS : lookupStream st.cfg.manifest.streams sid with
          | none => rw [hLS, hRoot] at hRO; cases hRO
          | some _ => rw [hLS, hRoot] at hRO; obtain ⟨_, hEq, _⟩ := hRO; injection hEq with hPair
                      exact hVmidMatch.symm.trans (congrArg Prod.fst hPair)
        obtain ⟨_, _, hEvTlbi⟩ := reconfigQueueValidB_evicts_unmapped_region hValidQ
        have hOnlyAll := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hOnly).2
        have hAuth₀ : ∀ e ∈ (runSmmuCmds ⟨[], [], st.iotlb⟩ cmds).iotlb, iotlbEntryAuthorizedB cfg'.manifest e = true := by
          intro e he; obtain ⟨heOld, hDisjOld⟩ := hEvTlbi e he; have heAuthOld := hPreAuth e heOld
          simp only [iotlbEntryAuthorizedB, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at heAuthOld ⊢
          obtain ⟨⟨⟨_, hs0⟩, hsw⟩, pt, hptOld, ⟨hptSid, heVmid⟩, reg, hregOld, hRegPred⟩ := heAuthOld
          have hKeep := hOnlyAll pt hptOld
          by_cases hEqSid : pt.streamId == sid
          · simp only [hEqSid, ↓reduceIte, List.all_eq_true] at hKeep
            have hSidEq : pt.streamId = sid := beq_iff_eq.mp hEqSid
            rcases (Bool.or_eq_true _ _).mp (hKeep reg hregOld) with hIsOld | hInNew
            · exfalso; rw [beq_iff_eq.mp hIsOld] at hRegPred
              have hDisj := hDisjOld (heVmid.trans (hSidEq ▸ hOldVmid.symm))
              have hCov := decide_eq_true_eq.mp hRegPred.1.1; have hGPos := PageGranule.byteSize_pos e.granule
              simp only [rangesDisjointB, decide_eq_true_eq] at hDisj; omega
            · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hInNew
              obtain ⟨pt', hpt', hpt'Sid, r', hr'Mem, hr'Eq⟩ := hInNew; subst hr'Eq
              have hSameSid : pt'.streamId = pt.streamId := hpt'Sid.trans hSidEq.symm
              exact ⟨⟨⟨hSafe.defaultDeny, hs0⟩, hsw⟩, pt', hpt', ⟨hSameSid.trans hptSid, hSameSid ▸ heVmid⟩, r', hr'Mem, hRegPred⟩
          · simp only [hEqSid, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, beq_iff_eq] at hKeep
            obtain ⟨pt', hpt', hPtEq⟩ := hKeep; subst hPtEq
            exact ⟨⟨⟨hSafe.defaultDeny, hs0⟩, hsw⟩, pt', hpt', ⟨hptSid, heVmid⟩, reg, hregOld, hRegPred⟩
        obtain ⟨_, _, _, _, _, _, _, _, hProtB, _, _, hAbEq, hCap, _⟩ := compileManifestToRadixArena_unpack hc
        obtain ⟨prKt, hprKtMem, hprKtOk⟩ := List.any_eq_true.mp hProtB
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hprKtOk
        have hErrSame : ∀ {tlb : List CachedTlbiEntry} {ep : Nat} {s : StreamId} {io ln : Nat}
            {ac : DmaAccess} {err : SmmuDmaFault} {tlb₁ : List CachedTlbiEntry},
            translateWithIotlb tlb arena' ep s io ln ac = (.error err, tlb₁) → tlb₁ = tlb := by
          intro tlb ep s io ln ac err tlb₁ hE; dsimp only [translateWithIotlb] at hE
          split at hE; · injection hE with _ hEq; exact hEq.symm
          split at hE; · injection hE with _ hEq; exact hEq.symm
          split at hE; · injection hE with _ hEq; exact hEq.symm
          cases hHitE : lookupIotlb tlb s io ln with
          | some eHit => rw [hHitE] at hE; dsimp only [] at hE; cases hPE : eHit.perm.permits ac <;> rw [hPE] at hE
                         · injection hE with _ hEq; exact hEq.symm
                         · simp at hE
          | none => rw [hHitE] at hE; dsimp only [] at hE
                    cases hWE : walkSmmuV3Stage2Detail arena' s io ln ac with
                    | error _ => rw [hWE] at hE; injection hE with _ hEq; exact hEq.symm
                    | ok det => obtain ⟨_, _, _, _⟩ := det; rw [hWE] at hE; cases hE
        have hLoop : ∀ (xs : List PeripheralDmaOp) (tlb : List CachedTlbiEntry) (m1 m2 : Nat → UInt8),
            (∀ e ∈ tlb, iotlbEntryAuthorizedB cfg'.manifest e = true) →
            (∀ pa, pa / pageSize ∉ cfg'.partition.commitPrivateFrames → pa / pageSize ∉ cfg'.partition.kernelAndCodeFrames → m1 pa = m2 pa) →
            (∀ e ∈ (execIotlbHardwareDmaBurst arena' (st.epoch + 1) tlb m1 xs).2.1, iotlbEntryAuthorizedB cfg'.manifest e = true) ∧
            (∀ pa, (pa / pageSize ∈ cfg'.partition.commitPrivateFrames ∨ pa / pageSize ∈ cfg'.partition.kernelAndCodeFrames ∨
                pa / pageSize ∈ cfg'.partition.egressOutboxFrames ∨ SmmuTablePhysAddr arena' pa) →
              (execIotlbHardwareDmaBurst arena' (st.epoch + 1) tlb m1 xs).1 pa = m1 pa) ∧
            (execIotlbHardwareDmaBurst arena' (st.epoch + 1) tlb m1 xs).2.2 =
              (execIotlbHardwareDmaBurst arena' (st.epoch + 1) tlb m2 xs).2.2 := by
          intro xs; induction xs with
          | nil => intro tlb _ _ hTlb _; exact ⟨hTlb, fun _ _ => rfl, rfl⟩
          | cons op xs ih =>
            intro tlb m1 m2 hTlb hAg; simp only [execIotlbHardwareDmaBurst]
            cases op with
            | read rSid rIova rLen =>
              dsimp only [execIotlbHardwareDmaOp]
              cases hTr : translateWithIotlb tlb arena' (st.epoch + 1) rSid rIova rLen .dmaRead with
              | mk res tlb₁ =>
                cases res with
                | error _ => dsimp only []; rw [hErrSame hTr]; obtain ⟨hT, hP, hO⟩ := ih tlb m1 m2 hTlb hAg; exact ⟨hT, hP, by rw [hO]⟩
                | ok basePa =>
                  obtain ⟨hTlb₁, _, hBytes⟩ := translateWithIotlb_ok_authorized hSafe hc hTlb hTr
                  have hEq := authorized_dma_read_congr_bytes hSafe basePa rLen
                    (fun i hi => by obtain ⟨pt, hpt, -, reg, hreg, -, hlo, hhi⟩ := hBytes i hi; exact ⟨pt, hpt, reg, hreg, hlo, hhi⟩) hAg
                  obtain ⟨hT, hP, hO⟩ := ih tlb₁ m1 m2 hTlb₁ hAg; dsimp only []; exact ⟨hT, hP, by rw [hEq, hO]⟩
            | write wSid wIova payload =>
              dsimp only [execIotlbHardwareDmaOp]
              cases hTr : translateWithIotlb tlb arena' (st.epoch + 1) wSid wIova payload.size .dmaWrite with
              | mk res tlb₁ =>
                cases res with
                | error _ => rw [hErrSame hTr]; obtain ⟨hT, hP, hO⟩ := ih tlb m1 m2 hTlb hAg; exact ⟨hT, hP, by rw [hO]⟩
                | ok basePa =>
                  obtain ⟨hTlb₁, _, hBytes⟩ := translateWithIotlb_ok_authorized hSafe hc hTlb hTr
                  have hStepPres : ∀ pa, (pa / pageSize ∈ cfg'.partition.commitPrivateFrames ∨
                      pa / pageSize ∈ cfg'.partition.kernelAndCodeFrames ∨
                      pa / pageSize ∈ cfg'.partition.egressOutboxFrames ∨ SmmuTablePhysAddr arena' pa) →
                      writePhys m1 basePa payload pa = m1 pa := by
                    intro pa hProt
                    have hByteW : ∀ i < payload.size, ∃ pt ∈ cfg'.manifest.streams, ∃ reg ∈ pt.regions,
                        reg.perm.permits .dmaWrite = true ∧ reg.paddr.toNat ≤ basePa + i ∧ basePa + i < reg.paddr.toNat + reg.size.toNat :=
                      fun i hi => by obtain ⟨pt, hpt, -, reg, hreg, hp, hlo, hhi⟩ := hBytes i hi; exact ⟨pt, hpt, reg, hreg, hp, hlo, hhi⟩
                    rcases hProt with hCom | hKern | hOut | hTbl
                    · exact authorized_dma_write_preserves_bytes hSafe basePa payload hByteW m1 (.inl hCom)
                    · exact authorized_dma_write_preserves_bytes hSafe basePa payload hByteW m1 (.inr (.inl hKern))
                    · exact authorized_dma_write_preserves_bytes hSafe basePa payload hByteW m1 (.inr (.inr hOut))
                    · have hInAr := smmuTablePhysAddr_in_arena hCap hTbl; rw [hAbEq] at hInAr
                      exact authorized_dma_write_disjoint_range hSafe hprKtMem (by rw [hprKtOk.1]; decide) basePa payload
                        (fun i hi => by obtain ⟨pt, hpt, reg, hreg, _, hlo, hhi⟩ := hByteW i hi; exact ⟨pt, hpt, reg, hreg, hlo, hhi⟩)
                        m1 ⟨by omega, by omega⟩
                  have hAg₁ : ∀ pa, pa / pageSize ∉ cfg'.partition.commitPrivateFrames →
                      pa / pageSize ∉ cfg'.partition.kernelAndCodeFrames →
                      writePhys m1 basePa payload pa = writePhys m2 basePa payload pa := fun pa hc0 hk0 =>
                    writePhys_agree (P := fun x => x / pageSize ∉ cfg'.partition.commitPrivateFrames ∧
                      x / pageSize ∉ cfg'.partition.kernelAndCodeFrames) (fun x ⟨c, k⟩ => hAg x c k) basePa payload pa ⟨hc0, hk0⟩
                  obtain ⟨hTRest, hPRest, hORest⟩ := ih tlb₁ _ _ hTlb₁ hAg₁
                  exact ⟨hTRest, fun pa hProt => (hPRest pa hProt).trans (hStepPres pa hProt), by rw [hORest]⟩
        obtain ⟨hTlbFin, hPresAll, hObsAll⟩ := hLoop ops _ mem₁ mem₂ hAuth₀ hAgree
        exact ⟨rfl, rfl, hv, hc, hAuth₀, hTlbFin, hPresAll, hObsAll⟩
inductive SmmuEpochTurn where
  | reconfig (sid : StreamId) (oldVmid : UInt16) (oldReg : Stage2DmaRegion)
      (cfg' : ChokepointSmmuConfig) (arenaBase' : UInt64) (maxFrames' : Nat)
      (cmds : List SmmuCmd) (postBurst : List PeripheralDmaOp)
def runSmmuEpochTrace : SmmuEpochState → (Nat → UInt8) → List SmmuEpochTurn →
    Option (SmmuEpochState × (Nat → UInt8) × List (List (Option ByteArray)))
  | s, mem, [] => some (s, mem, [])
  | s, mem, .reconfig sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds postBurst :: ts =>
    match unmapOrReassignDmaRegion s sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds with
    | .error _ => none
    | .ok mid =>
      if cfg'.partition.commitPrivateFrames == s.cfg.partition.commitPrivateFrames &&
          cfg'.partition.kernelAndCodeFrames == s.cfg.partition.kernelAndCodeFrames &&
          cfg'.partition.egressOutboxFrames == s.cfg.partition.egressOutboxFrames then
        let b := execIotlbHardwareDmaBurst mid.arena mid.epoch mid.iotlb mem postBurst
        match runSmmuEpochTrace { mid with iotlb := b.2.1 } b.1 ts with
        | none => none | some (f, memF, obsRest) => some (f, memF, b.2.2 :: obsRest)
      else none
/-- **Multi-Epoch Inductive IOTLB, Persistent-Memory & Observational Non-Interference Safety**: across
arbitrary $N$-epoch traces threading persistent physical memory `mem₁`/`mem₂` and hardware IOTLB state,
private/kernel/outbox frames stay unmodified and DMA read observations leak zero private/kernel bytes. -/
theorem validSmmuEpochTrace_dma_safe {s f : SmmuEpochState} {turns : List SmmuEpochTurn}
    {mem₁ mem₁' mem₂ : Nat → UInt8} {obs₁ : List (List (Option ByteArray))}
    (hValid₀ : verifyChokepointSmmuConfig s.cfg = .ok ())
    (hComp₀ : compileManifestToRadixArena s.cfg.manifest s.arenaBase s.maxFrames = .ok s.arena)
    (hAuth₀ : ∀ e ∈ s.iotlb, iotlbEntryAuthorizedB s.cfg.manifest e = true)
    (hAgree : ∀ pa, pa / pageSize ∉ s.cfg.partition.commitPrivateFrames →
      pa / pageSize ∉ s.cfg.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa)
    (hRun : runSmmuEpochTrace s mem₁ turns = some (f, mem₁', obs₁)) :
    (∃ mem₂', runSmmuEpochTrace s mem₂ turns = some (f, mem₂', obs₁)) ∧
    f.epoch = s.epoch + turns.length ∧
    verifyChokepointSmmuConfig f.cfg = .ok () ∧
    compileManifestToRadixArena f.cfg.manifest f.arenaBase f.maxFrames = .ok f.arena ∧
    (∀ e ∈ f.iotlb, iotlbEntryAuthorizedB f.cfg.manifest e = true) ∧
    (∀ pa, (pa / pageSize ∈ s.cfg.partition.commitPrivateFrames ∨
        pa / pageSize ∈ s.cfg.partition.kernelAndCodeFrames ∨
        pa / pageSize ∈ s.cfg.partition.egressOutboxFrames) → mem₁' pa = mem₁ pa) := by
  induction turns generalizing s mem₁ mem₂ obs₁ with
  | nil =>
    simp only [runSmmuEpochTrace, Option.some.injEq, Prod.mk.injEq] at hRun
    obtain ⟨rfl, rfl, rfl⟩ := hRun
    exact ⟨⟨mem₂, rfl⟩, by simp, hValid₀, hComp₀, hAuth₀, fun _ _ => rfl⟩
  | cons t ts ih =>
    cases t with
    | reconfig sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds postBurst =>
      dsimp only [runSmmuEpochTrace] at hRun ⊢
      cases hRec : unmapOrReassignDmaRegion s sid oldVmid oldReg cfg' arenaBase' maxFrames' cmds with
      | error _ => rw [hRec] at hRun; cases hRun
      | ok mid =>
        rw [hRec] at hRun; dsimp only [] at hRun
        cases hPart : (cfg'.partition.commitPrivateFrames == s.cfg.partition.commitPrivateFrames &&
            cfg'.partition.kernelAndCodeFrames == s.cfg.partition.kernelAndCodeFrames &&
            cfg'.partition.egressOutboxFrames == s.cfg.partition.egressOutboxFrames) with
        | false => rw [hPart] at hRun; simp at hRun
        | true =>
          rw [hPart] at hRun; simp only [↓reduceIte] at hRun ⊢
          have hPartP := hPart; simp only [Bool.and_eq_true, beq_iff_eq] at hPartP
          obtain ⟨⟨hComEq, hKernEq⟩, hOutEq⟩ := hPartP
          have hAgree' : ∀ pa, pa / pageSize ∉ cfg'.partition.commitPrivateFrames →
              pa / pageSize ∉ cfg'.partition.kernelAndCodeFrames → mem₁ pa = mem₂ pa := by
            rw [hComEq, hKernEq]; exact hAgree
          obtain ⟨hEp, hMidCfg, hVal₁, hComp₁, _, hTlbBurst, hPres₁, hObsEq⟩ :=
            tlbi_synced_reconfig_dma_safe hComp₀ hAuth₀ hRec postBurst mem₁ mem₂ hAgree'
          obtain ⟨hTlbEq, hAgNext⟩ := execIotlbBurst_iotlb_agrees mid.arena mid.epoch
            (cF := mid.cfg.partition.commitPrivateFrames) (kF := mid.cfg.partition.kernelAndCodeFrames)
            postBurst mid.iotlb mem₁ mem₂ (by rw [hMidCfg]; exact hAgree')
          let b₁ := execIotlbHardwareDmaBurst mid.arena mid.epoch mid.iotlb mem₁ postBurst
          let nextSt : SmmuEpochState := { mid with iotlb := b₁.2.1 }
          cases hSub : runSmmuEpochTrace nextSt b₁.1 ts with
          | none => rw [hSub] at hRun; cases hRun
          | some subOut =>
            obtain ⟨fOut, memF, obsRest⟩ := subOut
            rw [hSub] at hRun; simp only [Option.some.injEq, Prod.mk.injEq] at hRun
            obtain ⟨rfl, rfl, rfl⟩ := hRun
            obtain ⟨⟨mem₂', hRun₂⟩, hEpRest, hValF, hCompF, hAuthF, hPresRest⟩ :=
              ih (s := nextSt) hVal₁ hComp₁ hTlbBurst hAgNext hSub
            dsimp only [nextSt] at hEpRest
            have hRun₂Full : (let b₂ := execIotlbHardwareDmaBurst mid.arena mid.epoch mid.iotlb mem₂ postBurst
                match runSmmuEpochTrace { mid with iotlb := b₂.2.1 } b₂.1 ts with
                | none => none | some (f0, m0, o0) => some (f0, m0, b₂.2.2 :: o0)) = some (fOut, mem₂', b₁.2.2 :: obsRest) := by
              dsimp only []; rw [← hTlbEq, ← hObsEq]
              exact (by rw [hRun₂] :
                (match runSmmuEpochTrace nextSt (execIotlbHardwareDmaBurst mid.arena mid.epoch mid.iotlb mem₂ postBurst).1 ts with
                 | none => none | some (f0, m0, o0) => some (f0, m0, b₁.2.2 :: o0)) = some (fOut, mem₂', b₁.2.2 :: obsRest))
            refine ⟨⟨mem₂', hRun₂Full⟩, by simp only [List.length_cons] at *; omega, hValF, hCompF, hAuthF, fun pa hP => ?_⟩
            have hP' : pa / pageSize ∈ mid.cfg.partition.commitPrivateFrames ∨
                pa / pageSize ∈ mid.cfg.partition.kernelAndCodeFrames ∨
                pa / pageSize ∈ mid.cfg.partition.egressOutboxFrames := by rw [hMidCfg, hComEq, hKernEq, hOutEq]; exact hP
            exact (hPresRest pa hP').trans (hPres₁ pa (hP'.elim .inl (fun h => h.elim (.inr ∘ .inl) (.inr ∘ .inr ∘ .inl))))

/-! ## 7. Canonical Fixtures & Constructive Inhabitedness Witnesses -/
def canonicalSmmuManifest : SmmuManifest :=
  { arch := .armSmmuV3, defaultDeny := true, rootserverPhysStart := 0x60246000, rootserverPhysEnd := 0x60846000
    dmaPoolBase := 0x60846000, dmaPoolSize := 0x00100000
    protectedRanges := [⟨.commitPrivate, 0x60300000, 0x1000⟩, ⟨.pdCodeStackCspace, 0x60246000, 0x000ba000⟩]
    streams := [ ⟨0x10, .ingressNic, .ingress, [⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩]⟩
      , ⟨0x20, .persistNvme, .persist, [⟨0x80010000, 0x60847000, 0x2000, .page4KiB, .readWrite, .persistWalPool⟩]⟩
      , ⟨0x30, .egressNic, .txEgress, [⟨0x80020000, 0x60849000, 0x1000, .page4KiB, .readOnly, .egressOutboxRing⟩]⟩ ] }
def canonicalSmmuConfig : ChokepointSmmuConfig :=
  ⟨canonicalSmmuManifest, ⟨(0x60246000, 0x60846000), [0x60846], [0x60300], [0x60246, 0x60247], [0x60847, 0x60848], [0x60849]⟩⟩
def canonicalSmmuQuery : SmmuManifestQuery := ⟨canonicalSmmuConfig, none⟩
def canonicalSmmuCert : SmmuManifestCert := ⟨smmuManifestDigest canonicalSmmuManifest⟩
def canonicalRadixSmmuConfig : ChokepointSmmuConfig :=
  { canonicalSmmuConfig with manifest := { canonicalSmmuManifest with protectedRanges := ⟨.kernelPageTable, 0x60310000, 0x20000⟩ :: canonicalSmmuManifest.protectedRanges } }
def reassignedRadixSmmuConfig : ChokepointSmmuConfig :=
  { manifest := { canonicalRadixSmmuConfig.manifest with streams := [ ⟨0x10, .ingressNic, .ingress, [⟨0x80000000, 0x6084a000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩]⟩
      , ⟨0x20, .persistNvme, .persist, [⟨0x80010000, 0x60847000, 0x2000, .page4KiB, .readWrite, .persistWalPool⟩]⟩
      , ⟨0x30, .egressNic, .txEgress, [⟨0x80020000, 0x60849000, 0x1000, .page4KiB, .readOnly, .egressOutboxRing⟩]⟩ ] }
    partition := { canonicalSmmuConfig.partition with ingressRingFrames := [0x6084a] } }
private theorem threeStreamSingle4K_compiles {m : SmmuManifest} (hArch : (m.arch != .armSmmuV3) = false)
    (hD : (!m.defaultDeny) = false) (hNw : (!streamsNoWildcardB m || !streamsAlignedInPoolB m || !streamsNonCoalescableB m) = false)
    (hPr : (!arenaProtectedByKernelPtB m 0x60310000 32) = false) (hMs : maxManifestSid m.streams = 0x30) (hLen : m.streams.length = 3)
    (hSingle : ∀ pt ∈ m.streams, ∃ r, pt.regions = [r] ∧ r.granule = .page4KiB ∧ 0 < r.size.toNat ∧
      r.iova.toNat + r.size.toNat ≤ smmuAddrLimit48 ∧ r.iova.toNat / hugeBlock2MiB = (r.iova.toNat + r.size.toNat - 1) / hugeBlock2MiB) :
    (compileManifestToRadixArena m 0x60310000 32).isOk = true := by
  have hBound := compileStreamRoots_single4K_tables_le 0x60310000 2 m.streams #[] hSingle
  unfold compileManifestToRadixArena; rw [hArch, hD, hNw, hMs]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hLt4k : decide (0x30 ≥ 4096) = false := rfl; have hCnt : nextSteCountPow2 (0x30 + 1) = 64 := rfl
  rw [hLt4k]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hCnt]
  have hAb : (((0x60310000 : UInt64).toNat % (64 * 64) != 0) || ((0x60310000 : UInt64).toNat % pageSize != 0) || (32 == 0) ||
      decide ((0x60310000 : UInt64).toNat + 32 * pageSize > smmuAddrLimit48)) = false := by decide
  have hStF : (64 * 64) / pageSize + 1 = 2 := rfl; have hAbNat : (0x60310000 : UInt64).toNat = 0x60310000 := rfl
  rw [hAb, hPr]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hStF, hAbNat]
  have hSzOk : decide (2 + (compileStreamRoots 0x60310000 2 m.streams #[]).2.size > 32) = false :=
    decide_eq_false_iff_not.mpr (by simp only [Array.size_empty, hLen] at hBound; omega)
  rw [hSzOk]; rfl
theorem smmuChokepointCheck_inhabited (grade : Nat) (hGrade : 5 ≤ grade) :
    verifyChokepointSmmuConfig canonicalSmmuConfig = .ok () ∧
      smmuChokepointCheck grade canonicalSmmuQuery canonicalSmmuCert = .ok ∧
      ∃ arena st',
        compileManifestToRadixArena canonicalRadixSmmuConfig.manifest 0x60310000 32 = .ok arena ∧
        walkSmmuV3Stage2 arena 0x20 0x80010400 0x1800 .dmaWrite = .ok 0x60847400 ∧
        unmapOrReassignDmaRegion
          ⟨0, canonicalRadixSmmuConfig, 0x60310000, 32, arena, [⟨0x10, 0x10, 0x80000000, 0x60846000, .page4KiB, .writeOnly, 0⟩]⟩
          0x10 0x10 ⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩
          reassignedRadixSmmuConfig 0x60310000 32
          [.cfgiSte 0x10 false, .cfgiSte 0x20 false, .cfgiSte 0x30 false, .sync,
           .tlbiS12Vmall 0x20, .tlbiS12Vmall 0x30, .tlbiS2Ipa 0x10 0x80000000 false, .sync] = .ok st' ∧
        st'.iotlb = [] := by
  have hCfg : verifyChokepointSmmuConfig canonicalSmmuConfig = .ok () := rfl
  have hVR : verifyChokepointSmmuConfig canonicalRadixSmmuConfig = .ok () := rfl
  have hVR' : verifyChokepointSmmuConfig reassignedRadixSmmuConfig = .ok () := rfl
  have hBase5 : smmuChokepointCheck 5 canonicalSmmuQuery canonicalSmmuCert = .ok := by
    unfold smmuChokepointCheck
    have hReq : smmuRequiredGrade canonicalSmmuQuery = 5 := rfl; have hFitQ : manifestFitB canonicalSmmuQuery.config.manifest = true := by decide
    have hCfgQ : verifyChokepointSmmuConfig canonicalSmmuQuery.config = .ok () := hCfg; rw [hReq, hFitQ, hCfgQ]
    simp only [Nat.lt_irrefl, decide_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    have hDigQ : (canonicalSmmuCert.manifestDigest != smmuManifestDigest canonicalSmmuQuery.config.manifest) = false :=
      bne_self_eq_false (smmuManifestDigest canonicalSmmuManifest)
    have hExpQ : canonicalSmmuQuery.expectedDigest? = none := rfl; rw [hDigQ, hExpQ]; rfl
  have hJ : smmuChokepointCheck grade canonicalSmmuQuery canonicalSmmuCert = .ok :=
    (smmuChokepointCheck_mono hGrade (by rw [hBase5]; intro h; cases h)).trans hBase5
  have hComp0Ok : (compileManifestToRadixArena canonicalRadixSmmuConfig.manifest 0x60310000 32).isOk = true :=
    threeStreamSingle4K_compiles rfl rfl (by decide) (by decide) rfl rfl (by
      intro pt hpt; simp only [canonicalRadixSmmuConfig, canonicalSmmuManifest, List.mem_cons, List.not_mem_nil, or_false] at hpt
      rcases hpt with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩)
  have hComp1Ok : (compileManifestToRadixArena reassignedRadixSmmuConfig.manifest 0x60310000 32).isOk = true :=
    threeStreamSingle4K_compiles rfl rfl (by decide) (by decide) rfl rfl (by
      intro pt hpt; simp only [reassignedRadixSmmuConfig, List.mem_cons, List.not_mem_nil, or_false] at hpt
      rcases hpt with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩)
  cases hComp : compileManifestToRadixArena canonicalRadixSmmuConfig.manifest 0x60310000 32 with
  | error _ => rw [hComp] at hComp0Ok; cases hComp0Ok
  | ok arena =>
    cases hComp' : compileManifestToRadixArena reassignedRadixSmmuConfig.manifest 0x60310000 32 with
    | error _ => rw [hComp'] at hComp1Ok; cases hComp1Ok
    | ok arena' =>
      have hWalk : walkSmmuV3Stage2 arena 0x20 0x80010400 0x1800 .dmaWrite = .ok 0x60847400 := by
        rw [walkSmmuV3Stage2_refines_spec hVR hComp 0x20 0x80010400 0x1800 .dmaWrite]; rfl
      let initTlb : List CachedTlbiEntry := [⟨0x10, 0x10, 0x80000000, 0x60846000, .page4KiB, .writeOnly, 0⟩]
      let oldReg : Stage2DmaRegion := ⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩
      let cmds : List SmmuCmd := [.cfgiSte 0x10 false, .cfgiSte 0x20 false, .cfgiSte 0x30 false, .sync,
        .tlbiS12Vmall 0x20, .tlbiS12Vmall 0x30, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
      have hRoot := compiledArena_root_and_walk hComp 0x10; have hLook : lookupStream canonicalRadixSmmuConfig.manifest.streams 0x10 = some ⟨0x10, .ingressNic, .ingress, [oldReg]⟩ := rfl
      rw [hLook] at hRoot; obtain ⟨l0Pa, hDecRoot, _⟩ := hRoot
      have hQ : reconfigQueueValidB initTlb cmds 0x10 0x10 oldReg = true := by decide
      have hOnlyG : (!onlyOldRegChangedB canonicalRadixSmmuConfig.manifest reassignedRadixSmmuConfig.manifest 0x10 oldReg ||
          reassignedRadixSmmuConfig.manifest.streams.any (fun pt => pt.streamId == 0x10 && pt.regions.any (· == oldReg))) = false := by decide
      let snc := (runSmmuCmds ⟨[], [], initTlb⟩ cmds).synced
      have hNoSurv : (canonicalRadixSmmuConfig.manifest.streams.any fun p => p.streamId == 0x10 && p.regions.any (· != oldReg)) = false := by decide
      have hTgtW : (!(canonicalRadixSmmuConfig.manifest.streams.any fun p => p.streamId == 0x10 && p.regions.any (· != oldReg)) ||
          streamSubtreeIdenticalB arena arena' 0x10 || syncedCfgiPrecedesVmall snc 0x10 0x10) = true := by rw [hNoSurv]; rfl
      have h20 : syncedCfgiPrecedesVmall snc 0x20 (UInt16.ofNat (0x20 : StreamId).toNat) = true := by decide
      have h30 : syncedCfgiPrecedesVmall snc 0x30 (UInt16.ofNat (0x30 : StreamId).toNat) = true := by decide
      have hNewCoh : (reassignedRadixSmmuConfig.manifest.streams.all fun pt =>
          pt.streamId == 0x10 || streamSubtreeIdenticalB arena arena' pt.streamId ||
            syncedCfgiPrecedesVmall snc pt.streamId (UInt16.ofNat pt.streamId.toNat)) = true := by
        simp only [reassignedRadixSmmuConfig, List.all_cons, List.all_nil, beq_self_eq_true, h20, h30, Bool.true_or, Bool.or_true, Bool.and_self]
      have hOldCoh : (canonicalRadixSmmuConfig.manifest.streams.all fun pt =>
          pt.streamId == 0x10 || reassignedRadixSmmuConfig.manifest.streams.any (fun p => p.streamId == pt.streamId) ||
            syncedHasCfgiSte snc pt.streamId) = true := by decide
      have hVmEq : (UInt16.ofNat (0x10 : StreamId).toNat != (0x10 : UInt16)) = false := rfl
      let st1 : SmmuEpochState := ⟨1, reassignedRadixSmmuConfig, 0x60310000, 32, arena', (runSmmuCmds ⟨[], [], initTlb⟩ cmds).iotlb⟩
      have hRec : unmapOrReassignDmaRegion ⟨0, canonicalRadixSmmuConfig, 0x60310000, 32, arena, initTlb⟩
          0x10 0x10 oldReg reassignedRadixSmmuConfig 0x60310000 32 cmds = .ok st1 := by
        dsimp only [unmapOrReassignDmaRegion]; rw [hDecRoot]; dsimp only []; rw [hVmEq, hQ, hOnlyG, hVR', hComp']; dsimp only []; rw [hTgtW, hNewCoh, hOldCoh]; rfl
      have hEmpty : (runSmmuCmds ⟨[], [], initTlb⟩ cmds).iotlb = [] := by decide
      exact ⟨hCfg, hJ, arena, st1, rfl, hWalk, hRec, hEmpty⟩
end Obend.OS.SmmuDmaConfinement
end
