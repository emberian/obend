module
/-
# Obend.OS.SmmuRadixTables — Armv8 SMMUv3 / RISC-V IOMMU Descriptors and 4-Level (`9+9+9+9+12`)
  Armv8 VMSAv8-64 Stage-2 Multi-Page Radix Page-Table Arena & Hardware Walker
-/
public import Obend.OS.Sel4MicrokitKernel
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.OS.Sel4MicrokitKernel
public section
namespace Obend.OS.SmmuDmaConfinement
open Obend.OS.Sel4MicrokitKernel
set_option autoImplicit false

/-! ## 1. Hardware Bus-Masters, Stage-2 Page Tables, & 4-PD Chokepoint Classification -/
abbrev StreamId := UInt32
def wildcardStreamId : StreamId := 0xFFFFFFFF
def maxRootServerSpanBytes : Nat := 10 * 1024 * 1024
def stockMicrokitLoaderBase : Nat := 0x70000000
def smmuAddrLimit48 : Nat := 281474976710656
def l0WinSize : Nat := 549755813888
def l1WinSize : Nat := 1073741824
def hugeBlock2MiB : Nat := 2097152
def sv48x4RootAlign : Nat := 16384
inductive SmmuArch where | armSmmuV3 | riscvIommu deriving DecidableEq, Repr
def SmmuArch.tagByte : SmmuArch → UInt8 | .armSmmuV3 => 1 | .riscvIommu => 2
theorem SmmuArch.tagByte_injective {a b : SmmuArch} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive DeviceRole where
  | ingressNic | persistNvme | egressNic | displayScanout | cameraCsi2 | gpu deriving DecidableEq, Repr
def DeviceRole.tagByte : DeviceRole → UInt8
  | .ingressNic => 1 | .persistNvme => 2 | .egressNic => 3 | .displayScanout => 4 | .cameraCsi2 => 5 | .gpu => 6
theorem DeviceRole.tagByte_injective {a b : DeviceRole} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive ChokepointPdRole where | ingress | commit | persist | txEgress deriving DecidableEq, Repr
def ChokepointPdRole.tagByte : ChokepointPdRole → UInt8 | .ingress => 0 | .commit => 1 | .persist => 2 | .txEgress => 3
def ChokepointPdRole.toPdId : ChokepointPdRole → PdId | .ingress => 0 | .commit => 1 | .persist => 2 | .txEgress => 3
theorem ChokepointPdRole.tagByte_injective {a b : ChokepointPdRole} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
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
def IoPerm.permits (p : IoPerm) : DmaAccess → Bool | .dmaRead => p.allowsRead | .dmaWrite => p.allowsWrite
inductive ProtectedFrameClass where
  | commitPrivate | pdCodeStackCspace | trngMmio | kernelPageTable deriving DecidableEq, Repr
def ProtectedFrameClass.tagByte : ProtectedFrameClass → UInt8
  | .commitPrivate => 1 | .pdCodeStackCspace => 2 | .trngMmio => 3 | .kernelPageTable => 4
theorem ProtectedFrameClass.tagByte_injective {a b : ProtectedFrameClass} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
inductive DmaRegionKind where
  | ingressRing | persistWalPool | egressOutboxRing | displayFramebuffer | cameraRing
  | commitPrivateFrame | pdCodeStackCspace | trngMmio | gpuScratchPool deriving DecidableEq, Repr
def DmaRegionKind.tagByte : DmaRegionKind → UInt8
  | .ingressRing => 1 | .commitPrivateFrame => 2 | .pdCodeStackCspace => 3 | .trngMmio => 4
  | .persistWalPool => 5 | .egressOutboxRing => 6 | .displayFramebuffer => 7 | .cameraRing => 8 | .gpuScratchPool => 9
theorem DmaRegionKind.tagByte_injective {a b : DmaRegionKind} (h : a.tagByte = b.tagByte) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h
structure ProtectedPhysRange where (classTag : ProtectedFrameClass) (basePaddr size : UInt64) deriving DecidableEq, Repr
structure Stage2DmaRegion where
  (iova paddr size : UInt64) (granule : PageGranule) (perm : IoPerm) (kind : DmaRegionKind) deriving DecidableEq, Repr
structure Stage2IoPageTable where
  (streamId : StreamId) (role : DeviceRole) (ownerPd : ChokepointPdRole) (regions : List Stage2DmaRegion)
  deriving DecidableEq, Repr
structure SmmuManifest where
  (arch : SmmuArch) (defaultDeny : Bool) (rootserverPhysStart rootserverPhysEnd dmaPoolBase dmaPoolSize : UInt64)
  (protectedRanges : List ProtectedPhysRange) (streams : List Stage2IoPageTable) deriving DecidableEq, Repr
structure ChokepointFramePartition where
  (rootServerBootSpan : UInt64 × UInt64)
  (ingressRingFrames commitPrivateFrames kernelAndCodeFrames persistFrames egressOutboxFrames : List Nat)
  deriving DecidableEq, Repr
structure ChokepointSmmuConfig where (manifest : SmmuManifest) (partition : ChokepointFramePartition) deriving DecidableEq, Repr

/-! ## 2. Specification-Level Stage-2 DMA Translation & Completeness -/
inductive SmmuDmaFault where
  | bypassModeDisabled | invalidStreamId (sid : StreamId) | faultOnUnmappedStream (sid : StreamId)
  | zeroOrUnmappedIova (sid : StreamId) (iova len : Nat) | permissionFault (sid : StreamId) (req : DmaAccess) (havePerm : IoPerm)
  deriving DecidableEq, Repr
def lookupStream (streams : List Stage2IoPageTable) (sid : StreamId) : Option Stage2IoPageTable :=
  streams.find? fun pt => pt.streamId == sid
def lookupDmaRegion (regions : List Stage2DmaRegion) (iova len : Nat) : Option Stage2DmaRegion :=
  regions.find? fun r => decide (r.iova.toNat ≤ iova ∧ iova + len ≤ r.iova.toNat + r.size.toNat)
def translateStage2Dma (m : SmmuManifest) (sid : StreamId) (iova len : Nat) (acc : DmaAccess) : Except SmmuDmaFault Nat :=
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
theorem find_some_mem_pred {α : Type} {xs : List α} {p : α → Bool} {x : α} (h : xs.find? p = some x) : x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => cases h
  | cons a as ih =>
    simp only [List.find?_cons] at h; cases hp : p a <;> simp only [hp] at h
    · obtain ⟨hm, hpx⟩ := ih h; exact ⟨List.mem_cons_of_mem _ hm, hpx⟩
    · injection h with hEq; subst hEq; exact ⟨List.mem_cons_self, hp⟩
theorem lookupStream_some {streams : List Stage2IoPageTable} {sid : StreamId} {pt : Stage2IoPageTable}
    (h : lookupStream streams sid = some pt) : pt ∈ streams ∧ pt.streamId = sid := by
  obtain ⟨hm, hp⟩ := find_some_mem_pred h; exact ⟨hm, beq_iff_eq.mp hp⟩
theorem lookupDmaRegion_some {regions : List Stage2DmaRegion} {iova len : Nat} {reg : Stage2DmaRegion}
    (h : lookupDmaRegion regions iova len = some reg) :
    reg ∈ regions ∧ reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat := by
  obtain ⟨hm, hp⟩ := find_some_mem_pred h; obtain ⟨h1, h2⟩ := decide_eq_true_eq.mp hp; exact ⟨hm, h1, h2⟩
theorem translateStage2Dma_ok {m : SmmuManifest} {sid : StreamId} {iova len : Nat} {acc : DmaAccess} {pa : Nat}
    (h : translateStage2Dma m sid iova len acc = .ok pa) :
    m.defaultDeny = true ∧ sid ≠ 0 ∧ sid ≠ wildcardStreamId ∧ 0 < len ∧
      ∃ pt ∈ m.streams, pt.streamId = sid ∧ ∃ reg ∈ pt.regions,
        reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat ∧
        reg.perm.permits acc = true ∧ pa = reg.paddr.toNat + (iova - reg.iova.toNat) := by
  unfold translateStage2Dma at h
  cases hd : m.defaultDeny; · simp [hd] at h
  simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h; · cases h
  rename_i hsid; split at h; · cases h
  rename_i hlen
  cases hst : lookupStream m.streams sid with
  | none => simp [hst] at h
  | some pt =>
    simp only [hst] at h
    cases hreg : lookupDmaRegion pt.regions iova len with
    | none => simp [hreg] at h
    | some reg =>
      simp only [hreg] at h
      cases hperm : reg.perm.permits acc
      · simp [hperm] at h
      · simp only [hperm, ↓reduceIte] at h
        injection h with hpa; obtain ⟨hptMem, hptSid⟩ := lookupStream_some hst
        obtain ⟨hregMem, hlo, hhi⟩ := lookupDmaRegion_some hreg
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hsid
        exact ⟨rfl, hsid.1, hsid.2, Nat.pos_of_ne_zero (by simpa [beq_iff_eq] using hlen),
          pt, hptMem, hptSid, reg, hregMem, hlo, hhi, hperm, hpa.symm⟩
theorem unmapped_stream_dma_faults (m : SmmuManifest) (sid : StreamId) (iova len : Nat) (acc : DmaAccess)
    (hDeny : m.defaultDeny = true) (hSid0 : sid ≠ 0) (hSidWild : sid ≠ wildcardStreamId) (hLen : 0 < len)
    (hUnmapped : ∀ pt ∈ m.streams, pt.streamId ≠ sid) :
    translateStage2Dma m sid iova len acc = .error (.faultOnUnmappedStream sid) := by
  have hFind : lookupStream m.streams sid = none :=
    List.find?_eq_none.mpr fun pt hmem hEq => hUnmapped pt hmem (beq_iff_eq.mp hEq)
  have hSidB : (sid == 0 || sid == wildcardStreamId) = false := by simp [hSid0, hSidWild]
  have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [translateStage2Dma, hDeny, hSidB, hLenB, hFind]
def RegionsIovaDisjoint (regions : List Stage2DmaRegion) : Prop :=
  ∀ a ∈ regions, ∀ b ∈ regions,
    a.iova.toNat < b.iova.toNat + b.size.toNat → b.iova.toNat < a.iova.toNat + a.size.toNat → a = b
def RegionsNonCoalescable (regions : List Stage2DmaRegion) : Prop :=
  ∀ a ∈ regions, ∀ b ∈ regions,
    a.iova.toNat + a.size.toNat = b.iova.toNat → a.paddr.toNat + a.size.toNat = b.paddr.toNat → a.perm ≠ b.perm
def checkRegionsNonCoalescable (regs : List Stage2DmaRegion) : Bool :=
  regs.all fun a => regs.all fun b =>
    !(a.iova.toNat + a.size.toNat == b.iova.toNat && a.paddr.toNat + a.size.toNat == b.paddr.toNat) || a.perm != b.perm
theorem checkRegionsNonCoalescable_sound {regs : List Stage2DmaRegion}
    (h : checkRegionsNonCoalescable regs = true) : RegionsNonCoalescable regs := by
  intro a ha b hb hI hP; have h1 := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
  simp only [hI, hP, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, bne_iff_ne] at h1; exact h1
theorem nodup_streamId_eq {streams : List Stage2IoPageTable} (hNodup : (streams.map Stage2IoPageTable.streamId).Nodup)
    {a b : Stage2IoPageTable} (ha : a ∈ streams) (hb : b ∈ streams) (heq : a.streamId = b.streamId) : a = b := by
  induction streams with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hNodup
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd ⟨b, hb', heq.symm⟩ hNodup.1
    · exact absurd ⟨a, ha', heq⟩ hNodup.1
    · exact ih hNodup.2 ha' hb'
theorem translateStage2Dma_skip_implies_contract_violation (m : SmmuManifest) (sid : StreamId)
    (iova len : Nat) (acc : DmaAccess) (err : SmmuDmaFault)
    (hErr : translateStage2Dma m sid iova len acc = .error err) (hDeny : m.defaultDeny = true) :
    sid = 0 ∨ sid = wildcardStreamId ∨ len = 0 ∨ (∀ pt ∈ m.streams, pt.streamId ≠ sid) ∨
      ∃ pt ∈ m.streams, pt.streamId = sid ∧ (RegionsIovaDisjoint pt.regions →
        ∀ reg ∈ pt.regions, ¬ (reg.iova.toNat ≤ iova ∧ iova + len ≤ reg.iova.toNat + reg.size.toNat ∧ reg.perm.permits acc = true)) := by
  by_cases hs0 : sid = 0; · exact .inl hs0
  by_cases hsw : sid = wildcardStreamId; · exact .inr (.inl hsw)
  by_cases hl0 : len = 0; · exact .inr (.inr (.inl hl0))
  cases hst : lookupStream m.streams sid with
  | none => exact .inr (.inr (.inr (.inl fun pt hmem hEq => List.find?_eq_none.mp hst pt hmem (beq_iff_eq.mpr hEq))))
  | some pt =>
    obtain ⟨hptMem, hptSid⟩ := lookupStream_some hst
    refine .inr (.inr (.inr (.inr ⟨pt, hptMem, hptSid, fun hDisj reg hregMem ⟨hlo, hhi, hperm⟩ => ?_⟩)))
    have hFindSt : lookupStream m.streams pt.streamId = some pt := hptSid ▸ hst
    have hFindReg : lookupDmaRegion pt.regions iova len = some reg := by
      cases hf : lookupDmaRegion pt.regions iova len with
      | none => exact absurd (decide_eq_true ⟨hlo, hhi⟩) (List.find?_eq_none.mp hf reg hregMem)
      | some r' =>
        obtain ⟨hr'Mem, hr'Lo, hr'Hi⟩ := lookupDmaRegion_some hf
        rw [hDisj r' hr'Mem reg hregMem (by omega) (by omega)]
    subst hptSid
    have hSidB : (pt.streamId == 0 || pt.streamId == wildcardStreamId) = false := by simp [hs0, hsw]
    have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [translateStage2Dma, hDeny, hSidB, hLenB, hFindSt, hFindReg, hperm] at hErr
def rangesDisjointB (b1 s1 b2 s2 : Nat) : Bool := decide (b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1 ∨ s1 = 0 ∨ s2 = 0)
def checkRegionsIovaDisjoint : List Stage2DmaRegion → Bool
  | [] => true
  | r :: rs =>
    rs.all (fun r' => decide (r.iova.toNat + r.size.toNat ≤ r'.iova.toNat ∨
      r'.iova.toNat + r'.size.toNat ≤ r.iova.toNat)) && checkRegionsIovaDisjoint rs
theorem checkRegionsIovaDisjoint_sound {regions : List Stage2DmaRegion}
    (h : checkRegionsIovaDisjoint regions = true) : RegionsIovaDisjoint regions := by
  induction regions with
  | nil => intro _ ha; cases ha
  | cons r rs ih =>
    simp only [checkRegionsIovaDisjoint, Bool.and_eq_true, List.all_eq_true] at h
    intro a ha b hb h1 h2
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · rcases decide_eq_true_eq.mp (h.1 b hb') with hd | hd <;> omega
    · rcases decide_eq_true_eq.mp (h.1 a ha') with hd | hd <;> omega
    · exact ih h.2 a ha' b hb' h1 h2
theorem checkRegionsIovaDisjoint_complete {regions : List Stage2DmaRegion}
    (hNodup : regions.Nodup) (hPos : ∀ r ∈ regions, 0 < r.size.toNat)
    (hDisj : RegionsIovaDisjoint regions) : checkRegionsIovaDisjoint regions = true := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨hrNotMem, hrsNodup⟩ := List.nodup_cons.mp hNodup
    simp only [checkRegionsIovaDisjoint, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun r' hr' => decide_eq_true ?_,
      ih hrsNodup (fun x hx => hPos x (List.mem_cons_of_mem _ hx))
        (fun a ha b hb => hDisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    by_cases hLe : r.iova.toNat + r.size.toNat ≤ r'.iova.toNat
    · exact .inl hLe
    · by_cases hLe' : r'.iova.toNat + r'.size.toNat ≤ r.iova.toNat
      · exact .inr hLe'
      · exfalso
        have hEq := hDisj r List.mem_cons_self r' (List.mem_cons_of_mem _ hr') (by omega) (by omega)
        exact hrNotMem (hEq ▸ hr')
def regionAlignedInPoolB (m : SmmuManifest) (reg : Stage2DmaRegion) : Bool :=
  decide (0 < reg.size.toNat) && decide (reg.iova.toNat + reg.size.toNat ≤ smmuAddrLimit48) &&
  decide (reg.paddr.toNat + reg.size.toNat ≤ smmuAddrLimit48) &&
  (reg.iova.toNat % reg.granule.byteSize == 0) && (reg.paddr.toNat % reg.granule.byteSize == 0) &&
  (reg.size.toNat % reg.granule.byteSize == 0) &&
  decide (m.dmaPoolBase.toNat ≤ reg.paddr.toNat ∧ reg.paddr.toNat + reg.size.toNat ≤ m.dmaPoolBase.toNat + m.dmaPoolSize.toNat)
def streamsNoWildcardB (m : SmmuManifest) : Bool :=
  decide (m.streams.map Stage2IoPageTable.streamId).Nodup &&
  m.streams.all fun pt => pt.streamId != 0 && pt.streamId != wildcardStreamId
def streamsAlignedInPoolB (m : SmmuManifest) : Bool :=
  m.streams.all fun pt => checkRegionsIovaDisjoint pt.regions && pt.regions.all (regionAlignedInPoolB m)
inductive PeripheralDmaOp where
  | read (sid : StreamId) (iova len : Nat) | write (sid : StreamId) (iova : Nat) (payload : ByteArray)
  deriving DecidableEq
def writePhys (mem : Nat → UInt8) (pa : Nat) (payload : ByteArray) : Nat → UInt8 :=
  fun a => if pa ≤ a ∧ a < pa + payload.size then payload.data[a - pa]?.getD (mem a) else mem a
def execStage2DmaOp (m : SmmuManifest) (mem : Nat → UInt8) : PeripheralDmaOp → (Nat → UInt8) × Option ByteArray
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

/-! ## 3. Hardware-Real 512-Bit Armv8 SMMUv3 `SmmuV3Ste` (`STE.EATS=0b00` + Platform `CR0.ATSCHK=1`/ACS) & RISC-V `RiscvDdtEntry` -/
theorem u64_toNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt h
theorem u16_toNat_of_lt {n : Nat} (h : n < 65536) : (UInt16.ofNat n).toNat = n := UInt16.toNat_ofNat_of_lt h
structure SmmuV3Ste where (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) deriving DecidableEq, Repr
def SmmuV3Ste.abort : SmmuV3Ste := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
def steW2Stage2Hi32 : Nat := 0x040d0090
def SmmuV3Ste.packStage2 (vmid : UInt16) (s2ttbPa : UInt64) : SmmuV3Ste :=
  ⟨UInt64.ofNat 0x0d, 0, UInt64.ofNat (vmid.toNat + steW2Stage2Hi32 * 4294967296),
    UInt64.ofNat (((s2ttbPa.toNat % smmuAddrLimit48) / pageSize) * pageSize), 0, 0, 0, 0⟩
def SmmuV3Ste.packStage2Checked (vmid : UInt16) (s2ttbPa : UInt64) : Option SmmuV3Ste :=
  if vmid.toNat == 0 || decide (s2ttbPa.toNat ≥ smmuAddrLimit48) || s2ttbPa.toNat % pageSize != 0 then none
  else some (SmmuV3Ste.packStage2 vmid s2ttbPa)
inductive DecodedSte where | abort | stage2 (vmid : UInt16) (s2ttbPa : UInt64) deriving DecidableEq, Repr
def decodeSmmuV3Ste (ste : SmmuV3Ste) : Option DecodedSte :=
  if ste.w0.toNat % 2 == 0 then
    if ste == SmmuV3Ste.abort then some .abort else none
  else
    let cfg := (ste.w0.toNat / 2) % 8
    let eats := (ste.w1.toNat / (2 ^ 28)) % 4
    let vmidNat := ste.w2.toNat % 65536
    let hi32 := ste.w2.toNat / 4294967296
    let t0sz := hi32 % 64
    let sl0 := (hi32 / 64) % 4
    let tg := (hi32 / 16384) % 4
    let ps := (hi32 / 65536) % 8
    let aa64 := (hi32 / 524288) % 2
    let s2s := (hi32 / 33554432) % 2
    let s2r := (hi32 / 67108864) % 2
    if cfg != 6 || ste.w0.toNat != 0x0d || eats != 0 || ste.w1.toNat != 0 || vmidNat == 0 ||
        t0sz != 16 || sl0 != 2 || tg != 0 || ps != 5 || aa64 != 1 || s2s != 0 || s2r != 1 ||
        ste.w2.toNat / 65536 != steW2Stage2Hi32 * 65536 ||
        decide (ste.w3.toNat ≥ smmuAddrLimit48) || ste.w3.toNat % pageSize != 0 ||
        ste.w4 != 0 || ste.w5 != 0 || ste.w6 != 0 || ste.w7 != 0 then none
    else some (.stage2 (UInt16.ofNat vmidNat) ste.w3)
theorem decodeSmmuV3Ste_packStage2 {vmid : UInt16} {s2ttbPa : UInt64}
    (hVmid : 0 < vmid.toNat) (hLt : s2ttbPa.toNat < smmuAddrLimit48) (hAlign : s2ttbPa.toNat % pageSize = 0) :
    decodeSmmuV3Ste (SmmuV3Ste.packStage2 vmid s2ttbPa) = some (.stage2 vmid s2ttbPa) := by
  have hvLt : vmid.toNat < 65536 := vmid.toBitVec.isLt
  have hw2Nat : (UInt64.ofNat (vmid.toNat + steW2Stage2Hi32 * 4294967296)).toNat = vmid.toNat + steW2Stage2Hi32 * 4294967296 :=
    u64_toNat_of_lt (by simp only [steW2Stage2Hi32]; omega)
  have hw3U64 : UInt64.ofNat (((s2ttbPa.toNat % smmuAddrLimit48) / pageSize) * pageSize) = s2ttbPa := by
    have : ((s2ttbPa.toNat % smmuAddrLimit48) / pageSize) * pageSize = s2ttbPa.toNat := by simp only [smmuAddrLimit48, pageSize] at hLt hAlign ⊢; omega
    rw [this]; exact UInt64.ofNat_toNat
  have hMod : (vmid.toNat + steW2Stage2Hi32 * 4294967296) % 65536 = vmid.toNat := by
    rw [show steW2Stage2Hi32 * 4294967296 = (steW2Stage2Hi32 * 65536) * 65536 by decide, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvLt]
  have hDiv65k : (vmid.toNat + steW2Stage2Hi32 * 4294967296) / 65536 = steW2Stage2Hi32 * 65536 := by
    rw [show steW2Stage2Hi32 * 4294967296 = (steW2Stage2Hi32 * 65536) * 65536 by decide, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hvLt, Nat.zero_add]
  have hHi : (vmid.toNat + steW2Stage2Hi32 * 4294967296) / 4294967296 = steW2Stage2Hi32 := by
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hVmNe : (vmid.toNat == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hNotGe : decide (s2ttbPa.toNat ≥ smmuAddrLimit48) = false := decide_eq_false_iff_not.mpr (by omega)
  unfold decodeSmmuV3Ste SmmuV3Ste.packStage2; dsimp only []
  have hW0 : (UInt64.ofNat 0x0d).toNat = 0x0d := rfl; have hW1 : (0 : UInt64).toNat = 0 := rfl
  rw [hW0, hW1, hw2Nat, hw3U64, hMod, hDiv65k, hHi, hVmNe, hNotGe, hAlign]; simp [steW2Stage2Hi32, UInt16.ofNat_toNat]
theorem ste_eats_nonzero_refused (ste : SmmuV3Ste) (hEats : (ste.w1.toNat / (2 ^ 28)) % 4 ≠ 0) : decodeSmmuV3Ste ste = none := by
  dsimp only [decodeSmmuV3Ste]; cases hV : (ste.w0.toNat % 2 == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]; have hNeB : (((ste.w1.toNat / 2 ^ 28) % 4) != 0) = true := bne_iff_ne.mpr hEats; simp [hNeB]
  · simp only [↓reduceIte]; have hNeAbort : (ste == SmmuV3Ste.abort) = false := by
      cases hEq : (ste == SmmuV3Ste.abort); · rfl
      have := beq_iff_eq.mp hEq; subst this; simp [SmmuV3Ste.abort] at hEats
    simp [hNeAbort]
/-- 256-bit RISC-V IOMMU Base-Format Device-Context (`DDTE`, `Sv48x4` `MODE=9`, `16 KiB`-aligned `PPN[1:0]=0`). -/
structure RiscvDdtEntry where (tc iohgatp ta fsc : UInt64) deriving DecidableEq, Repr
def RiscvDdtEntry.abort : RiscvDdtEntry := ⟨0, 0, 0, 0⟩
def RiscvDdtEntry.packSv48x4 (gscid : UInt16) (rootPa : UInt64) : RiscvDdtEntry :=
  ⟨1, UInt64.ofNat (9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + ((rootPa.toNat % smmuAddrLimit48) / sv48x4RootAlign) * 4), 0, 0⟩
def RiscvDdtEntry.packSv48x4Checked (gscid : UInt16) (rootPa : UInt64) : Option RiscvDdtEntry :=
  if gscid.toNat == 0 || decide (rootPa.toNat ≥ smmuAddrLimit48) || rootPa.toNat % sv48x4RootAlign != 0 then none
  else some (RiscvDdtEntry.packSv48x4 gscid rootPa)
inductive DecodedRiscvDdte where | abort | sv48x4 (gscid : UInt16) (rootPa : UInt64) deriving DecidableEq, Repr
def decodeRiscvDdtEntry (d : RiscvDdtEntry) : Option DecodedRiscvDdte :=
  if d.tc.toNat % 2 == 0 then
    if d == RiscvDdtEntry.abort then some .abort else none
  else
    let mode := d.iohgatp.toNat / (2 ^ 60)
    let gscidNat := (d.iohgatp.toNat / (2 ^ 44)) % 65536
    let rootPaNat := (d.iohgatp.toNat % (2 ^ 44)) * pageSize
    if d.tc.toNat != 1 || mode != 9 || gscidNat == 0 || decide (rootPaNat ≥ smmuAddrLimit48) ||
        rootPaNat % sv48x4RootAlign != 0 || d.ta != 0 || d.fsc != 0 then none
    else some (.sv48x4 (UInt16.ofNat gscidNat) (UInt64.ofNat rootPaNat))
theorem decodeRiscvDdtEntry_packSv48x4 {gscid : UInt16} {rootPa : UInt64}
    (hGscid : 0 < gscid.toNat) (hLt : rootPa.toNat < smmuAddrLimit48) (hAlign : rootPa.toNat % sv48x4RootAlign = 0) :
    decodeRiscvDdtEntry (RiscvDdtEntry.packSv48x4 gscid rootPa) = some (.sv48x4 gscid rootPa) := by
  have hgLt : gscid.toNat < 65536 := gscid.toBitVec.isLt
  have hIoh : (UInt64.ofNat (9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + ((rootPa.toNat % smmuAddrLimit48) / sv48x4RootAlign) * 4)).toNat =
      9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + (rootPa.toNat / sv48x4RootAlign) * 4 := by
    rw [Nat.mod_eq_of_lt hLt]; exact u64_toNat_of_lt (by simp only [smmuAddrLimit48, sv48x4RootAlign] at hLt ⊢; omega)
  have hMode : (9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + (rootPa.toNat / sv48x4RootAlign) * 4) / 2 ^ 60 = 9 := by
    simp only [smmuAddrLimit48, sv48x4RootAlign] at hLt ⊢; omega
  have hGs : ((9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + (rootPa.toNat / sv48x4RootAlign) * 4) / 2 ^ 44) % 65536 = gscid.toNat := by
    simp only [smmuAddrLimit48, sv48x4RootAlign] at hLt ⊢; omega
  have hPpn : ((9 * 2 ^ 60 + gscid.toNat * 2 ^ 44 + (rootPa.toNat / sv48x4RootAlign) * 4) % 2 ^ 44) * pageSize = rootPa.toNat := by
    simp only [smmuAddrLimit48, sv48x4RootAlign, pageSize] at hLt hAlign ⊢; omega
  have hGsNe : (gscid.toNat == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hNotGe : decide (rootPa.toNat ≥ smmuAddrLimit48) = false := decide_eq_false_iff_not.mpr (by omega)
  have hTc : (1 : UInt64).toNat = 1 := rfl
  unfold decodeRiscvDdtEntry RiscvDdtEntry.packSv48x4; dsimp only []
  rw [hTc, hIoh, hMode, hGs, hPpn, hGsNe, hNotGe, hAlign]
  simp [UInt16.ofNat_toNat, UInt64.ofNat_toNat]

/-! ## 4. 4-Level (`9+9+9+9+12`) Armv8 Stage-2 Radix Arena Compiler & Multi-Page Hardware Walker -/
def IoPerm.s2apNat : IoPerm → Nat | .readOnly => 1 | .writeOnly => 2 | .readWrite => 3
def decodeS2ApNat : Nat → Option IoPerm
  | 1 => some .readOnly | 2 => some .writeOnly | 3 => some .readWrite | _ => none
def stage2XnAllNat : Nat := 18014398509481984
def stage2AfNat : Nat := 1024
def encodeStage2TableDesc (nextTablePa : UInt64) : UInt64 :=
  UInt64.ofNat (((nextTablePa.toNat % smmuAddrLimit48) / pageSize) * pageSize + 3)
def encodeStage2TableDescChecked (nextTablePa : UInt64) : Option UInt64 :=
  if decide (nextTablePa.toNat ≥ smmuAddrLimit48) || nextTablePa.toNat % pageSize != 0 then none else some (encodeStage2TableDesc nextTablePa)
def encodeStage2Block2MDesc (oa : UInt64) (perm : IoPerm) : UInt64 :=
  UInt64.ofNat (stage2XnAllNat + ((oa.toNat % smmuAddrLimit48) / hugeBlock2MiB) * hugeBlock2MiB + stage2AfNat + perm.s2apNat * 64 + 1)
def encodeStage2Block2MDescChecked (oa : UInt64) (perm : IoPerm) : Option UInt64 :=
  if decide (oa.toNat ≥ smmuAddrLimit48) || oa.toNat % hugeBlock2MiB != 0 then none else some (encodeStage2Block2MDesc oa perm)
def encodeStage2Page4KDesc (oa : UInt64) (perm : IoPerm) : UInt64 :=
  UInt64.ofNat (stage2XnAllNat + ((oa.toNat % smmuAddrLimit48) / pageSize) * pageSize + stage2AfNat + perm.s2apNat * 64 + 3)
def encodeStage2Page4KDescChecked (oa : UInt64) (perm : IoPerm) : Option UInt64 :=
  if decide (oa.toNat ≥ smmuAddrLimit48) || oa.toNat % pageSize != 0 then none else some (encodeStage2Page4KDesc oa perm)
def decodeStage2TableDesc (d : UInt64) : Option Nat :=
  let v := d.toNat
  if v % 4 != 3 || (v / 4) % 1024 != 0 || v / smmuAddrLimit48 != 0 then none
  else some (((v % smmuAddrLimit48) / pageSize) * pageSize)
def decodeStage2L2Desc (d : UInt64) : Option (Nat ⊕ (Nat × IoPerm)) :=
  let v := d.toNat
  if v == 0 then none
  else if v % 4 == 3 then (decodeStage2TableDesc d).map Sum.inl
  else if v % 4 == 1 then
    if (v / 4) % 16 != 0 || (v / 256) % 4 != 0 || (v / 1024) % 2 != 1 ||
        (v / 2048) % 1024 != 0 || v / smmuAddrLimit48 != 64 then none
    else match decodeS2ApNat ((v / 64) % 4) with
      | none => none
      | some perm => some (.inr (((v % smmuAddrLimit48) / hugeBlock2MiB) * hugeBlock2MiB, perm))
  else none
def decodeStage2L3Desc (d : UInt64) : Option (Nat × IoPerm) :=
  let v := d.toNat
  if v == 0 || v % 4 != 3 then none
  else if (v / 4) % 16 != 0 || (v / 256) % 4 != 0 || (v / 1024) % 2 != 1 ||
      (v / 2048) % 2 != 0 || v / smmuAddrLimit48 != 64 then none
  else match decodeS2ApNat ((v / 64) % 4) with
    | none => none
    | some perm => some (((v % smmuAddrLimit48) / pageSize) * pageSize, perm)
theorem decodeStage2TableDesc_encode {pa : UInt64}
    (hLt : pa.toNat < smmuAddrLimit48) (hAlign : pa.toNat % pageSize = 0) :
    decodeStage2TableDesc (encodeStage2TableDesc pa) = some pa.toNat := by
  have hNat : (encodeStage2TableDesc pa).toNat = pa.toNat + 3 := by
    unfold encodeStage2TableDesc; rw [Nat.mod_eq_of_lt hLt]
    have hDiv : (pa.toNat / pageSize) * pageSize = pa.toNat := by simp only [pageSize] at hAlign ⊢; omega
    rw [hDiv]; exact u64_toNat_of_lt (by simp only [smmuAddrLimit48] at hLt; omega)
  unfold decodeStage2TableDesc; dsimp only []; rw [hNat]
  have hCond : (((pa.toNat + 3) % 4 != 3) || (((pa.toNat + 3) / 4) % 1024 != 0) ||
      ((pa.toNat + 3) / smmuAddrLimit48 != 0)) = false := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq]
    simp only [smmuAddrLimit48, pageSize] at hLt hAlign ⊢; exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hOa : (((pa.toNat + 3) % smmuAddrLimit48) / pageSize) * pageSize = pa.toNat := by
    simp only [smmuAddrLimit48, pageSize] at hLt hAlign ⊢; omega
  rw [hCond]; simp [hOa]
theorem decodeStage2L2Desc_encodeTable {pa : UInt64}
    (hLt : pa.toNat < smmuAddrLimit48) (hAlign : pa.toNat % pageSize = 0) :
    decodeStage2L2Desc (encodeStage2TableDesc pa) = some (.inl pa.toNat) := by
  have hNat : (encodeStage2TableDesc pa).toNat = pa.toNat + 3 := by
    unfold encodeStage2TableDesc; rw [Nat.mod_eq_of_lt hLt]
    have hDiv : (pa.toNat / pageSize) * pageSize = pa.toNat := by simp only [pageSize] at hAlign ⊢; omega
    rw [hDiv]; exact u64_toNat_of_lt (by simp only [smmuAddrLimit48] at hLt; omega)
  unfold decodeStage2L2Desc; dsimp only []; rw [hNat]
  have hNe0 : ((pa.toNat + 3) == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hEq3 : ((pa.toNat + 3) % 4 == 3) = true := beq_iff_eq.mpr (by simp only [pageSize] at hAlign; omega)
  rw [hNe0, hEq3]; simp [decodeStage2TableDesc_encode hLt hAlign]
theorem decodeStage2L2Desc_encodeBlock2M {oa : UInt64} {perm : IoPerm}
    (hLt : oa.toNat < smmuAddrLimit48) (hAlign : oa.toNat % hugeBlock2MiB = 0) :
    decodeStage2L2Desc (encodeStage2Block2MDesc oa perm) = some (.inr (oa.toNat, perm)) := by
  have hpBnd : 1 ≤ perm.s2apNat ∧ perm.s2apNat ≤ 3 := by cases perm <;> simp [IoPerm.s2apNat]
  have hDecPerm : decodeS2ApNat perm.s2apNat = some perm := by cases perm <;> rfl
  let w := stage2XnAllNat + oa.toNat + stage2AfNat + perm.s2apNat * 64 + 1
  have hNat : (encodeStage2Block2MDesc oa perm).toNat = w := by
    unfold encodeStage2Block2MDesc; rw [Nat.mod_eq_of_lt hLt]
    have hDiv : (oa.toNat / hugeBlock2MiB) * hugeBlock2MiB = oa.toNat := by simp only [hugeBlock2MiB] at hAlign ⊢; omega
    rw [hDiv]; exact u64_toNat_of_lt (by simp only [stage2XnAllNat, stage2AfNat, smmuAddrLimit48] at hLt ⊢; omega)
  unfold decodeStage2L2Desc; dsimp only []; rw [hNat]
  have h0 : (w == 0) = false := beq_eq_false_iff_ne.mpr (by simp only [w, stage2XnAllNat, stage2AfNat]; omega)
  have h3 : (w % 4 == 3) = false := beq_eq_false_iff_ne.mpr (by simp only [w, stage2XnAllNat, stage2AfNat] at *; simp only [hugeBlock2MiB] at hAlign; omega)
  have h1 : (w % 4 == 1) = true := beq_iff_eq.mpr (by simp only [w, stage2XnAllNat, stage2AfNat] at *; simp only [hugeBlock2MiB] at hAlign; omega)
  have hFlags : (((w / 4) % 16 != 0) || ((w / 256) % 4 != 0) || ((w / 1024) % 2 != 1) ||
      ((w / 2048) % 1024 != 0) || (w / smmuAddrLimit48 != 64)) = false := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq]
    simp only [w, stage2XnAllNat, stage2AfNat, smmuAddrLimit48, hugeBlock2MiB] at hLt hAlign ⊢
    exact ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  have hAp : (w / 64) % 4 = perm.s2apNat := by
    simp only [w, stage2XnAllNat, stage2AfNat, hugeBlock2MiB] at hAlign ⊢; omega
  have hOa : ((w % smmuAddrLimit48) / hugeBlock2MiB) * hugeBlock2MiB = oa.toNat := by
    simp only [w, stage2XnAllNat, stage2AfNat, smmuAddrLimit48, hugeBlock2MiB] at hLt hAlign ⊢; omega
  rw [h0, h3, h1, hFlags, hAp, hDecPerm, hOa]; rfl
theorem decodeStage2L3Desc_encodePage4K {oa : UInt64} {perm : IoPerm}
    (hLt : oa.toNat < smmuAddrLimit48) (hAlign : oa.toNat % pageSize = 0) :
    decodeStage2L3Desc (encodeStage2Page4KDesc oa perm) = some (oa.toNat, perm) := by
  have hpBnd : 1 ≤ perm.s2apNat ∧ perm.s2apNat ≤ 3 := by cases perm <;> simp [IoPerm.s2apNat]
  have hDecPerm : decodeS2ApNat perm.s2apNat = some perm := by cases perm <;> rfl
  let w := stage2XnAllNat + oa.toNat + stage2AfNat + perm.s2apNat * 64 + 3
  have hNat : (encodeStage2Page4KDesc oa perm).toNat = w := by
    unfold encodeStage2Page4KDesc; rw [Nat.mod_eq_of_lt hLt]
    have hDiv : (oa.toNat / pageSize) * pageSize = oa.toNat := by simp only [pageSize] at hAlign ⊢; omega
    rw [hDiv]; exact u64_toNat_of_lt (by simp only [stage2XnAllNat, stage2AfNat, smmuAddrLimit48] at hLt ⊢; omega)
  unfold decodeStage2L3Desc; dsimp only []; rw [hNat]
  have hG0 : ((w == 0) || (w % 4 != 3)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
    simp only [w, stage2XnAllNat, stage2AfNat, pageSize] at hAlign ⊢; exact ⟨by omega, by omega⟩
  have hFlags : (((w / 4) % 16 != 0) || ((w / 256) % 4 != 0) || ((w / 1024) % 2 != 1) ||
      ((w / 2048) % 2 != 0) || (w / smmuAddrLimit48 != 64)) = false := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq]
    simp only [w, stage2XnAllNat, stage2AfNat, smmuAddrLimit48, pageSize] at hLt hAlign ⊢
    exact ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  have hAp : (w / 64) % 4 = perm.s2apNat := by
    simp only [w, stage2XnAllNat, stage2AfNat, pageSize] at hAlign ⊢; omega
  have hOa : ((w % smmuAddrLimit48) / pageSize) * pageSize = oa.toNat := by
    simp only [w, stage2XnAllNat, stage2AfNat, smmuAddrLimit48, pageSize] at hLt hAlign ⊢; omega
  rw [hG0, hFlags, hAp, hDecPerm, hOa]; rfl
/-- Concrete Armv8 SMMUv3 linear Stream Table + 4-level VMSAv8-64 Stage-2 radix table arena. -/
structure SmmuV3RadixArena where
  (smmuEnabled : Bool) (arenaBase : UInt64) (streamTableFrames : Nat)
  (streamTable : Array SmmuV3Ste) (tables : Array (Array UInt64)) deriving DecidableEq, Repr
inductive SmmuRadixBuildError where
  | armSmmuV3Required | defaultDenyDisabled | invalidStreams | unalignedArenaBase
  | arenaNotProtectedByKernelPageTable | streamTableTooLarge | arenaCapacityExhausted deriving DecidableEq, Repr
def nextSteCountPow2 (need : Nat) : Nat :=
  if need ≤ 64 then 64 else if need ≤ 128 then 128 else if need ≤ 256 then 256
  else if need ≤ 512 then 512 else if need ≤ 1024 then 1024 else if need ≤ 2048 then 2048 else 4096
theorem le_nextSteCountPow2 {need : Nat} (h : need ≤ 4096) : need ≤ nextSteCountPow2 need := by
  unfold nextSteCountPow2; repeat (first | omega | split)
def regionCovers4K (reg : Stage2DmaRegion) (pageIova : Nat) : Bool :=
  reg.granule == .page4KiB && decide (reg.iova.toNat ≤ pageIova ∧ pageIova + pageSize ≤ reg.iova.toNat + reg.size.toNat)
def regionCovers2M (reg : Stage2DmaRegion) (blockIova : Nat) : Bool :=
  reg.granule == .huge2MiB && decide (reg.iova.toNat ≤ blockIova ∧ blockIova + hugeBlock2MiB ≤ reg.iova.toNat + reg.size.toNat)
def regionsTouchWindow (regs : List Stage2DmaRegion) (winBase winSize : Nat) : Bool :=
  regs.any fun r => decide (r.iova.toNat < winBase + winSize ∧ winBase < r.iova.toNat + r.size.toNat)
def allocRadixTable (arenaBase stFrames : Nat) (tables : Array (Array UInt64))
    (entries : Array UInt64) : UInt64 × Array (Array UInt64) :=
  (UInt64.ofNat (arenaBase + (stFrames + tables.size) * pageSize), tables.push entries)
def mapAllocAux {σ : Type} (f : Nat → σ → UInt64 × σ) : Nat → Nat → σ → List UInt64 × σ
  | _, 0, st => ([], st)
  | i, k + 1, st =>
    let p₁ := f i st
    let p₂ := mapAllocAux f (i + 1) k p₁.2
    (p₁.1 :: p₂.1, p₂.2)
def buildL3Entries (regs : List Stage2DmaRegion) (base2M : Nat) : Array UInt64 :=
  Array.ofFn fun (i3 : Fin 512) =>
    let pageIova := base2M + i3.val * pageSize
    match regs.find? (fun r => regionCovers4K r pageIova) with
    | none => 0
    | some r => encodeStage2Page4KDesc (UInt64.ofNat (r.paddr.toNat + (pageIova - r.iova.toNat))) r.perm
def buildL2Step (arenaBase stFrames : Nat) (regs : List Stage2DmaRegion) (base1G : Nat)
    (i2 : Nat) (st : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  let blockIova := base1G + i2 * hugeBlock2MiB
  match regs.find? (fun r => regionCovers2M r blockIova) with
  | some r => (encodeStage2Block2MDesc (UInt64.ofNat (r.paddr.toNat + (blockIova - r.iova.toNat))) r.perm, st)
  | none =>
    if regionsTouchWindow regs blockIova hugeBlock2MiB then
      let (l3Pa, st') := allocRadixTable arenaBase stFrames st (buildL3Entries regs blockIova)
      (encodeStage2TableDesc l3Pa, st')
    else (0, st)
def buildL2Table (arenaBase stFrames : Nat) (regs : List Stage2DmaRegion) (base1G : Nat)
    (tables : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  let res := mapAllocAux (buildL2Step arenaBase stFrames regs base1G) 0 512 tables
  allocRadixTable arenaBase stFrames res.2 (Array.mk res.1)
def buildBranchStepFn (regs : List Stage2DmaRegion) (base winSize : Nat)
    (buildChild : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64))
    (idx : Nat) (st : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  let childBase := base + idx * winSize
  if regionsTouchWindow regs childBase winSize then
    let child := buildChild childBase st
    (encodeStage2TableDesc child.1, child.2)
  else (0, st)
def buildBranchTable (arenaBase stFrames : Nat) (regs : List Stage2DmaRegion) (base winSize : Nat)
    (buildChild : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64))
    (tables : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  let res := mapAllocAux (buildBranchStepFn regs base winSize buildChild) 0 512 tables
  allocRadixTable arenaBase stFrames res.2 (Array.mk res.1)
def buildL1Table (arenaBase stFrames : Nat) (regs : List Stage2DmaRegion) (base512G : Nat)
    (tables : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  buildBranchTable arenaBase stFrames regs base512G l1WinSize (buildL2Table arenaBase stFrames regs) tables
def buildL0Table (arenaBase stFrames : Nat) (regs : List Stage2DmaRegion)
    (tables : Array (Array UInt64)) : UInt64 × Array (Array UInt64) :=
  buildBranchTable arenaBase stFrames regs 0 l0WinSize (buildL1Table arenaBase stFrames regs) tables
def compileStreamRoots (arenaBase stFrames : Nat) :
    List Stage2IoPageTable → Array (Array UInt64) → List (StreamId × UInt16 × UInt64) × Array (Array UInt64)
  | [], tables => ([], tables)
  | pt :: pts, tables =>
    let r₀ := buildL0Table arenaBase stFrames pt.regions tables
    let r₁ := compileStreamRoots arenaBase stFrames pts r₀.2
    ((pt.streamId, UInt16.ofNat pt.streamId.toNat, r₀.1) :: r₁.1, r₁.2)
def maxManifestSid (streams : List Stage2IoPageTable) : Nat :=
  streams.foldl (fun acc pt => max acc pt.streamId.toNat) 0
def arenaProtectedByKernelPtB (m : SmmuManifest) (arenaBase : UInt64) (maxFrames : Nat) : Bool :=
  m.protectedRanges.any fun pr =>
    pr.classTag == .kernelPageTable &&
      decide (pr.basePaddr.toNat ≤ arenaBase.toNat ∧ arenaBase.toNat + maxFrames * pageSize ≤ pr.basePaddr.toNat + pr.size.toNat)
def streamsNonCoalescableB (m : SmmuManifest) : Bool :=
  m.streams.all fun pt => checkRegionsNonCoalescable pt.regions
def mkStreamTableSte (roots : List (StreamId × UInt16 × UInt64)) (sidVal : Nat) : SmmuV3Ste :=
  match roots.find? (fun r => r.1.toNat == sidVal) with
  | none => SmmuV3Ste.abort | some (_, vmid, l0Pa) => SmmuV3Ste.packStage2 vmid l0Pa
/-- Compile an Armv8 SMMUv3 `SmmuManifest` into a naturally-aligned (`SMMU_STRTAB_BASE` `2^LOG2SIZE * 64B`)
linear Stream Table + 1 Command-Queue frame + 4-level VMSAv8-64 Stage-2 radix tables. -/
def compileManifestToRadixArena (m : SmmuManifest) (arenaBase : UInt64) (maxFrames : Nat) :
    Except SmmuRadixBuildError SmmuV3RadixArena :=
  if m.arch != .armSmmuV3 then .error .armSmmuV3Required
  else if !m.defaultDeny then .error .defaultDenyDisabled
  else if !streamsNoWildcardB m || !streamsAlignedInPoolB m || !streamsNonCoalescableB m then .error .invalidStreams
  else
    let maxSid := maxManifestSid m.streams
    if decide (maxSid ≥ 4096) then .error .streamTableTooLarge
    else
      let tableCount := nextSteCountPow2 (maxSid + 1); let stBytes := tableCount * 64
      if arenaBase.toNat % stBytes != 0 || arenaBase.toNat % pageSize != 0 || maxFrames == 0 ||
          decide (arenaBase.toNat + maxFrames * pageSize > smmuAddrLimit48) then .error .unalignedArenaBase
      else if !arenaProtectedByKernelPtB m arenaBase maxFrames then .error .arenaNotProtectedByKernelPageTable
      else
        let stFrames := stBytes / pageSize + 1; let compiled := compileStreamRoots arenaBase.toNat stFrames m.streams #[]
        if decide (stFrames + compiled.2.size > maxFrames) then .error .arenaCapacityExhausted
        else .ok ⟨true, arenaBase, stFrames, Array.ofFn (fun (sid : Fin tableCount) => mkStreamTableSte compiled.1 sid.val), compiled.2⟩
def lookupRadixTable (arena : SmmuV3RadixArena) (pa : Nat) : Option (Array UInt64) :=
  let ptBase := arena.arenaBase.toNat + arena.streamTableFrames * pageSize
  if decide (pa < ptBase) || (pa - ptBase) % pageSize != 0 then none
  else match arena.tables[(pa - ptBase) / pageSize]? with
    | some entries => if entries.size == 512 then some entries else none | none => none
def decodeArenaStreamRoot (arena : SmmuV3RadixArena) (sid : StreamId) : Option (UInt16 × UInt64) :=
  match arena.streamTable[sid.toNat]? >>= decodeSmmuV3Ste with
  | some (.stage2 vmid l0Pa) => some (vmid, l0Pa) | _ => none
def tableIdenticalAtB (oldA newA : SmmuV3RadixArena) (pa : Nat) (checkEntry : UInt64 → Bool) : Bool :=
  match lookupRadixTable oldA pa, lookupRadixTable newA pa with
  | some t1, some t2 => t1 == t2 && t1.all checkEntry | _, _ => false
def streamSubtreeIdenticalB (oldA newA : SmmuV3RadixArena) (s : StreamId) : Bool :=
  match decodeArenaStreamRoot oldA s, decodeArenaStreamRoot newA s with
  | none, none => true
  | some (v1, l0a), some (v2, l0b) =>
    v1 == v2 && l0a == l0b && tableIdenticalAtB oldA newA l0a.toNat fun d0 =>
      match decodeStage2TableDesc d0 with
      | none => true
      | some l1Pa => tableIdenticalAtB oldA newA l1Pa fun d1 =>
        match decodeStage2TableDesc d1 with
        | none => true
        | some l2Pa => tableIdenticalAtB oldA newA l2Pa fun d2 =>
          match decodeStage2L2Desc d2 with
          | some (.inl l3Pa) => lookupRadixTable oldA l3Pa == lookupRadixTable newA l3Pa && (lookupRadixTable oldA l3Pa).isSome
          | _ => true
  | _, _ => false
def walkFromL2 (arena : SmmuV3RadixArena) (l2Pa iova : Nat) : Option (Nat × Nat × IoPerm) := do
  let tbl2 ← lookupRadixTable arena l2Pa
  let d2 ← tbl2[(iova / hugeBlock2MiB) % 512]?
  let step2 ← decodeStage2L2Desc d2
  match step2 with
  | .inr (blockOa, perm) => some (blockOa + iova % hugeBlock2MiB, hugeBlock2MiB, perm)
  | .inl l3Pa =>
    let tbl3 ← lookupRadixTable arena l3Pa
    let d3 ← tbl3[(iova / pageSize) % 512]?
    let (pageOa, perm) ← decodeStage2L3Desc d3
    some (pageOa + iova % pageSize, pageSize, perm)
def walkBranchStep (arena : SmmuV3RadixArena) (winSize : Nat)
    (walkChild : Nat → Nat → Option (Nat × Nat × IoPerm)) (tblPa iova : Nat) : Option (Nat × Nat × IoPerm) := do
  let tbl ← lookupRadixTable arena tblPa
  let d ← tbl[(iova / winSize) % 512]?
  let childPa ← decodeStage2TableDesc d
  walkChild childPa iova
def walkFromL1 (arena : SmmuV3RadixArena) (l1Pa iova : Nat) : Option (Nat × Nat × IoPerm) :=
  walkBranchStep arena l1WinSize (walkFromL2 arena) l1Pa iova
def walkSmmuV3RadixIova (arena : SmmuV3RadixArena) (l0Pa iova : Nat) : Option (Nat × Nat × IoPerm) :=
  walkBranchStep arena l0WinSize (walkFromL1 arena) l0Pa iova
def checkContigPages (arena : SmmuV3RadixArena) (l0Pa pa₀ : Nat) (perm₀ : IoPerm)
    (iova nextPage : Nat) : Nat → Bool
  | 0 => true
  | count + 1 =>
    let pageIova := nextPage * pageSize
    match walkSmmuV3RadixIova arena l0Pa pageIova with
    | none => false
    | some (paK, _, permK) =>
      (paK == pa₀ + (pageIova - iova)) && (permK == perm₀) &&
        checkContigPages arena l0Pa pa₀ perm₀ iova (nextPage + 1) count
def walkSmmuV3Stage2Detail (arena : SmmuV3RadixArena) (sid : StreamId)
    (iova len : Nat) (acc : DmaAccess) : Except SmmuDmaFault (Nat × UInt16 × PageGranule × IoPerm) :=
  if !arena.smmuEnabled then .error .bypassModeDisabled
  else if sid == 0 || sid == wildcardStreamId then .error (.invalidStreamId sid)
  else if len == 0 then .error (.zeroOrUnmappedIova sid iova len)
  else match decodeArenaStreamRoot arena sid with
    | none => .error (.faultOnUnmappedStream sid)
    | some (vmid, s2ttbPa) =>
      if !decide (iova + len ≤ smmuAddrLimit48) then .error (.zeroOrUnmappedIova sid iova len)
      else match walkSmmuV3RadixIova arena s2ttbPa.toNat iova with
        | none => .error (.zeroOrUnmappedIova sid iova len)
        | some (pa₀, granBytes, perm₀) =>
          let firstPage := iova / pageSize
          let extraPages := (iova + len - 1) / pageSize - firstPage
          if !checkContigPages arena s2ttbPa.toNat pa₀ perm₀ iova (firstPage + 1) extraPages then
            .error (.zeroOrUnmappedIova sid iova len)
          else if perm₀.permits acc then
            let gran := if granBytes == hugeBlock2MiB then PageGranule.huge2MiB else .page4KiB
            .ok (pa₀, vmid, gran, perm₀)
          else .error (.permissionFault sid acc perm₀)
def walkSmmuV3Stage2 (arena : SmmuV3RadixArena) (sid : StreamId)
    (iova len : Nat) (acc : DmaAccess) : Except SmmuDmaFault Nat :=
  match walkSmmuV3Stage2Detail arena sid iova len acc with
  | .ok (pa, _, _, _) => .ok pa | .error e => .error e
def TblAppend (a b : Array (Array UInt64)) : Prop :=
  a.size ≤ b.size ∧ ∀ j (hj : j < a.size), b[j]? = some a[j]
private theorem tblAppend_refl (a : Array (Array UInt64)) : TblAppend a a :=
  ⟨Nat.le_refl _, fun _ hj => Array.getElem?_eq_getElem hj⟩
private theorem tblAppend_trans {a b c : Array (Array UInt64)} (h₁ : TblAppend a b) (h₂ : TblAppend b c) : TblAppend a c := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun j hj => ?_⟩
  have hbj : j < b.size := Nat.lt_of_lt_of_le hj h₁.1
  rw [h₂.2 j hbj, Option.some.inj ((Array.getElem?_eq_getElem hbj).symm.trans (h₁.2 j hj))]
private theorem tblAppend_push (a : Array (Array UInt64)) (x : Array UInt64) : TblAppend a (a.push x) :=
  ⟨by simp, fun j hj => by rw [Array.getElem?_push, ite_eq_right_iff.mpr (fun h => absurd h (by omega)), Array.getElem?_eq_getElem hj]⟩
private theorem lookupRadixTable_alloc {arena : SmmuV3RadixArena} {st : Array (Array UInt64)}
    {entries : Array UInt64} (hSz : entries.size = 512) (hBaseAlign : arena.arenaBase.toNat % pageSize = 0)
    (hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48)
    (hApp : TblAppend (allocRadixTable arena.arenaBase.toNat arena.streamTableFrames st entries).2 arena.tables) :
    let pa := (allocRadixTable arena.arenaBase.toNat arena.streamTableFrames st entries).1
    pa.toNat < smmuAddrLimit48 ∧ pa.toNat % pageSize = 0 ∧ lookupRadixTable arena pa.toNat = some entries := by
  dsimp only [allocRadixTable] at hApp ⊢
  have hIdxLt : st.size < arena.tables.size := by have := hApp.1; simp at this; omega
  have hPaLt : arena.arenaBase.toNat + (arena.streamTableFrames + st.size) * pageSize < smmuAddrLimit48 := by
    dsimp only [pageSize, smmuAddrLimit48] at *; omega
  have hToNat : (UInt64.ofNat (arena.arenaBase.toNat + (arena.streamTableFrames + st.size) * pageSize)).toNat =
      arena.arenaBase.toNat + (arena.streamTableFrames + st.size) * pageSize :=
    u64_toNat_of_lt (by dsimp only [smmuAddrLimit48] at hPaLt; omega)
  refine ⟨by rw [hToNat]; exact hPaLt, by rw [hToNat]; dsimp only [pageSize] at *; omega, ?_⟩
  dsimp only [lookupRadixTable]; rw [hToNat]
  have hNotLt : ¬ (arena.arenaBase.toNat + (arena.streamTableFrames + st.size) * pageSize <
      arena.arenaBase.toNat + arena.streamTableFrames * pageSize) := by dsimp only [pageSize]; omega
  have hSub : arena.arenaBase.toNat + (arena.streamTableFrames + st.size) * pageSize -
      (arena.arenaBase.toNat + arena.streamTableFrames * pageSize) = st.size * pageSize := by dsimp only [pageSize]; omega
  have hDiv : (st.size * pageSize) / pageSize = st.size := Nat.mul_div_cancel _ (by dsimp only [pageSize]; decide)
  have hGet := hApp.2 st.size (by simp)
  rw [Array.getElem_push_eq] at hGet
  simp [hNotLt, hSub, hDiv, hGet, hSz, pageSize, Nat.mul_mod_left]
private theorem mapAllocAux_len (f : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64)) (i k : Nat) (st : Array (Array UInt64)) :
    (mapAllocAux f i k st).1.length = k := by
  induction k generalizing i st with
  | zero => rfl
  | succ k ih => simp [mapAllocAux, ih (i + 1) (f i st).2]
private theorem mapAllocAux_spec {f : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64)}
    {Post : Nat → UInt64 → Array (Array UInt64) → Prop}
    (hf : ∀ idx st, TblAppend st (f idx st).2 ∧ ∀ fin, TblAppend (f idx st).2 fin → Post idx (f idx st).1 fin)
    (i k : Nat) (st : Array (Array UInt64)) :
    TblAppend st (mapAllocAux f i k st).2 ∧
      ∀ (off : Nat) (hoff : off < k) fin, TblAppend (mapAllocAux f i k st).2 fin →
        Post (i + off) ((mapAllocAux f i k st).1[off]'(by rw [mapAllocAux_len]; exact hoff)) fin := by
  induction k generalizing i st with
  | zero => exact ⟨tblAppend_refl st, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨hApp₂, hPostRest⟩ := ih (i + 1) (f i st).2; obtain ⟨hApp₁, hPost₀⟩ := hf i st
    refine ⟨tblAppend_trans hApp₁ hApp₂, fun off hoff fin hFin => ?_⟩
    cases off with
    | zero => simp only [mapAllocAux, Nat.add_zero, List.getElem_cons_zero]; exact hPost₀ fin (tblAppend_trans hApp₂ hFin)
    | succ off' =>
      simp only [mapAllocAux, List.getElem_cons_succ]
      rw [show i + (off' + 1) = (i + 1) + off' by omega]; exact hPostRest off' (by omega) fin hFin
private theorem mapAllocAux_spec0 {f : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64)}
    {Post : Nat → UInt64 → Array (Array UInt64) → Prop}
    (hf : ∀ idx st, TblAppend st (f idx st).2 ∧ ∀ fin, TblAppend (f idx st).2 fin → Post idx (f idx st).1 fin)
    (k : Nat) (st : Array (Array UInt64)) :
    TblAppend st (mapAllocAux f 0 k st).2 ∧ ∀ (off : Nat) (hoff : off < k) fin, TblAppend (mapAllocAux f 0 k st).2 fin →
      Post off ((mapAllocAux f 0 k st).1[off]'(by rw [mapAllocAux_len]; exact hoff)) fin := by
  obtain ⟨h1, h2⟩ := mapAllocAux_spec hf 0 k st
  exact ⟨h1, fun off hoff fin hFin => by have hp := h2 off hoff fin hFin; rwa [Nat.zero_add] at hp⟩
theorem radix_step_base (iova shift : Nat) :
    (iova / (512 * shift)) * (512 * shift) + ((iova / shift) % 512) * shift = (iova / shift) * shift := by
  have h1 : iova / (512 * shift) = (iova / shift) / 512 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [h1]; have h2 := Nat.div_add_mod (iova / shift) 512
  calc ((iova / shift) / 512) * (512 * shift) + ((iova / shift) % 512) * shift
      = (512 * ((iova / shift) / 512) + (iova / shift) % 512) * shift := by rw [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_comm ((iova / shift) / 512) 512]
    _ = (iova / shift) * shift := by rw [h2]
def specLeafAt (regs : List Stage2DmaRegion) (iova : Nat) : Option (Nat × Nat × IoPerm) :=
  match regs.find? (fun r => regionCovers2M r ((iova / hugeBlock2MiB) * hugeBlock2MiB)) with
  | some r =>
    some (r.paddr.toNat + ((iova / hugeBlock2MiB) * hugeBlock2MiB - r.iova.toNat) + iova % hugeBlock2MiB, hugeBlock2MiB, r.perm)
  | none =>
    if regionsTouchWindow regs ((iova / hugeBlock2MiB) * hugeBlock2MiB) hugeBlock2MiB then
      match regs.find? (fun r => regionCovers4K r ((iova / pageSize) * pageSize)) with
      | none => none
      | some r => some (r.paddr.toNat + ((iova / pageSize) * pageSize - r.iova.toNat) + iova % pageSize, pageSize, r.perm)
    else none
private theorem walk_buildL3_entry {m : SmmuManifest} {regs : List Stage2DmaRegion}
    (hRegs : ∀ r ∈ regs, regionAlignedInPoolB m r = true)
    {blockIova : Nat} (hBlkAl : blockIova % pageSize = 0) (i3 : Fin 512) :
    decodeStage2L3Desc ((buildL3Entries regs blockIova)[i3.val]'(by simp [buildL3Entries])) =
      (regs.find? (fun r => regionCovers4K r (blockIova + i3.val * pageSize))).map fun r =>
        (r.paddr.toNat + ((blockIova + i3.val * pageSize) - r.iova.toNat), r.perm) := by
  simp only [buildL3Entries, Array.getElem_ofFn]
  cases hf : regs.find? (fun r => regionCovers4K r (blockIova + i3.val * pageSize)) with
  | none => rfl
  | some r =>
    obtain ⟨hMem, hrCov⟩ := find_some_mem_pred hf
    have hrAl := hRegs r hMem
    simp only [regionCovers4K, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrCov
    simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hrCov.1, PageGranule.byteSize] at hrAl
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hrP48⟩, hrIA⟩, hrPA⟩, _⟩, _⟩ := hrAl
    obtain ⟨_, hrLo, hrHi⟩ := hrCov
    have hToNat : (UInt64.ofNat (r.paddr.toNat + ((blockIova + i3.val * pageSize) - r.iova.toNat))).toNat =
        r.paddr.toNat + ((blockIova + i3.val * pageSize) - r.iova.toNat) :=
      u64_toNat_of_lt (by dsimp only [smmuAddrLimit48, pageSize] at *; omega)
    rw [decodeStage2L3Desc_encodePage4K
      (by rw [hToNat]; dsimp only [smmuAddrLimit48, pageSize] at *; omega)
      (by rw [hToNat]; dsimp only [pageSize] at *; omega), hToNat]; rfl
private theorem buildL2Table_walk {m : SmmuManifest} {arena : SmmuV3RadixArena}
    {regs : List Stage2DmaRegion} (hRegs : ∀ r ∈ regs, regionAlignedInPoolB m r = true)
    (hBaseAlign : arena.arenaBase.toNat % pageSize = 0)
    (hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48)
    {base1G : Nat} (hB1G : base1G % hugeBlock2MiB = 0) (st : Array (Array UInt64)) :
    let out := buildL2Table arena.arenaBase.toNat arena.streamTableFrames regs base1G st
    TblAppend st out.2 ∧ (TblAppend out.2 arena.tables →
      out.1.toNat < smmuAddrLimit48 ∧ out.1.toNat % pageSize = 0 ∧
      ∀ iova, (iova / l1WinSize) * l1WinSize = base1G → walkFromL2 arena out.1.toNat iova = specLeafAt regs iova) := by
  unfold buildL2Table
  have hMap := mapAllocAux_spec0 (f := buildL2Step arena.arenaBase.toNat arena.streamTableFrames regs base1G)
    (Post := fun i2 d2 fin => fin = arena.tables → ∀ iova, (iova / hugeBlock2MiB) * hugeBlock2MiB = base1G + i2 * hugeBlock2MiB →
      (do let step2 ← decodeStage2L2Desc d2
          match step2 with
          | .inr (blockOa, perm) => some (blockOa + iova % hugeBlock2MiB, hugeBlock2MiB, perm)
          | .inl l3Pa =>
            let tbl3 ← lookupRadixTable arena l3Pa
            let d3 ← tbl3[(iova / pageSize) % 512]?
            let (pageOa, perm) ← decodeStage2L3Desc d3
            some (pageOa + iova % pageSize, pageSize, perm)) = specLeafAt regs iova)
    (fun i2 s => by
      dsimp only [buildL2Step]
      cases hf2m : regs.find? (fun r => regionCovers2M r (base1G + i2 * hugeBlock2MiB)) with
      | some r =>
        refine ⟨tblAppend_refl s, fun _ _ _ iova hBlkEq => ?_⟩
        obtain ⟨hMem, hrCov⟩ := find_some_mem_pred hf2m
        have hrAl := hRegs r hMem
        simp only [regionCovers2M, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrCov
        simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hrCov.1, PageGranule.byteSize] at hrAl
        obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hrP48⟩, hrIA⟩, hrPA⟩, _⟩, _⟩ := hrAl
        obtain ⟨_, hrLo, hrHi⟩ := hrCov
        have hToNat : (UInt64.ofNat (r.paddr.toNat + ((base1G + i2 * hugeBlock2MiB) - r.iova.toNat))).toNat =
            r.paddr.toNat + ((base1G + i2 * hugeBlock2MiB) - r.iova.toNat) :=
          u64_toNat_of_lt (by simp only [smmuAddrLimit48, hugeBlock2MiB] at hrP48 hrLo hrHi ⊢; omega)
        rw [decodeStage2L2Desc_encodeBlock2M
          (by rw [hToNat]; simp only [smmuAddrLimit48, hugeBlock2MiB] at hrP48 hrLo hrHi ⊢; omega)
          (by rw [hToNat]; simp only [hugeBlock2MiB] at hB1G hrIA hrPA hrLo ⊢; omega), hToNat]
        dsimp only [specLeafAt, Bind.bind, Option.bind]; rw [hBlkEq, hf2m]
      | none =>
        cases htw : regionsTouchWindow regs (base1G + i2 * hugeBlock2MiB) hugeBlock2MiB
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨tblAppend_refl s, fun _ _ _ iova hBlkEq => ?_⟩
          have hDec0 : decodeStage2L2Desc 0 = none := rfl
          dsimp only [specLeafAt, Bind.bind, Option.bind]; rw [hDec0, hBlkEq, hf2m, htw]; rfl
        · simp only [↓reduceIte]
          refine ⟨tblAppend_push _ _, fun fin hAppFin hFinEq iova hBlkEq => ?_⟩
          subst hFinEq
          have hL3Sz : (buildL3Entries regs (base1G + i2 * hugeBlock2MiB)).size = 512 := by simp [buildL3Entries]
          obtain ⟨hL3Lt, hL3Al, hL3Look⟩ := lookupRadixTable_alloc hL3Sz hBaseAlign hArena48 hAppFin
          rw [decodeStage2L2Desc_encodeTable hL3Lt hL3Al]
          dsimp only [Bind.bind, Option.bind]; rw [hL3Look]; dsimp only []
          have hi3Lt : (iova / pageSize) % 512 < 512 := Nat.mod_lt _ (by decide)
          rw [Array.getElem?_eq_getElem (by rw [hL3Sz]; exact hi3Lt)]; dsimp only []
          have hBlk4K : (base1G + i2 * hugeBlock2MiB) % pageSize = 0 := by simp only [hugeBlock2MiB, pageSize] at hB1G ⊢; omega
          rw [walk_buildL3_entry hRegs hBlk4K ⟨(iova / pageSize) % 512, hi3Lt⟩]
          have hPageEq : (base1G + i2 * hugeBlock2MiB) + ((iova / pageSize) % 512) * pageSize =
              (iova / pageSize) * pageSize := by
            have hStep := radix_step_base iova pageSize
            have hMul : 512 * pageSize = hugeBlock2MiB := by decide
            rw [hMul, hBlkEq] at hStep; exact hStep
          dsimp only [specLeafAt]; rw [hBlkEq, hf2m, htw, hPageEq]; simp only [↓reduceIte]
          cases regs.find? (fun r => regionCovers4K r ((iova / pageSize) * pageSize)) <;> rfl) 512 st
  have hDsLen : (Array.mk (mapAllocAux (buildL2Step arena.arenaBase.toNat arena.streamTableFrames regs base1G) 0 512 st).1).size = 512 :=
    mapAllocAux_len _ 0 512 st
  refine ⟨tblAppend_trans hMap.1 (tblAppend_push _ _), fun hAppTop => ?_⟩
  obtain ⟨hPaLt, hPaAl, hLook⟩ := lookupRadixTable_alloc hDsLen hBaseAlign hArena48 hAppTop
  refine ⟨hPaLt, hPaAl, fun iova hWin1G => ?_⟩
  unfold walkFromL2; dsimp only [Bind.bind, Option.bind]; rw [hLook]; dsimp only []
  have hi2Lt : (iova / hugeBlock2MiB) % 512 < 512 := Nat.mod_lt _ (by decide)
  rw [Array.getElem?_eq_getElem (by rw [hDsLen]; exact hi2Lt)]; dsimp only []
  have hBlkEq : (iova / hugeBlock2MiB) * hugeBlock2MiB = base1G + ((iova / hugeBlock2MiB) % 512) * hugeBlock2MiB := by
    have hStep := (radix_step_base iova hugeBlock2MiB).symm
    have hMul : 512 * hugeBlock2MiB = l1WinSize := by decide
    rw [hMul, hWin1G] at hStep; exact hStep
  exact hMap.2 _ hi2Lt arena.tables (tblAppend_trans (tblAppend_push _ _) hAppTop) rfl iova hBlkEq
private theorem buildBranchTable_walk {arena : SmmuV3RadixArena} {regs : List Stage2DmaRegion}
    (hBaseAlign : arena.arenaBase.toNat % pageSize = 0)
    (hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48)
    {base winSize : Nat} {buildChild : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64)}
    {walkChild : Nat → Nat → Option (Nat × Nat × IoPerm)} {childSpec : Nat → Option (Nat × Nat × IoPerm)}
    (hChild : ∀ idx s,
      let out := buildChild (base + idx * winSize) s
      TblAppend s out.2 ∧ (TblAppend out.2 arena.tables →
        out.1.toNat < smmuAddrLimit48 ∧ out.1.toNat % pageSize = 0 ∧
        ∀ iova, (iova / winSize) * winSize = base + idx * winSize → walkChild out.1.toNat iova = childSpec iova))
    (st : Array (Array UInt64)) :
    let out := buildBranchTable arena.arenaBase.toNat arena.streamTableFrames regs base winSize buildChild st
    TblAppend st out.2 ∧ (TblAppend out.2 arena.tables →
      out.1.toNat < smmuAddrLimit48 ∧ out.1.toNat % pageSize = 0 ∧
      ∀ iova, (iova / (512 * winSize)) * (512 * winSize) = base →
        walkBranchStep arena winSize walkChild out.1.toNat iova =
          if regionsTouchWindow regs ((iova / winSize) * winSize) winSize then childSpec iova else none) := by
  unfold buildBranchTable
  have hMap := mapAllocAux_spec0 (f := buildBranchStepFn regs base winSize buildChild)
    (Post := fun idx d fin => fin = arena.tables → ∀ iova, (iova / winSize) * winSize = base + idx * winSize →
      (do let cPa ← decodeStage2TableDesc d; walkChild cPa iova) =
        if regionsTouchWindow regs (base + idx * winSize) winSize then childSpec iova else none)
    (fun idx s => by
      dsimp only [buildBranchStepFn]
      cases htw : regionsTouchWindow regs (base + idx * winSize) winSize
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨tblAppend_refl s, fun _ _ _ _ _ => rfl⟩
      · simp only [↓reduceIte]
        obtain ⟨hAppC, hWC⟩ := hChild idx s
        refine ⟨hAppC, fun fin hFin hEq iova hWinEq => ?_⟩
        subst hEq; obtain ⟨hPaLt, hPaAl, hW⟩ := hWC hFin
        rw [decodeStage2TableDesc_encode hPaLt hPaAl]; exact hW iova hWinEq) 512 st
  have hDsLen : (Array.mk (mapAllocAux (buildBranchStepFn regs base winSize buildChild) 0 512 st).1).size = 512 :=
    mapAllocAux_len _ 0 512 st
  refine ⟨tblAppend_trans hMap.1 (tblAppend_push _ _), fun hAppTop => ?_⟩
  obtain ⟨hPaLt, hPaAl, hLook⟩ := lookupRadixTable_alloc hDsLen hBaseAlign hArena48 hAppTop
  refine ⟨hPaLt, hPaAl, fun iova hParent => ?_⟩
  unfold walkBranchStep; dsimp only [Bind.bind, Option.bind]; rw [hLook]; dsimp only []
  have hiLt : (iova / winSize) % 512 < 512 := Nat.mod_lt _ (by decide)
  rw [Array.getElem?_eq_getElem (by rw [hDsLen]; exact hiLt)]; dsimp only []
  have hWinEq : (iova / winSize) * winSize = base + ((iova / winSize) % 512) * winSize := by
    rw [← hParent]; exact (radix_step_base iova winSize).symm
  have hRes := hMap.2 _ hiLt arena.tables (tblAppend_trans (tblAppend_push _ _) hAppTop) rfl iova hWinEq
  rw [← hWinEq] at hRes; exact hRes
private theorem buildL0Table_walk {m : SmmuManifest} {arena : SmmuV3RadixArena}
    {regs : List Stage2DmaRegion} (hRegs : ∀ r ∈ regs, regionAlignedInPoolB m r = true)
    (hBaseAlign : arena.arenaBase.toNat % pageSize = 0)
    (hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48)
    (st : Array (Array UInt64)) :
    let out := buildL0Table arena.arenaBase.toNat arena.streamTableFrames regs st
    TblAppend st out.2 ∧ (TblAppend out.2 arena.tables →
      out.1.toNat < smmuAddrLimit48 ∧ out.1.toNat % pageSize = 0 ∧
      ∀ iova, iova < smmuAddrLimit48 →
        walkSmmuV3RadixIova arena out.1.toNat iova =
          if regionsTouchWindow regs ((iova / l0WinSize) * l0WinSize) l0WinSize &&
              regionsTouchWindow regs ((iova / l1WinSize) * l1WinSize) l1WinSize then specLeafAt regs iova else none) := by
  unfold buildL0Table
  have hMul1 : 512 * l1WinSize = l0WinSize := by decide
  have hMul0 : 512 * l0WinSize = smmuAddrLimit48 := by decide
  have hB0 := buildBranchTable_walk (arena := arena) (regs := regs) hBaseAlign hArena48
    (base := 0) (winSize := l0WinSize)
    (buildChild := buildL1Table arena.arenaBase.toNat arena.streamTableFrames regs)
    (walkChild := walkFromL1 arena)
    (childSpec := fun iova => if regionsTouchWindow regs ((iova / l1WinSize) * l1WinSize) l1WinSize then specLeafAt regs iova else none)
    (fun i0 s0 => by
      unfold buildL1Table walkFromL1
      have hB1 := buildBranchTable_walk (arena := arena) (regs := regs) hBaseAlign hArena48
        (base := 0 + i0 * l0WinSize) (winSize := l1WinSize)
        (buildChild := buildL2Table arena.arenaBase.toNat arena.streamTableFrames regs)
        (walkChild := walkFromL2 arena) (childSpec := specLeafAt regs)
        (fun i1 s1 => buildL2Table_walk hRegs hBaseAlign hArena48
          (by simp only [l0WinSize, l1WinSize, hugeBlock2MiB]; omega) s1) s0
      exact ⟨hB1.1, fun hFin => by
        obtain ⟨h1, h2, h3⟩ := hB1.2 hFin
        exact ⟨h1, h2, fun iova hw => h3 iova (by rw [hMul1]; exact hw)⟩⟩) st
  refine ⟨hB0.1, fun hFin => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hB0.2 hFin
  refine ⟨h1, h2, fun iova hLt48 => ?_⟩
  unfold walkSmmuV3RadixIova
  rw [h3 iova (by rw [hMul0, Nat.div_eq_of_lt hLt48, Nat.zero_mul])]
  cases regionsTouchWindow regs ((iova / l0WinSize) * l0WinSize) l0WinSize <;>
    simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
theorem foldl_max_sid_le (pts : List Stage2IoPageTable) (acc : Nat) :
    ∀ pt ∈ pts, pt.streamId.toNat ≤ pts.foldl (fun a p => max a p.streamId.toNat) acc := by
  induction pts generalizing acc with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro pt hpt; simp only [List.foldl_cons]
    rcases List.mem_cons.mp hpt with rfl | htl
    · have hMono : ∀ (ys : List Stage2IoPageTable) (b : Nat), b ≤ ys.foldl (fun a p => max a p.streamId.toNat) b := by
        intro ys; induction ys with
        | nil => intro b; exact Nat.le_refl b
        | cons _ _ ihy => intro b; exact Nat.le_trans (Nat.le_max_left _ _) (ihy _)
      exact Nat.le_trans (Nat.le_max_right _ _) (hMono xs _)
    · exact ih _ pt htl
private theorem compileStreamRoots_spec {m : SmmuManifest} {arena : SmmuV3RadixArena}
    (hBaseAlign : arena.arenaBase.toNat % pageSize = 0)
    (hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48)
    (pts : List Stage2IoPageTable) (st : Array (Array UInt64))
    (hAll : ∀ pt ∈ pts, pt.streamId ≠ 0 ∧ pt.streamId.toNat < 4096 ∧ ∀ r ∈ pt.regions, regionAlignedInPoolB m r = true) :
    let out := compileStreamRoots arena.arenaBase.toNat arena.streamTableFrames pts st
    TblAppend st out.2 ∧ (TblAppend out.2 arena.tables →
      ∀ sid : StreamId,
        match lookupStream pts sid with
        | none => out.1.find? (fun x => x.1.toNat == sid.toNat) = none
        | some pt =>
          ∃ l0Pa, out.1.find? (fun x => x.1.toNat == sid.toNat) = some (sid, UInt16.ofNat sid.toNat, l0Pa) ∧
            0 < (UInt16.ofNat sid.toNat).toNat ∧ l0Pa.toNat < smmuAddrLimit48 ∧ l0Pa.toNat % pageSize = 0 ∧
            ∀ iova, iova < smmuAddrLimit48 →
              walkSmmuV3RadixIova arena l0Pa.toNat iova =
                if regionsTouchWindow pt.regions ((iova / l0WinSize) * l0WinSize) l0WinSize &&
                    regionsTouchWindow pt.regions ((iova / l1WinSize) * l1WinSize) l1WinSize then
                  specLeafAt pt.regions iova else none) := by
  induction pts generalizing st with
  | nil => exact ⟨tblAppend_refl st, fun _ _ => by simp [compileStreamRoots, lookupStream]⟩
  | cons pt pts ih =>
    obtain ⟨hNe0, hLt4k, hRegs⟩ := hAll pt List.mem_cons_self
    obtain ⟨hApp0, hWalk0⟩ := buildL0Table_walk hRegs hBaseAlign hArena48 st
    obtain ⟨hAppR, hSpecR⟩ := ih _ (fun p hp => hAll p (List.mem_cons_of_mem _ hp))
    refine ⟨tblAppend_trans hApp0 hAppR, fun hFin sid => ?_⟩
    unfold compileStreamRoots lookupStream; simp only [List.find?_cons]
    by_cases hEq : pt.streamId == sid
    · have hSidEq : pt.streamId = sid := beq_iff_eq.mp hEq
      have hNatEq : (pt.streamId.toNat == sid.toNat) = true := by simp [hSidEq]
      rw [hEq, hNatEq]
      obtain ⟨hPaLt, hPaAl, hW⟩ := hWalk0 (tblAppend_trans hAppR hFin)
      have hvPos : 0 < (UInt16.ofNat sid.toNat).toNat := by
        subst hSidEq
        have hSidPos : 0 < pt.streamId.toNat := Nat.pos_of_ne_zero (fun h0 => hNe0 (UInt32.toNat_inj.mp h0))
        rw [u16_toNat_of_lt (Nat.lt_trans hLt4k (by decide))]; exact hSidPos
      exact ⟨_, by simp [hSidEq], hvPos, hPaLt, hPaAl, hW⟩
    · have hNatNe : (pt.streamId.toNat == sid.toNat) = false := by
        cases hN : (pt.streamId.toNat == sid.toNat); · rfl
        exact absurd (beq_iff_eq.mpr (UInt32.toNat_inj.mp (beq_iff_eq.mp hN))) hEq
      have hEqF : (pt.streamId == sid) = false := Bool.eq_false_iff.mpr hEq
      rw [hEqF, hNatNe]; exact hSpecR hFin sid
private theorem decodeSmmuV3Ste_abort : decodeSmmuV3Ste SmmuV3Ste.abort = some .abort := by
  unfold decodeSmmuV3Ste; have h0 : (SmmuV3Ste.abort.w0.toNat % 2 == 0) = true := rfl
  rw [h0, beq_self_eq_true SmmuV3Ste.abort]; rfl
private theorem decodeArenaStreamRoot_mkStreamTable {n : Nat} (roots : List (StreamId × UInt16 × UInt64))
    (arena : SmmuV3RadixArena)
    (hArr : arena.streamTable = Array.ofFn fun (i : Fin n) => mkStreamTableSte roots i.val) (sid : StreamId) :
    decodeArenaStreamRoot arena sid = if sid.toNat < n then
      match decodeSmmuV3Ste (mkStreamTableSte roots sid.toNat) with
      | some (.stage2 vmid l0Pa) => some (vmid, l0Pa) | _ => none
    else none := by
  unfold decodeArenaStreamRoot; rw [hArr]; by_cases h : sid.toNat < n
  · simp only [h, ↓reduceIte]; rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]; rfl
  · simp only [h, ↓reduceIte]; rw [Array.getElem?_eq_none (by rw [Array.size_ofFn]; exact Nat.le_of_not_lt h)]; rfl
private theorem mkStreamTableSte_none {roots : List (StreamId × UInt16 × UInt64)} {k : Nat}
    (h : roots.find? (fun r => r.1.toNat == k) = none) :
    decodeSmmuV3Ste (mkStreamTableSte roots k) = some .abort := by
  unfold mkStreamTableSte; rw [h]; exact decodeSmmuV3Ste_abort
private theorem mkStreamTableSte_some {roots : List (StreamId × UInt16 × UInt64)} {k : Nat}
    {s : StreamId} {vmid : UInt16} {l0Pa : UInt64}
    (h : roots.find? (fun r => r.1.toNat == k) = some (s, vmid, l0Pa))
    (hv : 0 < vmid.toNat) (hLt : l0Pa.toNat < smmuAddrLimit48) (hAl : l0Pa.toNat % pageSize = 0) :
    decodeSmmuV3Ste (mkStreamTableSte roots k) = some (.stage2 vmid l0Pa) := by
  unfold mkStreamTableSte; rw [h]; exact decodeSmmuV3Ste_packStage2 hv hLt hAl
theorem compileManifestToRadixArena_unpack {m : SmmuManifest} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hComp : compileManifestToRadixArena m arenaBase maxFrames = .ok arena) :
    m.arch = .armSmmuV3 ∧ m.defaultDeny = true ∧ streamsNoWildcardB m = true ∧ streamsAlignedInPoolB m = true ∧
    arenaBase.toNat % (nextSteCountPow2 (maxManifestSid m.streams + 1) * 64) = 0 ∧
    arenaBase.toNat % pageSize = 0 ∧ 0 < maxFrames ∧ arenaBase.toNat + maxFrames * pageSize ≤ smmuAddrLimit48 ∧
    arenaProtectedByKernelPtB m arenaBase maxFrames = true ∧ maxManifestSid m.streams < 4096 ∧
    arena.smmuEnabled = true ∧ arena.arenaBase = arenaBase ∧ arena.streamTableFrames + arena.tables.size ≤ maxFrames ∧
    streamsNonCoalescableB m = true ∧
    let tableCount := nextSteCountPow2 (maxManifestSid m.streams + 1); let stFrames := (tableCount * 64) / pageSize + 1
    let compiled := compileStreamRoots arenaBase.toNat stFrames m.streams #[]
    arena.streamTableFrames = stFrames ∧ arena.tables = compiled.2 ∧
    arena.streamTable = Array.ofFn fun (sid : Fin tableCount) => mkStreamTableSte compiled.1 sid.val := by
  unfold compileManifestToRadixArena at hComp; split at hComp; · cases hComp
  rename_i h0; cases h1 : m.defaultDeny; · simp [h1] at hComp
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hComp
  cases h2a : streamsNoWildcardB m; · simp [h2a] at hComp
  cases h2b : streamsAlignedInPoolB m; · simp [h2a, h2b] at hComp
  cases h2c : streamsNonCoalescableB m; · simp [h2a, h2b, h2c] at hComp
  simp only [h2a, h2b, h2c, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hComp
  split at hComp; · cases hComp
  rename_i hSidLt; split at hComp; · cases hComp
  rename_i h3; cases h4 : arenaProtectedByKernelPtB m arenaBase maxFrames; · simp [h4] at hComp
  simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hComp
  split at hComp; · cases hComp
  rename_i h6; cases hComp; have hArchEq : m.arch = .armSmmuV3 := by simpa [bne_iff_ne] using h0
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt, Nat.not_le] at hSidLt h3 h6
  exact ⟨hArchEq, rfl, rfl, rfl, Classical.not_not.mp h3.1.1.1, Classical.not_not.mp h3.1.1.2,
    Nat.pos_of_ne_zero h3.1.2, h3.2, rfl, hSidLt, rfl, rfl, h6, rfl, rfl, rfl, rfl⟩
theorem compiledArena_root_and_walk {m : SmmuManifest} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hComp : compileManifestToRadixArena m arenaBase maxFrames = .ok arena) (sid : StreamId) :
    match lookupStream m.streams sid with
    | none => decodeArenaStreamRoot arena sid = none
    | some pt =>
      ∃ l0Pa, decodeArenaStreamRoot arena sid = some (UInt16.ofNat sid.toNat, l0Pa) ∧
        ∀ iova, iova < smmuAddrLimit48 →
          walkSmmuV3RadixIova arena l0Pa.toNat iova =
            if regionsTouchWindow pt.regions ((iova / l0WinSize) * l0WinSize) l0WinSize &&
                regionsTouchWindow pt.regions ((iova / l1WinSize) * l1WinSize) l1WinSize then
              specLeafAt pt.regions iova else none := by
  obtain ⟨_, _, hNoWild, hAlPool, _, hBaseAl, _, hMax48, _, hMaxSid, _, hAbEq, hCap, _,
    hStFrEq, hTblEq, hStArr⟩ := compileManifestToRadixArena_unpack hComp
  have hArena48 : arena.arenaBase.toNat + (arena.streamTableFrames + arena.tables.size) * pageSize ≤ smmuAddrLimit48 :=
    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right pageSize hCap) _) (hAbEq ▸ hMax48)
  have hAllPts : ∀ pt ∈ m.streams, pt.streamId ≠ 0 ∧ pt.streamId.toNat < 4096 ∧
      ∀ r ∈ pt.regions, regionAlignedInPoolB m r = true := fun pt hpt => by
    have hnw := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hNoWild).2 pt hpt
    have hal := List.all_eq_true.mp hAlPool pt hpt
    exact ⟨bne_iff_ne.mp ((Bool.and_eq_true _ _).mp hnw).1,
      Nat.lt_of_le_of_lt (foldl_max_sid_le m.streams 0 pt hpt) hMaxSid,
      fun r hr => List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hal).2 r hr⟩
  have hRoots := (compileStreamRoots_spec (m := m) (arena := arena)
    (by rw [hAbEq]; exact hBaseAl) hArena48 m.streams #[] hAllPts).2
    (by rw [hTblEq, ← hStFrEq, hAbEq]; exact tblAppend_refl _) sid
  have hFindEq : (compileStreamRoots arena.arenaBase.toNat arena.streamTableFrames m.streams #[]).1.find? (fun x => x.1.toNat == sid.toNat) =
      (compileStreamRoots arenaBase.toNat ((nextSteCountPow2 (maxManifestSid m.streams + 1) * 64) / pageSize + 1) m.streams #[]).1.find? (fun x => x.1.toNat == sid.toNat) := by
    rw [hAbEq, hStFrEq]
  rw [decodeArenaStreamRoot_mkStreamTable _ arena hStArr sid]
  cases hLook : lookupStream m.streams sid with
  | none =>
    rw [hLook] at hRoots; have hNone := hFindEq.symm.trans hRoots
    by_cases hLt : sid.toNat < nextSteCountPow2 (maxManifestSid m.streams + 1)
    · simp only [hLt, ↓reduceIte]; rw [mkStreamTableSte_none hNone]
    · simp only [hLt, ↓reduceIte]
  | some pt =>
    rw [hLook] at hRoots; obtain ⟨l0Pa, hFind, hvPos, hL0Lt, hL0Al, hWalk⟩ := hRoots
    have hSome := hFindEq.symm.trans hFind; obtain ⟨hptMem, hptSid⟩ := lookupStream_some hLook
    have hLt : sid.toNat < nextSteCountPow2 (maxManifestSid m.streams + 1) := by
      rw [← hptSid]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (foldl_max_sid_le m.streams 0 pt hptMem))
        (le_nextSteCountPow2 (need := maxManifestSid m.streams + 1) hMaxSid)
    refine ⟨l0Pa, ?_, hWalk⟩
    simp only [hLt, ↓reduceIte]; rw [mkStreamTableSte_some hSome hvPos hL0Lt hL0Al]
theorem specLeafAt_iff_lookup {m : SmmuManifest} {regs : List Stage2DmaRegion}
    (hDisj : RegionsIovaDisjoint regs) (hRegs : ∀ r ∈ regs, regionAlignedInPoolB m r = true)
    {iova len : Nat} (hLenPos : 0 < len) (hPage : (iova % pageSize) + len ≤ pageSize) :
    (if regionsTouchWindow regs ((iova / l0WinSize) * l0WinSize) l0WinSize &&
        regionsTouchWindow regs ((iova / l1WinSize) * l1WinSize) l1WinSize then specLeafAt regs iova else none) =
      (lookupDmaRegion regs iova len).map fun r =>
        (r.paddr.toNat + (iova - r.iova.toNat), r.granule.byteSize, r.perm) := by
  have hDiv4K : (iova / pageSize) * pageSize + iova % pageSize = iova := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hDiv2M : (iova / hugeBlock2MiB) * hugeBlock2MiB + iova % hugeBlock2MiB = iova := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hMod2M : iova % hugeBlock2MiB < hugeBlock2MiB := Nat.mod_lt _ (by decide)
  have hBlk4K : ((iova / hugeBlock2MiB) * hugeBlock2MiB) ≤ (iova / pageSize) * pageSize ∧
      (iova / pageSize) * pageSize + pageSize ≤ (iova / hugeBlock2MiB) * hugeBlock2MiB + hugeBlock2MiB := by
    have hq := radix_step_base iova pageSize
    have hMul : 512 * pageSize = hugeBlock2MiB := by decide
    rw [hMul] at hq
    have hm : (iova / pageSize) % 512 < 512 := Nat.mod_lt _ (by decide)
    simp only [hugeBlock2MiB, pageSize] at hq hm ⊢; omega
  cases hLook : lookupDmaRegion regs iova len with
  | none =>
    simp only [Option.map_none]
    have hNoReg : ∀ r ∈ regs, ¬ (r.iova.toNat ≤ iova ∧ iova + len ≤ r.iova.toNat + r.size.toNat) :=
      fun r hr hIn => absurd (decide_eq_true hIn) (List.find?_eq_none.mp hLook r hr)
    have hNo2M : regs.find? (fun r => regionCovers2M r ((iova / hugeBlock2MiB) * hugeBlock2MiB)) = none :=
      List.find?_eq_none.mpr fun r hr hCov => by
        simp only [regionCovers2M, Bool.and_eq_true, decide_eq_true_eq] at hCov
        obtain ⟨_, hc1, hc2⟩ := hCov
        exact hNoReg r hr (by simp only [hugeBlock2MiB, pageSize] at hc1 hc2 hDiv2M hMod2M hDiv4K hPage hBlk4K ⊢; omega)
    have hNo4K : regs.find? (fun r => regionCovers4K r ((iova / pageSize) * pageSize)) = none :=
      List.find?_eq_none.mpr fun r hr hCov => by
        simp only [regionCovers4K, Bool.and_eq_true, decide_eq_true_eq] at hCov
        obtain ⟨_, hc1, hc2⟩ := hCov
        exact hNoReg r hr (by simp only [pageSize] at hc1 hc2 hDiv4K hPage ⊢; omega)
    split
    · simp only [specLeafAt, hNo2M, hNo4K, ite_self]
    · rfl
  | some reg =>
    obtain ⟨hMem, hlo, hhi⟩ := lookupDmaRegion_some hLook
    have hrAl := hRegs reg hMem
    simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrAl
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hrIA⟩, _⟩, hrSA⟩, _⟩ := hrAl
    have hDiv39 : (iova / l0WinSize) * l0WinSize + iova % l0WinSize = iova := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hMod39 : iova % l0WinSize < l0WinSize := Nat.mod_lt _ (by decide)
    have hDiv30 : (iova / l1WinSize) * l1WinSize + iova % l1WinSize = iova := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hMod30 : iova % l1WinSize < l1WinSize := Nat.mod_lt _ (by decide)
    have hTw39 : regionsTouchWindow regs ((iova / l0WinSize) * l0WinSize) l0WinSize = true :=
      List.any_eq_true.mpr ⟨reg, hMem, decide_eq_true ⟨by omega, by omega⟩⟩
    have hTw30 : regionsTouchWindow regs ((iova / l1WinSize) * l1WinSize) l1WinSize = true :=
      List.any_eq_true.mpr ⟨reg, hMem, decide_eq_true ⟨by omega, by omega⟩⟩
    rw [hTw39, hTw30]; simp only [Bool.and_self, ↓reduceIte, Option.map_some]; dsimp only [specLeafAt]
    cases hg : reg.granule with
    | huge2MiB =>
      simp only [hg, PageGranule.byteSize] at hrIA hrSA ⊢
      have hCov2M : regionCovers2M reg ((iova / hugeBlock2MiB) * hugeBlock2MiB) = true := by
        simp only [regionCovers2M, hg, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
        simp only [hugeBlock2MiB] at hDiv2M hMod2M ⊢; omega
      cases hf2 : regs.find? (fun r => regionCovers2M r ((iova / hugeBlock2MiB) * hugeBlock2MiB)) with
      | none => exact absurd hCov2M (List.find?_eq_none.mp hf2 reg hMem)
      | some r' =>
        obtain ⟨hr'Mem, hr'Cov⟩ := find_some_mem_pred hf2
        simp only [regionCovers2M, Bool.and_eq_true, decide_eq_true_eq] at hr'Cov
        obtain ⟨_, hc1, hc2⟩ := hr'Cov
        have hEqReg := hDisj r' hr'Mem reg hMem
          (by simp only [hugeBlock2MiB] at hc1 hc2 hDiv2M hMod2M; omega)
          (by simp only [hugeBlock2MiB] at hc1 hc2 hDiv2M hMod2M; omega)
        subst hEqReg
        have hAddrEq : r'.paddr.toNat + ((iova / hugeBlock2MiB) * hugeBlock2MiB - r'.iova.toNat) +
            iova % hugeBlock2MiB = r'.paddr.toNat + (iova - r'.iova.toNat) := by omega
        dsimp only []; rw [hAddrEq]; rfl
    | page4KiB =>
      simp only [hg, PageGranule.byteSize] at hrIA hrSA ⊢
      have hNo2M : regs.find? (fun r => regionCovers2M r ((iova / hugeBlock2MiB) * hugeBlock2MiB)) = none :=
        List.find?_eq_none.mpr fun r' hr' hc => by
          simp only [regionCovers2M, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          obtain ⟨hcg, hc1, hc2⟩ := hc
          have hEq := hDisj r' hr' reg hMem
            (by simp only [hugeBlock2MiB] at hc1 hc2 hDiv2M hMod2M; omega)
            (by simp only [hugeBlock2MiB] at hc1 hc2 hDiv2M hMod2M; omega)
          rw [hEq, hg] at hcg; cases hcg
      have hTw2M : regionsTouchWindow regs ((iova / hugeBlock2MiB) * hugeBlock2MiB) hugeBlock2MiB = true :=
        List.any_eq_true.mpr ⟨reg, hMem, decide_eq_true ⟨by omega, by omega⟩⟩
      have hCov4K : regionCovers4K reg ((iova / pageSize) * pageSize) = true := by
        simp only [regionCovers4K, hg, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
        simp only [pageSize] at hDiv4K hPage ⊢; omega
      rw [hNo2M, hTw2M]; simp only [↓reduceIte]
      cases hf4 : regs.find? (fun r => regionCovers4K r ((iova / pageSize) * pageSize)) with
      | none => exact absurd hCov4K (List.find?_eq_none.mp hf4 reg hMem)
      | some r' =>
        obtain ⟨hr'Mem, hr'Cov⟩ := find_some_mem_pred hf4
        simp only [regionCovers4K, Bool.and_eq_true, decide_eq_true_eq] at hr'Cov
        obtain ⟨_, hc1, hc2⟩ := hr'Cov
        have hEqReg := hDisj r' hr'Mem reg hMem
          (by simp only [pageSize] at hc1 hc2 hDiv4K hPage; omega)
          (by simp only [pageSize] at hc1 hc2 hDiv4K hPage; omega)
        subst hEqReg
        have hAddrEq : r'.paddr.toNat + ((iova / pageSize) * pageSize - r'.iova.toNat) +
            iova % pageSize = r'.paddr.toNat + (iova - r'.iova.toNat) := by omega
        dsimp only []; rw [hAddrEq]
theorem checkContigPages_at {arena : SmmuV3RadixArena} {l0Pa pa₀ : Nat} {perm₀ : IoPerm}
    {iova nextPage count : Nat}
    (hOk : checkContigPages arena l0Pa pa₀ perm₀ iova nextPage count = true) :
    ∀ {k : Nat}, k < count →
      ∃ granK, walkSmmuV3RadixIova arena l0Pa ((nextPage + k) * pageSize) =
        some (pa₀ + ((nextPage + k) * pageSize - iova), granK, perm₀) := by
  induction count generalizing nextPage with
  | zero => intro _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ count ih =>
    dsimp only [checkContigPages] at hOk
    cases hW : walkSmmuV3RadixIova arena l0Pa (nextPage * pageSize) with
    | none => rw [hW] at hOk; cases hOk
    | some val =>
      obtain ⟨paK, granK, permK⟩ := val
      rw [hW] at hOk; simp only [Bool.and_eq_true, beq_iff_eq] at hOk
      obtain ⟨⟨rfl, rfl⟩, hRest⟩ := hOk
      intro k hk
      cases k with
      | zero => rw [Nat.add_zero]; exact ⟨granK, hW⟩
      | succ k' =>
        rw [show nextPage + (k' + 1) = (nextPage + 1) + k' by omega]
        exact ih hRest (by omega)
theorem checkContigPages_of_region {m : SmmuManifest} {arena : SmmuV3RadixArena} {l0Pa : Nat}
    {regs : List Stage2DmaRegion} {reg : Stage2DmaRegion}
    (hWalk : ∀ addr, addr < smmuAddrLimit48 →
      walkSmmuV3RadixIova arena l0Pa addr =
        if regionsTouchWindow regs ((addr / l0WinSize) * l0WinSize) l0WinSize &&
            regionsTouchWindow regs ((addr / l1WinSize) * l1WinSize) l1WinSize then
          specLeafAt regs addr else none)
    (hDisj : RegionsIovaDisjoint regs) (hRegs : ∀ r ∈ regs, regionAlignedInPoolB m r = true)
    (hRegMem : reg ∈ regs) (iova : Nat) (hLo : reg.iova.toNat ≤ iova) :
    ∀ nextPage count,
      iova < nextPage * pageSize →
      (nextPage + count) * pageSize ≤ reg.iova.toNat + reg.size.toNat →
      checkContigPages arena l0Pa (reg.paddr.toNat + (iova - reg.iova.toNat)) reg.perm iova nextPage count = true := by
  intro nextPage count
  induction count generalizing nextPage with
  | zero => intros; rfl
  | succ count ih =>
    intro hGt hEnd
    have hrAl := hRegs reg hRegMem
    simp only [regionAlignedInPoolB, Bool.and_eq_true, decide_eq_true_eq] at hrAl
    obtain ⟨⟨⟨⟨⟨⟨_, hrI48⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hrAl
    have hPage48 : nextPage * pageSize + pageSize ≤ smmuAddrLimit48 :=
      Nat.le_trans (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right pageSize (by omega : nextPage + 1 ≤ nextPage + (count + 1)))
        (Nat.le_trans hEnd hrI48)
    have hPagePos : 0 < pageSize := by decide
    have hFind : lookupDmaRegion regs (nextPage * pageSize) pageSize = some reg := by
      cases hf : lookupDmaRegion regs (nextPage * pageSize) pageSize with
      | none =>
        exact absurd (decide_eq_true ⟨Nat.le_trans hLo (Nat.le_of_lt hGt),
          Nat.le_trans (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right pageSize (by omega : nextPage + 1 ≤ nextPage + (count + 1))) hEnd⟩)
          (List.find?_eq_none.mp hf reg hRegMem)
      | some r' =>
        obtain ⟨hm', hl', hh'⟩ := lookupDmaRegion_some hf
        rw [hDisj r' hm' reg hRegMem
          (Nat.lt_of_le_of_lt hl' (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hPagePos)
            (Nat.le_trans (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right pageSize (by omega : nextPage + 1 ≤ nextPage + (count + 1))) hEnd)))
          (Nat.lt_of_le_of_lt (Nat.le_trans hLo (Nat.le_of_lt hGt)) (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hPagePos) hh'))]
    dsimp only [checkContigPages]
    rw [hWalk (nextPage * pageSize) (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hPagePos) hPage48),
      specLeafAt_iff_lookup (iova := nextPage * pageSize) (len := pageSize) hDisj hRegs hPagePos
        (by rw [Nat.mul_mod_left, Nat.zero_add]; exact Nat.le_refl _), hFind]
    dsimp only [Option.map]
    have hLoNP : reg.iova.toNat ≤ nextPage * pageSize := Nat.le_trans hLo (Nat.le_of_lt hGt)
    have hPaEq : (reg.paddr.toNat + (nextPage * pageSize - reg.iova.toNat) ==
        reg.paddr.toNat + (iova - reg.iova.toNat) + (nextPage * pageSize - iova)) = true :=
      beq_iff_eq.mpr (by clear hWalk hRegs; omega)
    rw [hPaEq]; simp only [beq_self_eq_true, Bool.and_self, Bool.true_and]
    exact ih (nextPage + 1) (Nat.lt_of_lt_of_le hGt (Nat.mul_le_mul_right pageSize (Nat.le_succ nextPage)))
      (by rw [show nextPage + 1 + count = nextPage + (count + 1) by omega]; exact hEnd)
theorem specLeafAt_some_region {regs : List Stage2DmaRegion} {iova pa granBytes : Nat}
    {perm : IoPerm} (h : specLeafAt regs iova = some (pa, granBytes, perm)) :
    ∃ r ∈ regs, ∃ gran : PageGranule, granBytes = gran.byteSize ∧ perm = r.perm ∧
      r.iova.toNat ≤ (iova / gran.byteSize) * gran.byteSize ∧
      (iova / gran.byteSize) * gran.byteSize + gran.byteSize ≤ r.iova.toNat + r.size.toNat ∧
      pa = r.paddr.toNat + ((iova / gran.byteSize) * gran.byteSize - r.iova.toNat) + iova % gran.byteSize := by
  dsimp only [specLeafAt] at h
  cases hf2 : regs.find? (fun r => regionCovers2M r ((iova / hugeBlock2MiB) * hugeBlock2MiB)) with
  | some r =>
    rw [hf2] at h; injection h with hT
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hT
    obtain ⟨hMem, hrCov⟩ := find_some_mem_pred hf2
    simp only [regionCovers2M, Bool.and_eq_true, decide_eq_true_eq] at hrCov
    exact ⟨r, hMem, .huge2MiB, rfl, rfl, hrCov.2.1, hrCov.2.2, rfl⟩
  | none =>
    rw [hf2] at h
    cases htw : regionsTouchWindow regs ((iova / hugeBlock2MiB) * hugeBlock2MiB) hugeBlock2MiB
    · simp [htw] at h
    · simp only [htw, ↓reduceIte] at h
      cases hf4 : regs.find? (fun r => regionCovers4K r ((iova / pageSize) * pageSize)) with
      | none => simp [hf4] at h
      | some r =>
        rw [hf4] at h; injection h with hT
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Prod.mk.injEq .. ▸ hT
        obtain ⟨hMem, hrCov⟩ := find_some_mem_pred hf4
        simp only [regionCovers4K, Bool.and_eq_true, decide_eq_true_eq] at hrCov
        exact ⟨r, hMem, .page4KiB, rfl, rfl, hrCov.2.1, hrCov.2.2, rfl⟩
def execSmmuV3HardwareDmaOp (arena : SmmuV3RadixArena) (mem : Nat → UInt8) : PeripheralDmaOp → (Nat → UInt8) × Option ByteArray
  | .read sid iova len => match walkSmmuV3Stage2 arena sid iova len .dmaRead with
    | .ok pa => (mem, some (readPhys mem pa len)) | .error _ => (mem, none)
  | .write sid iova payload => match walkSmmuV3Stage2 arena sid iova payload.size .dmaWrite with
    | .ok pa => (writePhys mem pa payload, none) | .error _ => (mem, none)
def execSmmuV3HardwareDmaBurst (arena : SmmuV3RadixArena) (mem : Nat → UInt8) : List PeripheralDmaOp → (Nat → UInt8) × List (Option ByteArray)
  | [] => (mem, [])
  | op :: ops => let (mem₁, obs₁) := execSmmuV3HardwareDmaOp arena mem op
                 let (mem₂, obsRest) := execSmmuV3HardwareDmaBurst arena mem₁ ops; (mem₂, obs₁ :: obsRest)
def SmmuTablePhysAddr (arena : SmmuV3RadixArena) (pa : Nat) : Prop :=
  (arena.arenaBase.toNat ≤ pa ∧ pa < arena.arenaBase.toNat + arena.streamTableFrames * pageSize) ∨
    ∃ tblPa entries, lookupRadixTable arena tblPa = some entries ∧ tblPa ≤ pa ∧ pa < tblPa + pageSize
theorem smmuTablePhysAddr_in_arena {arena : SmmuV3RadixArena} {maxFrames pa : Nat}
    (hCap : arena.streamTableFrames + arena.tables.size ≤ maxFrames) (hTbl : SmmuTablePhysAddr arena pa) :
    arena.arenaBase.toNat ≤ pa ∧ pa < arena.arenaBase.toNat + maxFrames * pageSize := by
  rcases hTbl with ⟨hlo, hhi⟩ | ⟨tblPa, entries, hLook, hlo, hhi⟩
  · simp only [pageSize] at hCap hlo hhi ⊢; omega
  · dsimp only [lookupRadixTable] at hLook; split at hLook; · cases hLook
    rename_i hGe; simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, not_or, Nat.not_lt, Classical.not_not] at hGe
    cases hGet : arena.tables[(tblPa - (arena.arenaBase.toNat + arena.streamTableFrames * pageSize)) / pageSize]? with
    | none => rw [hGet] at hLook; cases hLook
    | some _ => obtain ⟨hIdxLt, _⟩ := Array.getElem?_eq_some_iff.mp hGet; simp only [pageSize] at hCap hGe hIdxLt hlo hhi ⊢; omega
private theorem mapAllocAux_size_at_most_one {f : Nat → Array (Array UInt64) → UInt64 × Array (Array UInt64)}
    {hit K : Nat} (hZero : ∀ idx st, idx ≠ hit → (f idx st).2 = st) (hHit : ∀ st, (f hit st).2.size ≤ st.size + K)
    (i k : Nat) (st : Array (Array UInt64)) : (mapAllocAux f i k st).2.size ≤ st.size + (if i ≤ hit ∧ hit < i + k then K else 0) := by
  induction k generalizing i st with
  | zero => simp only [mapAllocAux, Nat.add_zero]; split <;> omega
  | succ k ih =>
    dsimp only [mapAllocAux]; by_cases hEq : i = hit
    · subst hEq; have h1 := hHit st; have h2 := ih (i + 1) (f i st).2
      have hNo : ¬ (i + 1 ≤ i ∧ i < i + 1 + k) := by omega
      have hYes : i ≤ i ∧ i < i + (k + 1) := by omega
      simp only [hNo, hYes, and_self, ↓reduceIte] at h2 ⊢; omega
    · rw [hZero i st hEq]; have h2 := ih (i + 1) st
      by_cases hIn : i + 1 ≤ hit ∧ hit < i + 1 + k
      · have hIn' : i ≤ hit ∧ hit < i + (k + 1) := by omega
        simp only [hIn, hIn', and_self, ↓reduceIte] at h2 ⊢; exact h2
      · have hOut' : ¬ (i ≤ hit ∧ hit < i + (k + 1)) := by omega
        simp only [hIn, hOut', ↓reduceIte] at h2 ⊢; exact h2
theorem single4K_stream_tables_le_four (arenaBase stFrames : Nat) (r : Stage2DmaRegion)
    (h4K : r.granule = .page4KiB) (hPos : 0 < r.size.toNat)
    (hLt48 : r.iova.toNat + r.size.toNat ≤ smmuAddrLimit48)
    (hSame2M : r.iova.toNat / hugeBlock2MiB = (r.iova.toNat + r.size.toNat - 1) / hugeBlock2MiB)
    (st : Array (Array UInt64)) :
    (buildL0Table arenaBase stFrames [r] st).2.size ≤ st.size + 4 := by
  have hTwUnique : ∀ base win (hMult : hugeBlock2MiB ≤ win ∧ win % hugeBlock2MiB = 0)
      (hBase : base = (r.iova.toNat / (512 * win)) * (512 * win)) (idx : Nat),
      idx ≠ (r.iova.toNat / win) % 512 → regionsTouchWindow [r] (base + idx * win) win = false := by
    intro base win ⟨hGe, hMod⟩ hBase idx hNe
    refine Bool.eq_false_iff.mpr fun hTw => ?_
    simp only [regionsTouchWindow, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hTw
    have hTarget := (radix_step_base r.iova.toNat win).symm; rw [← hBase] at hTarget
    have hSameW : (r.iova.toNat + r.size.toNat - 1) / win = r.iova.toNat / win := by
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hMod
      rw [hq, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hSame2M]
    have hd1 : (r.iova.toNat / win) * win + r.iova.toNat % win = r.iova.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hd2 : ((r.iova.toNat + r.size.toNat - 1) / win) * win + (r.iova.toNat + r.size.toNat - 1) % win =
        r.iova.toNat + r.size.toNat - 1 := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hWinPos : 0 < win := Nat.lt_of_lt_of_le (by decide : 0 < hugeBlock2MiB) hGe
    have hm1 := Nat.mod_lt r.iova.toNat hWinPos
    have hm2 := Nat.mod_lt (r.iova.toNat + r.size.toNat - 1) hWinPos
    by_cases hLtIdx : idx < (r.iova.toNat / win) % 512
    · have hLe : base + (idx + 1) * win ≤ base + ((r.iova.toNat / win) % 512) * win :=
        Nat.add_le_add_left (Nat.mul_le_mul_right win (by omega)) base
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, ← hTarget] at hLe; omega
    · have hGtIdx : (r.iova.toNat / win) % 512 + 1 ≤ idx := by omega
      have hLe : base + ((r.iova.toNat / win) % 512 + 1) * win ≤ base + idx * win :=
        Nat.add_le_add_left (Nat.mul_le_mul_right win hGtIdx) base
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, ← hTarget, ← hSameW] at hLe; omega
  have hMul1 : 512 * hugeBlock2MiB = l1WinSize := by decide
  have hMul2 : 512 * l1WinSize = l0WinSize := by decide
  have hMul3 : 512 * l0WinSize = smmuAddrLimit48 := by decide
  have hL2 : ∀ s, (buildL2Table arenaBase stFrames [r] ((r.iova.toNat / l1WinSize) * l1WinSize) s).2.size ≤ s.size + 2 := by
    intro s; unfold buildL2Table
    have hM := mapAllocAux_size_at_most_one
      (f := buildL2Step arenaBase stFrames [r] ((r.iova.toNat / l1WinSize) * l1WinSize))
      (hit := (r.iova.toNat / hugeBlock2MiB) % 512) (K := 1)
      (fun idx s0 hNe => by
        dsimp only [buildL2Step]
        have hNo2M : ([r].find? fun x => regionCovers2M x (r.iova.toNat / l1WinSize * l1WinSize + idx * hugeBlock2MiB)) = none := by
          simp [regionCovers2M, h4K]
        rw [hNo2M, hTwUnique _ hugeBlock2MiB ⟨Nat.le_refl _, Nat.mod_self _⟩ (by rw [hMul1]) idx hNe]; rfl)
      (fun s0 => by dsimp only [buildL2Step]; split; · dsimp only []; omega
                    split <;> simp [allocRadixTable]) 0 512 s
    have hHit : 0 ≤ (r.iova.toNat / hugeBlock2MiB) % 512 ∧ (r.iova.toNat / hugeBlock2MiB) % 512 < 0 + 512 :=
      ⟨Nat.zero_le _, Nat.mod_lt _ (by decide)⟩
    simp only [hHit, and_self, ↓reduceIte] at hM
    simp only [allocRadixTable, Array.size_push]; omega
  have hL1 : ∀ s, (buildL1Table arenaBase stFrames [r] ((r.iova.toNat / l0WinSize) * l0WinSize) s).2.size ≤ s.size + 3 := by
    intro s; unfold buildL1Table buildBranchTable
    have hM := mapAllocAux_size_at_most_one
      (f := buildBranchStepFn [r] ((r.iova.toNat / l0WinSize) * l0WinSize) l1WinSize (buildL2Table arenaBase stFrames [r]))
      (hit := (r.iova.toNat / l1WinSize) % 512) (K := 2)
      (fun idx s0 hNe => by
        dsimp only [buildBranchStepFn]
        rw [hTwUnique _ l1WinSize ⟨by decide, by decide⟩ (by rw [hMul2]) idx hNe]; rfl)
      (fun s0 => by
        dsimp only [buildBranchStepFn]; split
        · dsimp only []; have hStp := radix_step_base r.iova.toNat l1WinSize; rw [hMul2] at hStp; rw [hStp]; exact hL2 s0
        · dsimp only []; omega) 0 512 s
    have hHit : 0 ≤ (r.iova.toNat / l1WinSize) % 512 ∧ (r.iova.toNat / l1WinSize) % 512 < 0 + 512 :=
      ⟨Nat.zero_le _, Nat.mod_lt _ (by decide)⟩
    simp only [hHit, and_self, ↓reduceIte] at hM
    simp only [allocRadixTable, Array.size_push]; omega
  unfold buildL0Table buildBranchTable
  have h0Eq : (0 : Nat) = (r.iova.toNat / (512 * l0WinSize)) * (512 * l0WinSize) := by
    rw [hMul3, Nat.div_eq_of_lt (by omega), Nat.zero_mul]
  have hM := mapAllocAux_size_at_most_one
    (f := buildBranchStepFn [r] 0 l0WinSize (buildL1Table arenaBase stFrames [r]))
    (hit := (r.iova.toNat / l0WinSize) % 512) (K := 3)
    (fun idx s0 hNe => by
      dsimp only [buildBranchStepFn]
      rw [hTwUnique 0 l0WinSize ⟨by decide, by decide⟩ h0Eq idx hNe]; rfl)
    (fun s0 => by
      dsimp only [buildBranchStepFn]; split
      · dsimp only []
        have hStep0 : 0 + ((r.iova.toNat / l0WinSize) % 512) * l0WinSize = (r.iova.toNat / l0WinSize) * l0WinSize := by
          have hStp := radix_step_base r.iova.toNat l0WinSize; rw [← h0Eq] at hStp; simpa using hStp
        rw [hStep0]; exact hL1 s0
      · dsimp only []; omega) 0 512 st
  have hHit : 0 ≤ (r.iova.toNat / l0WinSize) % 512 ∧ (r.iova.toNat / l0WinSize) % 512 < 0 + 512 :=
    ⟨Nat.zero_le _, Nat.mod_lt _ (by decide)⟩
  simp only [hHit, and_self, ↓reduceIte] at hM
  simp only [allocRadixTable, Array.size_push]; omega
theorem compileStreamRoots_single4K_tables_le (arenaBase stFrames : Nat) :
    ∀ (pts : List Stage2IoPageTable) (st : Array (Array UInt64)),
      (∀ pt ∈ pts, ∃ r, pt.regions = [r] ∧ r.granule = .page4KiB ∧ 0 < r.size.toNat ∧
        r.iova.toNat + r.size.toNat ≤ smmuAddrLimit48 ∧
        r.iova.toNat / hugeBlock2MiB = (r.iova.toNat + r.size.toNat - 1) / hugeBlock2MiB) →
      (compileStreamRoots arenaBase stFrames pts st).2.size ≤ st.size + 4 * pts.length
  | [], st, _ => by simp [compileStreamRoots]
  | pt :: pts, st, hAll => by
    obtain ⟨r, hRegs, h4K, hPos, hLt48, hSame⟩ := hAll pt List.mem_cons_self
    dsimp only [compileStreamRoots]; rw [hRegs]
    have h1 := single4K_stream_tables_le_four arenaBase stFrames r h4K hPos hLt48 hSame st
    have h2 := compileStreamRoots_single4K_tables_le arenaBase stFrames pts
      (buildL0Table arenaBase stFrames [r] st).2 (fun p hp => hAll p (List.mem_cons_of_mem _ hp))
    simp only [List.length_cons]; omega
theorem walkSmmuV3Stage2_agrees_on_region {m : SmmuManifest} {arenaBase : UInt64} {maxFrames : Nat} {arena : SmmuV3RadixArena}
    (hComp : compileManifestToRadixArena m arenaBase maxFrames = .ok arena)
    {pt : Stage2IoPageTable} (hptMem : pt ∈ m.streams) {reg : Stage2DmaRegion} (hregMem : reg ∈ pt.regions)
    {iova len : Nat} (hLen : 0 < len) (hLo : reg.iova.toNat ≤ iova) (hHi : iova + len ≤ reg.iova.toNat + reg.size.toNat)
    (acc : DmaAccess) : walkSmmuV3Stage2 arena pt.streamId iova len acc = translateStage2Dma m pt.streamId iova len acc := by
  obtain ⟨_, hDeny, hNoWild, hAlPool, _, _, _, _, _, _, hEn, _⟩ := compileManifestToRadixArena_unpack hComp
  have hNodup : (m.streams.map Stage2IoPageTable.streamId).Nodup := decide_eq_true_eq.mp ((Bool.and_eq_true _ _).mp hNoWild).1
  have hNwPt := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hNoWild).2 pt hptMem
  have hSidOk : (pt.streamId == 0 || pt.streamId == wildcardStreamId) = false := by
    simp [bne_iff_ne.mp ((Bool.and_eq_true _ _).mp hNwPt).1, bne_iff_ne.mp ((Bool.and_eq_true _ _).mp hNwPt).2]
  have hAlPt := List.all_eq_true.mp hAlPool pt hptMem
  have hDisj := checkRegionsIovaDisjoint_sound ((Bool.and_eq_true _ _).mp hAlPt).1
  have hRegs := fun r hr => List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hAlPt).2 r hr
  have hrAl := hRegs reg hregMem
  simp only [regionAlignedInPoolB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrAl
  obtain ⟨⟨⟨⟨⟨⟨_, hrI48⟩, _⟩, hrIA⟩, _⟩, hrSA⟩, _⟩ := hrAl
  have hLookSt : lookupStream m.streams pt.streamId = some pt := by
    cases hf : lookupStream m.streams pt.streamId with
    | none => exact absurd (by simp) (List.find?_eq_none.mp hf pt hptMem)
    | some pt' => obtain ⟨hm', hs'⟩ := lookupStream_some hf; rw [nodup_streamId_eq hNodup hm' hptMem hs']
  have hLookReg : lookupDmaRegion pt.regions iova len = some reg := by
    cases hf : lookupDmaRegion pt.regions iova len with
    | none => exact absurd (decide_eq_true ⟨hLo, hHi⟩) (List.find?_eq_none.mp hf reg hregMem)
    | some r' => obtain ⟨hm', _, _⟩ := lookupDmaRegion_some hf; rw [hDisj r' hm' reg hregMem (by omega) (by omega)]
  have hRoot := compiledArena_root_and_walk hComp pt.streamId
  rw [hLookSt] at hRoot; obtain ⟨l0Pa, hDecRoot, hWalk⟩ := hRoot
  have hLenB : (len == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hIova48 : iova + len ≤ smmuAddrLimit48 := by omega
  have hLook0 : lookupDmaRegion pt.regions iova 1 = some reg := by
    cases hf : lookupDmaRegion pt.regions iova 1 with
    | none => exact absurd (decide_eq_true ⟨hLo, by omega⟩) (List.find?_eq_none.mp hf reg hregMem)
    | some r' => obtain ⟨hm', _, _⟩ := lookupDmaRegion_some hf; rw [hDisj r' hm' reg hregMem (by omega) (by omega)]
  have hW0 := hWalk iova (by omega)
  rw [specLeafAt_iff_lookup (iova := iova) (len := 1) hDisj hRegs (by decide)
    (Nat.succ_le_of_lt (Nat.mod_lt iova (by decide))), hLook0] at hW0
  dsimp only [Option.map] at hW0
  have hEndMult : (reg.iova.toNat + reg.size.toNat) % pageSize = 0 := by
    cases hg : reg.granule <;> simp only [hg, PageGranule.byteSize, pageSize] at hrIA hrSA ⊢ <;> omega
  have hGt0 : iova < (iova / pageSize + 1) * pageSize := by
    have hd := Nat.div_add_mod iova pageSize
    have hm := Nat.mod_lt iova (by decide : 0 < pageSize)
    simp only [pageSize] at hd hm ⊢; omega
  have hEndContig : ((iova / pageSize + 1) + ((iova + len - 1) / pageSize - iova / pageSize)) * pageSize ≤
      reg.iova.toNat + reg.size.toNat := by
    have hLeDiv : iova / pageSize ≤ (iova + len - 1) / pageSize := Nat.div_le_div_right (by omega)
    have hdLast := Nat.div_add_mod (iova + len - 1) pageSize
    simp only [pageSize] at hLeDiv hdLast hEndMult hLen hHi ⊢; omega
  have hContig : checkContigPages arena l0Pa.toNat (reg.paddr.toNat + (iova - reg.iova.toNat)) reg.perm
      iova (iova / pageSize + 1) ((iova + len - 1) / pageSize - iova / pageSize) = true :=
    checkContigPages_of_region hWalk hDisj hRegs hregMem iova hLo
      (iova / pageSize + 1) ((iova + len - 1) / pageSize - iova / pageSize) hGt0 hEndContig
  unfold walkSmmuV3Stage2 walkSmmuV3Stage2Detail translateStage2Dma
  simp only [hEn, hDeny, hSidOk, hLenB, hDecRoot, hLookSt, hLookReg, hIova48, decide_true,
    hW0, hContig, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases reg.perm.permits acc <;> rfl
end Obend.OS.SmmuDmaConfinement
end
