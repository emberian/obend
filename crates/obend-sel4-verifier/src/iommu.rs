#![forbid(unsafe_code)]
//! Stack-only `#![no_std]` SMMUv3 / RISC-V IOMMU Stage-2 DMA Chokepoint Verifier,
//! deterministic DMA transaction filter, `OBEND.SHE.SMMU_MANIFEST/v1` `cSHAKE256` commitment,
//! and canonical seL4 Microkit `.system` XML + Device Tree `iommus` binding emitter.
//!
//! Closes *Rainbows End* SHE Gap #2 in Rust alongside `Obend.OS.SmmuDmaConfinement`:
//! - Enforces default-deny Stage-2 IOMMU translation (`FaultOnUnmappedStream`).
//! - Ties every peripheral bus-master `StreamId` to `chokepoint.rs`'s 4-PD Microkit layout
//!   (`ingress-pd`, `commit-pd`, `persist-pd`, `tx-egress-pd`) and `< 10 MiB` root-server +
//!   DMA pool physical span budget.
//! - Unconditionally refuses any DMA region overlapping `commit-pd` private copy-before-verify
//!   frames (`copy_into_private_pd_frame_before_verify`), PD code/stack/CSpace frames,
//!   kernel page tables, root-server boot span, or hardware TRNG MMIO registers.
//! - Blocks cross-role privilege escalation (`IngressNic` writing `tx-egress-pd` rings,
//!   `EgressNic` writing finalized outbox payloads, `DisplayScanout` writing anything,
//!   `Commit` PD owning any peripheral DMA stream, or cross-stream writable physical aliasing).

use super::*;

/// Domain customization tag matching `Obend.OS.SmmuDmaConfinement` (`OBEND.SHE.SMMU_MANIFEST/v1`).
pub const SMMU_MANIFEST_DOMAIN: &[u8] = b"OBEND.SHE.SMMU_MANIFEST/v1";

/// Standard 4 KiB Stage-2 IOMMU page granule.
pub const PAGE_SIZE_4K: u64 = 4096;
/// Standard 2 MiB Stage-2 IOMMU block/huge-page granule.
pub const PAGE_SIZE_2M: u64 = 2 * 1024 * 1024;
/// Fixed virtual-address window reserved for the three Microkit chokepoint IPC rings
/// (`ingress_ring` @ `0x4000000`, `commit_leaf_buf` @ `0x4001000`, `egress_release_ring` @ `0x4002000`).
pub const MICROKIT_RESERVED_IPC_VADDR_BASE: u64 = 0x0400_0000;
pub const MICROKIT_RESERVED_IPC_VADDR_SIZE: u64 = 3 * PAGE_SIZE_4K;

/// Hardware peripheral bus-master Stream ID (ARM SMMUv3 SID / RISC-V IOMMU `device_id`).
/// `0` (`UNASSIGNED`) and `u32::MAX` (`WILDCARD`) are unconditionally refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StreamId(pub u32);

impl StreamId {
    pub const UNASSIGNED: Self = Self(0);
    pub const WILDCARD: Self = Self(u32::MAX);

    pub const fn is_valid(self) -> bool {
        self.0 != Self::UNASSIGNED.0 && self.0 != Self::WILDCARD.0
    }
}

/// Supported hardware Stage-2 IOMMU architectures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum IommuArch {
    ArmSmmuV3 = 1,
    RiscvIommu = 2,
}

impl IommuArch {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }

    pub const fn dtb_compatible(self) -> &'static [u8] {
        match self {
            Self::ArmSmmuV3 => b"arm,smmu-v3",
            Self::RiscvIommu => b"riscv,iommu",
        }
    }
}

/// Peripheral bus-master role inside the four-PD Microkit chokepoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum DeviceRole {
    IngressNic = 1,
    PersistNvme = 2,
    EgressNic = 3,
    DisplayScanout = 4,
    CameraCsi2 = 5,
    Gpu = 6,
}

impl DeviceRole {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }

    /// Least-privilege Protection Domain permitted to own this peripheral's DMA stream.
    /// `ChokepointRole::Commit` NEVER owns any peripheral DMA stream!
    pub const fn expected_owner_pd(self) -> ChokepointRole {
        match self {
            Self::IngressNic | Self::CameraCsi2 => ChokepointRole::Ingress,
            Self::PersistNvme => ChokepointRole::Persist,
            Self::EgressNic | Self::DisplayScanout | Self::Gpu => ChokepointRole::TxEgress,
        }
    }

    pub const fn dtb_prefix(self) -> &'static [u8] {
        match self {
            Self::IngressNic => b"ingress-nic",
            Self::PersistNvme => b"persist-nvme",
            Self::EgressNic => b"egress-nic",
            Self::DisplayScanout => b"display-scanout",
            Self::CameraCsi2 => b"camera-csi2",
            Self::Gpu => b"gpu-scanout",
        }
    }

    /// Role-scoped Stage-2 DMA permission gate:
    /// - No peripheral may ever map `CommitPrivateFrame`, `PdCodeStackCspace`, or `TrngMmio`.
    /// - `IngressNic` may only DMA into `IngressRing` (`WriteOnly` / `ReadWrite`).
    /// - `PersistNvme` may only DMA into `PersistWalPool`.
    /// - `EgressNic` may only have `ReadOnly` DMA on `EgressOutboxRing` (never write finalized payloads!).
    /// - `DisplayScanout` & `Gpu` may only have `ReadOnly` DMA on `DisplayFramebuffer`.
    /// - `CameraCsi2` may only DMA into `CameraRing` or `IngressRing` (`WriteOnly` / `ReadWrite`).
    pub const fn permits_region(self, kind: DmaRegionKind, perm: IoPerm) -> bool {
        matches!(
            (self, kind, perm),
            (
                Self::IngressNic,
                DmaRegionKind::IngressRing,
                IoPerm::WriteOnly | IoPerm::ReadWrite,
            ) | (Self::PersistNvme, DmaRegionKind::PersistWalPool, _)
                | (
                    Self::EgressNic,
                    DmaRegionKind::EgressOutboxRing,
                    IoPerm::ReadOnly,
                )
                | (
                    Self::DisplayScanout,
                    DmaRegionKind::DisplayFramebuffer,
                    IoPerm::ReadOnly,
                )
                | (Self::Gpu, DmaRegionKind::DisplayFramebuffer, IoPerm::ReadOnly)
                | (Self::Gpu, DmaRegionKind::GpuScratchPool, _)
                | (
                    Self::CameraCsi2,
                    DmaRegionKind::CameraRing | DmaRegionKind::IngressRing,
                    IoPerm::WriteOnly | IoPerm::ReadWrite,
                )
        )
    }
}

/// Stage-2 IOMMU page/block translation granule (`4 KiB` or `2 MiB`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PageGranule {
    Page4KiB = 1,
    Huge2MiB = 2,
}

impl PageGranule {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }

    pub const fn bytes(self) -> u64 {
        match self {
            Self::Page4KiB => PAGE_SIZE_4K,
            Self::Huge2MiB => PAGE_SIZE_2M,
        }
    }
}

/// Stage-2 IOMMU access permissions for a mapped DMA region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum IoPerm {
    ReadOnly = 1,
    WriteOnly = 2,
    ReadWrite = 3,
}

impl IoPerm {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }

    pub const fn can_read(self) -> bool {
        matches!(self, Self::ReadOnly | Self::ReadWrite)
    }

    pub const fn can_write(self) -> bool {
        matches!(self, Self::WriteOnly | Self::ReadWrite)
    }

    pub const fn allows(self, access: DmaAccess) -> bool {
        match access {
            DmaAccess::Read => self.can_read(),
            DmaAccess::Write => self.can_write(),
        }
    }

    pub const fn xml_perms(self) -> &'static [u8] {
        match self {
            Self::ReadOnly => b"r",
            Self::WriteOnly => b"w",
            Self::ReadWrite => b"rw",
        }
    }
}

/// Physical frame classification for a Stage-2 DMA region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum DmaRegionKind {
    IngressRing = 1,
    CommitPrivateFrame = 2,
    PdCodeStackCspace = 3,
    TrngMmio = 4,
    PersistWalPool = 5,
    EgressOutboxRing = 6,
    DisplayFramebuffer = 7,
    CameraRing = 8,
    GpuScratchPool = 9,
}

impl DmaRegionKind {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }
}

/// Protected physical frame class strictly excluded from ALL peripheral DMA.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ProtectedFrameClass {
    CommitPrivate = 1,
    PdCodeStackCspace = 2,
    TrngMmio = 3,
    KernelPageTable = 4,
}

impl ProtectedFrameClass {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }

    pub const fn dtb_label(self) -> &'static [u8] {
        match self {
            Self::CommitPrivate => b"commit-private",
            Self::PdCodeStackCspace => b"pd-code-stack-cspace",
            Self::TrngMmio => b"trng-mmio",
            Self::KernelPageTable => b"kernel-pt",
        }
    }
}

/// Non-empty physical address range `[base_paddr, base_paddr + size)` excluded from peripheral DMA.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProtectedFrameRange {
    pub class: ProtectedFrameClass,
    pub base_paddr: u64,
    pub size: u64,
}

/// One Stage-2 IOMMU mapping entry translating `[iova, iova + size) -> [paddr, paddr + size)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DmaRegion {
    pub iova: u64,
    pub paddr: u64,
    pub size: u64,
    pub granule: PageGranule,
    pub perm: IoPerm,
    pub kind: DmaRegionKind,
}

/// Per-device SMMUv3 / RISC-V IOMMU stream binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeviceStreamBinding<'a> {
    pub stream_id: StreamId,
    pub role: DeviceRole,
    pub owner_pd: ChokepointRole,
    pub regions: &'a [DmaRegion],
}

/// Complete Stage-2 IOMMU chokepoint policy bound to the 4-PD Microkit layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChokepointIommuPolicy<'a> {
    pub arch: IommuArch,
    /// Must be `true`: unmapped streams unconditionally fault (`FaultOnUnmappedStream`).
    pub default_deny_unmapped: bool,
    pub rootserver_phys_start: u64,
    pub rootserver_phys_end: u64,
    pub dma_pool_base: u64,
    pub dma_pool_size: u64,
    pub protected_ranges: &'a [ProtectedFrameRange],
    pub streams: &'a [DeviceStreamBinding<'a>],
}

/// Exact fail-closed diagnostic refusal for `ChokepointIommuPolicy` verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IommuRefusal {
    DefaultDenyDisabled,
    ChokepointSystemInvalid(ChokepointViolation),
    RootServerSpanMismatch,
    InvalidPhysicalBudget,
    PhysicalBudgetExceeded {
        total_bytes: u64,
        limit_bytes: u64,
    },
    LoaderCollision {
        phys_end: u64,
        loader_base: u64,
    },
    DmaPoolOverlapsRootServer,
    DmaPoolOverlapsProtectedFrame {
        class: ProtectedFrameClass,
    },
    ProtectedRangeInvalid,
    MissingRequiredProtection {
        class: ProtectedFrameClass,
    },
    EmptyStreamTable,
    UnassignedOrWildcardStreamId {
        stream_id: u32,
    },
    DuplicateStreamId {
        stream_id: u32,
    },
    StreamOwnerRoleMismatch {
        stream_id: u32,
        device_role: DeviceRole,
        owner_pd: ChokepointRole,
    },
    UnalignedDmaRegion {
        stream_id: u32,
        addr: u64,
        size: u64,
        required_align: u64,
    },
    WrappingAddressRange {
        stream_id: u32,
        addr: u64,
        size: u64,
    },
    DmaRegionOutsidePool {
        stream_id: u32,
        paddr: u64,
        size: u64,
    },
    OverlappingRootServerSpan {
        stream_id: u32,
        paddr: u64,
    },
    OverlappingProtectedFrame {
        stream_id: u32,
        class: ProtectedFrameClass,
        paddr: u64,
    },
    OverlappingStreamIova {
        stream_id: u32,
        iova_a: u64,
        iova_b: u64,
    },
    ForbiddenDmaRegionKind {
        stream_id: u32,
        role: DeviceRole,
        kind: DmaRegionKind,
        perm: IoPerm,
    },
    CrossStreamWritableAlias {
        stream_a: u32,
        stream_b: u32,
        paddr: u64,
    },
}

/// Bus-master DMA access direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DmaAccess {
    Read,
    Write,
}

/// Hardware Stage-2 IOMMU translation fault.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DmaFault {
    DefaultDenyDisabled,
    UnmappedStream {
        stream_id: u32,
    },
    ZeroLengthTransfer,
    AddressWrap,
    UnmappedIova {
        stream_id: u32,
        iova: u64,
    },
    CrossRegionSpanDenied {
        stream_id: u32,
        iova: u64,
        len: u64,
    },
    PermissionDenied {
        stream_id: u32,
        iova: u64,
        perm: IoPerm,
        access: DmaAccess,
    },
}

/// Result of a permitted Stage-2 DMA translation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DmaTranslation {
    pub paddr: u64,
    pub len: u64,
    pub kind: DmaRegionKind,
    pub perm: IoPerm,
}

/// Single peripheral DMA transaction for deterministic bus simulation/fuzzing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DmaBurstOp {
    pub stream_id: StreamId,
    pub iova: u64,
    pub len: u64,
    pub access: DmaAccess,
    pub payload_byte: u8,
}

/// Summary counters returned by the deterministic DMA bus simulator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DmaSimReport {
    pub total_ops: u64,
    pub allowed_reads: u64,
    pub allowed_writes: u64,
    pub faulted_ops: u64,
    pub private_frame_touches: u64,
    pub egress_outbox_writes: u64,
}

/// Error returned by the `#![no_std]` fixed-slice XML / DTB emitters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EmitError {
    BufferTooSmall,
    InvalidPolicy(IommuRefusal),
    ReservedIpcVaddrCollision {
        stream_id: u32,
        iova: u64,
    },
}

fn ranges_overlap(a_start: u64, a_len: u64, b_start: u64, b_len: u64) -> Option<bool> {
    let a_end = a_start.checked_add(a_len)?;
    let b_end = b_start.checked_add(b_len)?;
    Some(!(a_end <= b_start || b_end <= a_start))
}

fn range_contains(outer_start: u64, outer_len: u64, inner_start: u64, inner_len: u64) -> Option<bool> {
    let outer_end = outer_start.checked_add(outer_len)?;
    let inner_end = inner_start.checked_add(inner_len)?;
    Some(inner_start >= outer_start && inner_end <= outer_end)
}

fn check_loader_window(phys_start: u64, phys_end: u64) -> Result<(), IommuRefusal> {
    if phys_start < STOCK_MICROKIT_LOADER_BASE && phys_end > STOCK_MICROKIT_LOADER_BASE {
        return Err(IommuRefusal::LoaderCollision {
            phys_end,
            loader_base: STOCK_MICROKIT_LOADER_BASE,
        });
    }
    Ok(())
}

/// Compute the canonical 32-byte `OBEND.SHE.SMMU_MANIFEST/v1` `cSHAKE256` commitment over every
/// field of `policy` using LEB128-length-framed fields (`encodeListField` parity with Lean).
///
/// Streaming `#![no_std]` implementation with zero heap allocation and no fixed-capacity truncation.
pub fn smmu_manifest_digest(policy: &ChokepointIommuPolicy<'_>) -> Digest {
    let mut s = customized(SMMU_MANIFEST_DOMAIN);
    field(&mut s, &[policy.arch.tag_byte()]);
    field(&mut s, &[u8::from(policy.default_deny_unmapped)]);
    field(&mut s, &policy.rootserver_phys_start.to_be_bytes());
    field(&mut s, &policy.rootserver_phys_end.to_be_bytes());
    field(&mut s, &policy.dma_pool_base.to_be_bytes());
    field(&mut s, &policy.dma_pool_size.to_be_bytes());

    // Field 7: protected_ranges (`be8(count) || concat([class(1B) || be8(base) || be8(size)])`)
    let prot_count = u64::try_from(policy.protected_ranges.len()).expect("protected count");
    let prot_body_len = prot_count
        .checked_mul(17)
        .and_then(|n| n.checked_add(8))
        .expect("protected field length");
    let mut len_buf = [0u8; 10];
    let n = leb(prot_body_len, &mut len_buf);
    s.absorb(&len_buf[..n]);
    s.absorb(&prot_count.to_be_bytes());
    for r in policy.protected_ranges {
        s.absorb(&[r.class.tag_byte()]);
        s.absorb(&r.base_paddr.to_be_bytes());
        s.absorb(&r.size.to_be_bytes());
    }

    // Field 8: streams (`be8(count) || concat(be4(sid) || role(1B) || owner_pd(1B) || be8(rcount) || regions)`)
    let stream_count = u64::try_from(policy.streams.len()).expect("stream count");
    let mut streams_body_len = 8u64;
    for st in policy.streams {
        let rc = u64::try_from(st.regions.len()).expect("region count");
        let reg_bytes = rc.checked_mul(27).expect("region bytes");
        streams_body_len = streams_body_len
            .checked_add(14)
            .and_then(|acc| acc.checked_add(reg_bytes))
            .expect("streams field length");
    }
    let m = leb(streams_body_len, &mut len_buf);
    s.absorb(&len_buf[..m]);
    s.absorb(&stream_count.to_be_bytes());
    for st in policy.streams {
        s.absorb(&st.stream_id.0.to_be_bytes());
        s.absorb(&[st.role.tag_byte()]);
        s.absorb(&[st.owner_pd.index() as u8]);
        let rc = u64::try_from(st.regions.len()).expect("region count");
        s.absorb(&rc.to_be_bytes());
        for reg in st.regions {
            s.absorb(&reg.iova.to_be_bytes());
            s.absorb(&reg.paddr.to_be_bytes());
            s.absorb(&reg.size.to_be_bytes());
            s.absorb(&[reg.granule.tag_byte()]);
            s.absorb(&[reg.perm.tag_byte()]);
            s.absorb(&[reg.kind.tag_byte()]);
        }
    }

    s.digest()
}

/// Fail-closed verifier for a Stage-2 SMMUv3 / RISC-V IOMMU chokepoint policy.
/// Returns the 32-byte `OBEND.SHE.SMMU_MANIFEST/v1` commitment digest on success.
pub fn verify_iommu_policy(policy: &ChokepointIommuPolicy<'_>) -> Result<Digest, IommuRefusal> {
    if !policy.default_deny_unmapped {
        return Err(IommuRefusal::DefaultDenyDisabled);
    }

    if policy.rootserver_phys_end <= policy.rootserver_phys_start || policy.dma_pool_size == 0 {
        return Err(IommuRefusal::InvalidPhysicalBudget);
    }
    if !policy.dma_pool_base.is_multiple_of(PAGE_SIZE_4K)
        || !policy.dma_pool_size.is_multiple_of(PAGE_SIZE_4K)
    {
        return Err(IommuRefusal::InvalidPhysicalBudget);
    }
    let dma_pool_end = policy
        .dma_pool_base
        .checked_add(policy.dma_pool_size)
        .ok_or(IommuRefusal::InvalidPhysicalBudget)?;
    let root_span = policy.rootserver_phys_end - policy.rootserver_phys_start;
    let total_budget = root_span
        .checked_add(policy.dma_pool_size)
        .ok_or(IommuRefusal::InvalidPhysicalBudget)?;
    if total_budget >= MAX_ROOTSERVER_SPAN_BYTES {
        return Err(IommuRefusal::PhysicalBudgetExceeded {
            total_bytes: total_budget,
            limit_bytes: MAX_ROOTSERVER_SPAN_BYTES,
        });
    }
    check_loader_window(policy.rootserver_phys_start, policy.rootserver_phys_end)?;
    check_loader_window(policy.dma_pool_base, dma_pool_end)?;

    // Pool-level disjointness from root-server physical span.
    if ranges_overlap(
        policy.dma_pool_base,
        policy.dma_pool_size,
        policy.rootserver_phys_start,
        root_span,
    )
    .unwrap_or(true)
    {
        return Err(IommuRefusal::DmaPoolOverlapsRootServer);
    }

    // Validate protected physical frame ranges, ensure commit-private & PD code/stack/CSpace are pinned,
    // and enforce pool-level disjointness from every protected range.
    let mut has_commit_private = false;
    let mut has_pd_code_stack = false;
    for pr in policy.protected_ranges {
        if pr.size == 0 || pr.base_paddr.checked_add(pr.size).is_none() {
            return Err(IommuRefusal::ProtectedRangeInvalid);
        }
        if ranges_overlap(
            policy.dma_pool_base,
            policy.dma_pool_size,
            pr.base_paddr,
            pr.size,
        )
        .unwrap_or(true)
        {
            return Err(IommuRefusal::DmaPoolOverlapsProtectedFrame { class: pr.class });
        }
        match pr.class {
            ProtectedFrameClass::CommitPrivate => has_commit_private = true,
            ProtectedFrameClass::PdCodeStackCspace => has_pd_code_stack = true,
            ProtectedFrameClass::TrngMmio | ProtectedFrameClass::KernelPageTable => {}
        }
    }
    if !has_commit_private {
        return Err(IommuRefusal::MissingRequiredProtection {
            class: ProtectedFrameClass::CommitPrivate,
        });
    }
    if !has_pd_code_stack {
        return Err(IommuRefusal::MissingRequiredProtection {
            class: ProtectedFrameClass::PdCodeStackCspace,
        });
    }

    if policy.streams.is_empty() {
        return Err(IommuRefusal::EmptyStreamTable);
    }

    for (s_idx, st) in policy.streams.iter().enumerate() {
        if !st.stream_id.is_valid() {
            return Err(IommuRefusal::UnassignedOrWildcardStreamId {
                stream_id: st.stream_id.0,
            });
        }
        for later in &policy.streams[s_idx + 1..] {
            if st.stream_id == later.stream_id {
                return Err(IommuRefusal::DuplicateStreamId {
                    stream_id: st.stream_id.0,
                });
            }
        }
        if st.owner_pd == ChokepointRole::Commit || st.owner_pd != st.role.expected_owner_pd() {
            return Err(IommuRefusal::StreamOwnerRoleMismatch {
                stream_id: st.stream_id.0,
                device_role: st.role,
                owner_pd: st.owner_pd,
            });
        }

        for (r_idx, reg) in st.regions.iter().enumerate() {
            let align = reg.granule.bytes();
            if reg.size == 0 || !reg.size.is_multiple_of(align) {
                return Err(IommuRefusal::UnalignedDmaRegion {
                    stream_id: st.stream_id.0,
                    addr: reg.paddr,
                    size: reg.size,
                    required_align: align,
                });
            }
            if !reg.iova.is_multiple_of(align) {
                return Err(IommuRefusal::UnalignedDmaRegion {
                    stream_id: st.stream_id.0,
                    addr: reg.iova,
                    size: reg.size,
                    required_align: align,
                });
            }
            if !reg.paddr.is_multiple_of(align) {
                return Err(IommuRefusal::UnalignedDmaRegion {
                    stream_id: st.stream_id.0,
                    addr: reg.paddr,
                    size: reg.size,
                    required_align: align,
                });
            }
            if reg.iova.checked_add(reg.size).is_none() {
                return Err(IommuRefusal::WrappingAddressRange {
                    stream_id: st.stream_id.0,
                    addr: reg.iova,
                    size: reg.size,
                });
            }
            if reg.paddr.checked_add(reg.size).is_none() {
                return Err(IommuRefusal::WrappingAddressRange {
                    stream_id: st.stream_id.0,
                    addr: reg.paddr,
                    size: reg.size,
                });
            }

            if !st.role.permits_region(reg.kind, reg.perm) {
                return Err(IommuRefusal::ForbiddenDmaRegionKind {
                    stream_id: st.stream_id.0,
                    role: st.role,
                    kind: reg.kind,
                    perm: reg.perm,
                });
            }

            // Reject any DMA mapping overlapping the Microkit root-server physical span.
            if ranges_overlap(
                reg.paddr,
                reg.size,
                policy.rootserver_phys_start,
                root_span,
            )
            .unwrap_or(true)
            {
                return Err(IommuRefusal::OverlappingRootServerSpan {
                    stream_id: st.stream_id.0,
                    paddr: reg.paddr,
                });
            }

            // Reject any DMA mapping overlapping protected frames (commit-pd private, code/stack/CSpace, TRNG, PT).
            for pr in policy.protected_ranges {
                if ranges_overlap(reg.paddr, reg.size, pr.base_paddr, pr.size).unwrap_or(true) {
                    return Err(IommuRefusal::OverlappingProtectedFrame {
                        stream_id: st.stream_id.0,
                        class: pr.class,
                        paddr: reg.paddr,
                    });
                }
            }

            // Every DMA region must sit strictly inside the budgeted DMA pool.
            if !range_contains(
                policy.dma_pool_base,
                policy.dma_pool_size,
                reg.paddr,
                reg.size,
            )
            .unwrap_or(false)
            {
                return Err(IommuRefusal::DmaRegionOutsidePool {
                    stream_id: st.stream_id.0,
                    paddr: reg.paddr,
                    size: reg.size,
                });
            }

            // Intra-stream IOVA uniqueness (no overlapping IOVA translations in one Stage-2 table).
            for other_reg in &st.regions[r_idx + 1..] {
                if ranges_overlap(reg.iova, reg.size, other_reg.iova, other_reg.size).unwrap_or(true)
                {
                    return Err(IommuRefusal::OverlappingStreamIova {
                        stream_id: st.stream_id.0,
                        iova_a: reg.iova,
                        iova_b: other_reg.iova,
                    });
                }
            }

            // Cross-stream writable physical aliasing check: blocks peripheral-to-peripheral DMA bypass!
            for later_st in &policy.streams[s_idx + 1..] {
                for other_reg in later_st.regions {
                    if (reg.perm.can_write() || other_reg.perm.can_write())
                        && ranges_overlap(reg.paddr, reg.size, other_reg.paddr, other_reg.size)
                            .unwrap_or(true)
                    {
                        return Err(IommuRefusal::CrossStreamWritableAlias {
                            stream_a: st.stream_id.0,
                            stream_b: later_st.stream_id.0,
                            paddr: reg.paddr,
                        });
                    }
                }
            }
        }
    }

    Ok(smmu_manifest_digest(policy))
}

/// Coupled verification tying `ChokepointIommuPolicy` directly to `chokepoint.rs`'s
/// `ChokepointSystemDesc` and `FourPdCspace`:
/// 1. Runs `verify_chokepoint_system(desc, cspaces)`.
/// 2. Pins `policy.rootserver_phys_{start,end} == desc.rootserver_phys_{start,end}`.
/// 3. Runs `verify_iommu_policy(policy)`.
/// 4. Ensures every live `KernelObject::PrivateFrame { pfn }` in `commit-pd`'s CSpace AND every
///    PD MMIO aperture (`HardwareTrngMmio`, `RxNicMmio`, `TxNicMmio`, `DurableLogStorage`) in `desc`
///    is completely unreachable by every peripheral DMA stream!
pub fn verify_chokepoint_with_iommu<const SLOTS: usize>(
    desc: &ChokepointSystemDesc<'_>,
    cspaces: &FourPdCspace<SLOTS>,
    policy: &ChokepointIommuPolicy<'_>,
) -> Result<Digest, IommuRefusal> {
    verify_chokepoint_system(desc, cspaces).map_err(IommuRefusal::ChokepointSystemInvalid)?;

    if policy.rootserver_phys_start != desc.rootserver_phys_start
        || policy.rootserver_phys_end != desc.rootserver_phys_end
    {
        return Err(IommuRefusal::RootServerSpanMismatch);
    }

    let digest = verify_iommu_policy(policy)?;

    // Cross-check Commit PD's live CSpace `PrivateFrame`s against every stream's DMA regions and the DMA pool.
    for entry in cspaces.pd_table(ChokepointRole::Commit).slots() {
        if !entry.live {
            continue;
        }
        if let KernelObject::PrivateFrame { pfn } = entry.obj {
            let priv_paddr = pfn
                .checked_mul(PAGE_SIZE_4K)
                .ok_or(IommuRefusal::ProtectedRangeInvalid)?;
            for st in policy.streams {
                for reg in st.regions {
                    if ranges_overlap(reg.paddr, reg.size, priv_paddr, PAGE_SIZE_4K).unwrap_or(true)
                    {
                        return Err(IommuRefusal::OverlappingProtectedFrame {
                            stream_id: st.stream_id.0,
                            class: ProtectedFrameClass::CommitPrivate,
                            paddr: reg.paddr,
                        });
                    }
                }
            }
            if ranges_overlap(
                policy.dma_pool_base,
                policy.dma_pool_size,
                priv_paddr,
                PAGE_SIZE_4K,
            )
            .unwrap_or(true)
            {
                return Err(IommuRefusal::DmaPoolOverlapsProtectedFrame {
                    class: ProtectedFrameClass::CommitPrivate,
                });
            }
        }
    }

    // Cross-check all PD MMIO apertures (including HardwareTrngMmio) against every DMA region and the DMA pool.
    for pd in &desc.domains {
        for ap in pd.apertures {
            let class = match ap.kind {
                ApertureKind::HardwareTrngMmio => ProtectedFrameClass::TrngMmio,
                _ => ProtectedFrameClass::PdCodeStackCspace,
            };
            for st in policy.streams {
                for reg in st.regions {
                    if ranges_overlap(reg.paddr, reg.size, ap.base_paddr, ap.byte_size)
                        .unwrap_or(true)
                    {
                        return Err(IommuRefusal::OverlappingProtectedFrame {
                            stream_id: st.stream_id.0,
                            class,
                            paddr: reg.paddr,
                        });
                    }
                }
            }
            if ranges_overlap(
                policy.dma_pool_base,
                policy.dma_pool_size,
                ap.base_paddr,
                ap.byte_size,
            )
            .unwrap_or(true)
            {
                return Err(IommuRefusal::DmaPoolOverlapsProtectedFrame { class });
            }
        }
    }

    Ok(digest)
}

/// Deterministic Stage-2 IOMMU transaction filter (`translate_dma`):
/// - Unconditionally faults (`FaultOnUnmappedStream`) on unknown/unmapped `stream_id`s.
/// - Refuses zero-length transfers, wrapping `[iova, iova + len)` ranges, partial cross-region
///   escapes (atomic fail-closed), and read/write permission violations.
pub fn translate_dma(
    policy: &ChokepointIommuPolicy<'_>,
    stream_id: StreamId,
    iova: u64,
    len: u64,
    access: DmaAccess,
) -> Result<DmaTranslation, DmaFault> {
    if !policy.default_deny_unmapped {
        return Err(DmaFault::DefaultDenyDisabled);
    }
    if len == 0 {
        return Err(DmaFault::ZeroLengthTransfer);
    }
    let req_end = iova.checked_add(len).ok_or(DmaFault::AddressWrap)?;

    if !stream_id.is_valid() {
        return Err(DmaFault::UnmappedStream {
            stream_id: stream_id.0,
        });
    }

    let Some(stream) = policy.streams.iter().find(|s| s.stream_id == stream_id) else {
        return Err(DmaFault::UnmappedStream {
            stream_id: stream_id.0,
        });
    };

    for reg in stream.regions {
        let Some(reg_end) = reg.iova.checked_add(reg.size) else {
            continue;
        };
        if iova >= reg.iova && iova < reg_end {
            if req_end > reg_end {
                return Err(DmaFault::CrossRegionSpanDenied {
                    stream_id: stream_id.0,
                    iova,
                    len,
                });
            }
            if !reg.perm.allows(access) {
                return Err(DmaFault::PermissionDenied {
                    stream_id: stream_id.0,
                    iova,
                    perm: reg.perm,
                    access,
                });
            }
            let offset = iova - reg.iova;
            let paddr = reg.paddr.checked_add(offset).ok_or(DmaFault::AddressWrap)?;
            if paddr.checked_add(len).is_none() {
                return Err(DmaFault::AddressWrap);
            }
            return Ok(DmaTranslation {
                paddr,
                len,
                kind: reg.kind,
                perm: reg.perm,
            });
        }
    }

    Err(DmaFault::UnmappedIova {
        stream_id: stream_id.0,
        iova,
    })
}

impl ChokepointIommuPolicy<'_> {
    pub fn translate_dma(
        &self,
        stream_id: StreamId,
        iova: u64,
        len: u64,
        access: DmaAccess,
    ) -> Result<DmaTranslation, DmaFault> {
        translate_dma(self, stream_id, iova, len, access)
    }

    /// Returns `true` iff NO peripheral DMA stream can reach `[paddr, paddr + size)` (read OR write).
    pub fn physical_range_is_dma_unreachable(&self, paddr: u64, size: u64) -> bool {
        if size == 0 || paddr.checked_add(size).is_none() {
            return false;
        }
        for st in self.streams {
            for reg in st.regions {
                if ranges_overlap(reg.paddr, reg.size, paddr, size).unwrap_or(true) {
                    return false;
                }
            }
        }
        true
    }
}

/// Run a deterministic sequence of arbitrary peripheral DMA operations against a verified
/// `ChokepointIommuPolicy`, verifying that:
/// - `commit-pd` private frame bytes `[private_paddr, private_paddr + private_frame.len())`
///   are NEVER read or written, and
/// - `EgressOutboxRing` payloads are NEVER written by any peripheral!
///
/// Any permitted write landing inside `[pool_backing_base, pool_backing_base + pool_backing.len())`
/// is applied to `pool_backing` so callers can also verify normal RX/NVMe DMA still works.
pub fn simulate_dma_burst(
    policy: &ChokepointIommuPolicy<'_>,
    private_paddr: u64,
    private_frame: &[u8],
    pool_backing_base: u64,
    pool_backing: &mut [u8],
    ops: &[DmaBurstOp],
) -> Result<DmaSimReport, IommuRefusal> {
    let _ = verify_iommu_policy(policy)?;

    let mut report = DmaSimReport {
        total_ops: 0,
        allowed_reads: 0,
        allowed_writes: 0,
        faulted_ops: 0,
        private_frame_touches: 0,
        egress_outbox_writes: 0,
    };

    let priv_len = u64::try_from(private_frame.len()).unwrap_or(0);
    let pool_len = u64::try_from(pool_backing.len()).unwrap_or(0);

    for op in ops {
        report.total_ops = report.total_ops.saturating_add(1);
        match translate_dma(policy, op.stream_id, op.iova, op.len, op.access) {
            Err(_) => {
                report.faulted_ops = report.faulted_ops.saturating_add(1);
            }
            Ok(tr) => {
                if priv_len > 0
                    && ranges_overlap(tr.paddr, tr.len, private_paddr, priv_len).unwrap_or(true)
                {
                    report.private_frame_touches = report.private_frame_touches.saturating_add(1);
                }
                match op.access {
                    DmaAccess::Read => {
                        report.allowed_reads = report.allowed_reads.saturating_add(1);
                    }
                    DmaAccess::Write => {
                        report.allowed_writes = report.allowed_writes.saturating_add(1);
                        if tr.kind == DmaRegionKind::EgressOutboxRing {
                            report.egress_outbox_writes =
                                report.egress_outbox_writes.saturating_add(1);
                        }
                        if pool_len > 0
                            && range_contains(pool_backing_base, pool_len, tr.paddr, tr.len)
                                .unwrap_or(false)
                        {
                            let start = (tr.paddr - pool_backing_base) as usize;
                            let count = (tr.len as usize).min(pool_backing.len() - start);
                            pool_backing[start..start + count].fill(op.payload_byte);
                        }
                    }
                }
            }
        }
    }

    Ok(report)
}

/// Zero-allocation fixed-slice writer for canonical `.system` XML and DTS `iommus` emission.
struct SliceWriter<'a> {
    out: &'a mut [u8],
    pos: usize,
}

impl<'a> SliceWriter<'a> {
    fn new(out: &'a mut [u8]) -> Self {
        Self { out, pos: 0 }
    }

    fn written(&self) -> usize {
        self.pos
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), EmitError> {
        let end = self
            .pos
            .checked_add(bytes.len())
            .ok_or(EmitError::BufferTooSmall)?;
        if end > self.out.len() {
            return Err(EmitError::BufferTooSmall);
        }
        self.out[self.pos..end].copy_from_slice(bytes);
        self.pos = end;
        Ok(())
    }

    fn write_hex_u64(&mut self, mut val: u64) -> Result<(), EmitError> {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut buf = [0u8; 16];
        let mut idx = 16usize;
        if val == 0 {
            return self.write_bytes(b"0x0");
        }
        while val > 0 {
            idx -= 1;
            buf[idx] = HEX[(val & 0xf) as usize];
            val >>= 4;
        }
        self.write_bytes(b"0x")?;
        self.write_bytes(&buf[idx..])
    }

    fn write_dec_u64(&mut self, mut val: u64) -> Result<(), EmitError> {
        let mut buf = [0u8; 20];
        let mut idx = 20usize;
        if val == 0 {
            return self.write_bytes(b"0");
        }
        while val > 0 {
            idx -= 1;
            buf[idx] = b'0' + (val % 10) as u8;
            val /= 10;
        }
        self.write_bytes(&buf[idx..])
    }

    fn write_digest_hex(&mut self, digest: &Digest) -> Result<(), EmitError> {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut buf = [0u8; 64];
        for (i, &b) in digest.iter().enumerate() {
            buf[2 * i] = HEX[(b >> 4) as usize];
            buf[2 * i + 1] = HEX[(b & 0xf) as usize];
        }
        self.write_bytes(&buf)
    }
}

/// Emit a canonical seL4 Microkit `.system` XML manifest directly into a caller-supplied
/// fixed byte slice (`#![no_std]`, zero heap allocation).
///
/// Fail-closed: unconditionally refuses to emit XML if `verify_iommu_policy(policy)` fails
/// or if `policy` disagrees with `desc`'s root-server physical span.
pub fn emit_microkit_system_xml(
    policy: &ChokepointIommuPolicy<'_>,
    desc: &ChokepointSystemDesc<'_>,
    out: &mut [u8],
) -> Result<usize, EmitError> {
    if policy.rootserver_phys_start != desc.rootserver_phys_start
        || policy.rootserver_phys_end != desc.rootserver_phys_end
    {
        return Err(EmitError::InvalidPolicy(IommuRefusal::RootServerSpanMismatch));
    }
    let digest = verify_iommu_policy(policy).map_err(EmitError::InvalidPolicy)?;

    // Reject any DMA region whose IOVA/VAddr collides with the fixed Microkit IPC ring VAddr window.
    for st in policy.streams {
        for reg in st.regions {
            if ranges_overlap(
                reg.iova,
                reg.size,
                MICROKIT_RESERVED_IPC_VADDR_BASE,
                MICROKIT_RESERVED_IPC_VADDR_SIZE,
            )
            .unwrap_or(true)
            {
                return Err(EmitError::ReservedIpcVaddrCollision {
                    stream_id: st.stream_id.0,
                    iova: reg.iova,
                });
            }
        }
    }

    let mut w = SliceWriter::new(out);
    w.write_bytes(b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<system>\n")?;
    w.write_bytes(b"  <!-- OBEND.SHE.SMMU_MANIFEST/v1 digest=")?;
    w.write_digest_hex(&digest)?;
    w.write_bytes(b" arch=")?;
    w.write_bytes(policy.arch.dtb_compatible())?;
    w.write_bytes(b" -->\n")?;

    // Canonical shared IPC rings for the four-PD chokepoint.
    w.write_bytes(b"  <memory_region name=\"ingress_ring\" size=\"0x1000\" />\n")?;
    w.write_bytes(b"  <memory_region name=\"commit_leaf_buf\" size=\"0x1000\" />\n")?;
    w.write_bytes(b"  <memory_region name=\"egress_release_ring\" size=\"0x1000\" />\n")?;

    // Physical DMA memory regions bound to SMMUv3 / RISC-V IOMMU streams.
    for st in policy.streams {
        for (r_idx, reg) in st.regions.iter().enumerate() {
            w.write_bytes(b"  <memory_region name=\"dma_s")?;
            w.write_dec_u64(st.stream_id.0 as u64)?;
            w.write_bytes(b"_r")?;
            w.write_dec_u64(r_idx as u64)?;
            w.write_bytes(b"\" size=\"")?;
            w.write_hex_u64(reg.size)?;
            w.write_bytes(b"\" phys_addr=\"")?;
            w.write_hex_u64(reg.paddr)?;
            w.write_bytes(b"\" />\n")?;
        }
    }

    // Four Protection Domains with strict least-privilege mappings (commit-pd maps zero DMA pools!).
    for pd in &desc.domains {
        w.write_bytes(b"  <protection_domain name=\"")?;
        w.write_bytes(pd.name)?;
        w.write_bytes(b"\" priority=\"")?;
        w.write_dec_u64(pd.priority as u64)?;
        w.write_bytes(b"\">\n")?;
        w.write_bytes(b"    <program_image path=\"")?;
        w.write_bytes(pd.name)?;
        w.write_bytes(b".elf\" />\n")?;

        match pd.role {
            ChokepointRole::Ingress => {
                w.write_bytes(
                    b"    <map mr=\"ingress_ring\" vaddr=\"0x4000000\" perms=\"rw\" />\n",
                )?;
            }
            ChokepointRole::Commit => {
                w.write_bytes(
                    b"    <map mr=\"ingress_ring\" vaddr=\"0x4000000\" perms=\"r\" />\n",
                )?;
                w.write_bytes(
                    b"    <map mr=\"commit_leaf_buf\" vaddr=\"0x4001000\" perms=\"rw\" />\n",
                )?;
                w.write_bytes(
                    b"    <map mr=\"egress_release_ring\" vaddr=\"0x4002000\" perms=\"rw\" />\n",
                )?;
            }
            ChokepointRole::Persist => {
                w.write_bytes(
                    b"    <map mr=\"commit_leaf_buf\" vaddr=\"0x4001000\" perms=\"r\" />\n",
                )?;
            }
            ChokepointRole::TxEgress => {
                w.write_bytes(
                    b"    <map mr=\"egress_release_ring\" vaddr=\"0x4002000\" perms=\"r\" />\n",
                )?;
            }
        }

        // Map owned peripheral DMA regions into their owning PD only (never `commit-pd`).
        for st in policy.streams {
            if st.owner_pd == pd.role {
                for (r_idx, reg) in st.regions.iter().enumerate() {
                    w.write_bytes(b"    <map mr=\"dma_s")?;
                    w.write_dec_u64(st.stream_id.0 as u64)?;
                    w.write_bytes(b"_r")?;
                    w.write_dec_u64(r_idx as u64)?;
                    w.write_bytes(b"\" vaddr=\"")?;
                    w.write_hex_u64(reg.iova)?;
                    w.write_bytes(b"\" perms=\"")?;
                    w.write_bytes(reg.perm.xml_perms())?;
                    w.write_bytes(b"\" cached=\"false\" />\n")?;
                }
            }
        }
        w.write_bytes(b"  </protection_domain>\n")?;
    }

    // Directed IPC channels (`ingress-pd <-> commit-pd`, `commit-pd <-> persist-pd`, `commit-pd <-> tx-egress-pd`).
    for ch in desc.channels {
        w.write_bytes(b"  <channel>\n")?;
        w.write_bytes(b"    <end pd=\"")?;
        w.write_bytes(ch.src.expected_name())?;
        w.write_bytes(b"\" id=\"")?;
        w.write_dec_u64(ch.channel_id as u64)?;
        w.write_bytes(b"\" />\n")?;
        w.write_bytes(b"    <end pd=\"")?;
        w.write_bytes(ch.dst.expected_name())?;
        w.write_bytes(b"\" id=\"")?;
        w.write_dec_u64(ch.channel_id as u64)?;
        w.write_bytes(b"\" />\n")?;
        w.write_bytes(b"  </channel>\n")?;
    }

    w.write_bytes(b"</system>\n")?;
    Ok(w.written())
}

/// Emit a canonical Device Tree Source (DTS) `iommus` + `reserved-memory` binding fragment
/// directly into a caller-supplied fixed byte slice (`#![no_std]`, zero heap allocation).
///
/// Fail-closed: unconditionally refuses to emit DTS unless `verify_iommu_policy(policy)` passes.
pub fn emit_dtb_iommus_binding(
    policy: &ChokepointIommuPolicy<'_>,
    out: &mut [u8],
) -> Result<usize, EmitError> {
    let digest = verify_iommu_policy(policy).map_err(EmitError::InvalidPolicy)?;
    let root_span = policy.rootserver_phys_end - policy.rootserver_phys_start;

    let mut w = SliceWriter::new(out);
    w.write_bytes(b"/* OBEND.SHE.SMMU_MANIFEST/v1 digest=")?;
    w.write_digest_hex(&digest)?;
    w.write_bytes(b" */\n")?;

    w.write_bytes(b"iommu0: iommu {\n  compatible = \"")?;
    w.write_bytes(policy.arch.dtb_compatible())?;
    w.write_bytes(b"\";\n  #iommu-cells = <1>;\n  status = \"okay\";\n")?;
    w.write_bytes(b"  /* default-deny: FaultOnUnmappedStream */\n};\n")?;

    // Reserved-memory block pinning root-server + all protected frame ranges as `no-map`.
    w.write_bytes(b"reserved-memory {\n  #address-cells = <2>;\n  #size-cells = <2>;\n  ranges;\n")?;
    w.write_bytes(b"  microkit-rootserver {\n    reg = <")?;
    w.write_hex_u64(policy.rootserver_phys_start >> 32)?;
    w.write_bytes(b" ")?;
    w.write_hex_u64(policy.rootserver_phys_start & 0xffff_ffff)?;
    w.write_bytes(b" ")?;
    w.write_hex_u64(root_span >> 32)?;
    w.write_bytes(b" ")?;
    w.write_hex_u64(root_span & 0xffff_ffff)?;
    w.write_bytes(b">;\n    no-map;\n  };\n")?;
    for (idx, pr) in policy.protected_ranges.iter().enumerate() {
        w.write_bytes(b"  ")?;
        w.write_bytes(pr.class.dtb_label())?;
        w.write_bytes(b"-")?;
        w.write_dec_u64(idx as u64)?;
        w.write_bytes(b" {\n    reg = <")?;
        w.write_hex_u64(pr.base_paddr >> 32)?;
        w.write_bytes(b" ")?;
        w.write_hex_u64(pr.base_paddr & 0xffff_ffff)?;
        w.write_bytes(b" ")?;
        w.write_hex_u64(pr.size >> 32)?;
        w.write_bytes(b" ")?;
        w.write_hex_u64(pr.size & 0xffff_ffff)?;
        w.write_bytes(b">;\n    no-map;\n  };\n")?;
    }
    w.write_bytes(b"};\n")?;

    // Per-device `iommus = <&iommu0 0x<stream_id>>;` bindings.
    for st in policy.streams {
        w.write_bytes(st.role.dtb_prefix())?;
        w.write_bytes(b"_s")?;
        w.write_dec_u64(st.stream_id.0 as u64)?;
        w.write_bytes(b" {\n  iommus = <&iommu0 ")?;
        w.write_hex_u64(st.stream_id.0 as u64)?;
        w.write_bytes(b">;\n  obend,owner-pd = \"")?;
        w.write_bytes(st.owner_pd.expected_name())?;
        w.write_bytes(b"\";\n  obend,region-count = <")?;
        w.write_dec_u64(st.regions.len() as u64)?;
        w.write_bytes(b">;\n};\n")?;
    }

    Ok(w.written())
}
