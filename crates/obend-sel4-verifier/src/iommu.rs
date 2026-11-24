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
    /// - `CameraCsi2` may only have `WriteOnly` DMA on `CameraRing` (matches Lean `roleRegionPermAllowed`!).
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
                | (
                    Self::Gpu,
                    DmaRegionKind::DisplayFramebuffer,
                    IoPerm::ReadOnly
                )
                | (Self::Gpu, DmaRegionKind::GpuScratchPool, _)
                | (
                    Self::CameraCsi2,
                    DmaRegionKind::CameraRing,
                    IoPerm::WriteOnly
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
    StaleOrForeignArenaEpoch,
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
    ReservedIpcVaddrCollision { stream_id: u32, iova: u64 },
}

fn ranges_overlap(a_start: u64, a_len: u64, b_start: u64, b_len: u64) -> Option<bool> {
    let a_end = a_start.checked_add(a_len)?;
    let b_end = b_start.checked_add(b_len)?;
    Some(!(a_end <= b_start || b_end <= a_start))
}

fn range_contains(
    outer_start: u64,
    outer_len: u64,
    inner_start: u64,
    inner_len: u64,
) -> Option<bool> {
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
    let mut s = Cshake256::customized(SMMU_MANIFEST_DOMAIN);
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

    s.finalize_32()
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
            if ranges_overlap(reg.paddr, reg.size, policy.rootserver_phys_start, root_span)
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
                if ranges_overlap(reg.iova, reg.size, other_reg.iova, other_reg.size)
                    .unwrap_or(true)
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
        return Err(EmitError::InvalidPolicy(
            IommuRefusal::RootServerSpanMismatch,
        ));
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
    w.write_bytes(
        b"reserved-memory {\n  #address-cells = <2>;\n  #size-cells = <2>;\n  ranges;\n",
    )?;
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

// ============================================================================
// Hardware-Real SMMUv3 / RISC-V IOMMU Descriptors, 4-Level Stage-2 Radix
// Page-Table Arena & Walker, and Stateful IOTLB / CMD_TLBI Epoch Safety
// ============================================================================

/// Maximum 48-bit Stage-2 Input/Output Physical Address limit (`2^48` bytes = 256 TiB).
pub const SMMUV3_ADDR_LIMIT_48BIT: u64 = 1u64 << 48;
/// Maximum linear StreamID table capacity in `RadixTableArena` (`STRTAB_BASE_CFG.LOG2SIZE = 7`).
pub const MAX_STREAM_TABLE_ENTRIES: usize = 128;
/// Maximum compiled contiguous DMA region span records in `RadixTableArena`.
pub const MAX_COMPILED_REGIONS: usize = 64;
/// Maximum protected physical ranges tracked inside `RadixTableArena` across epochs.
pub const MAX_PROTECTED_RANGES: usize = 32;
/// Maximum declared peripheral streams tracked inside `RadixTableArena` across epochs.
pub const MAX_DECLARED_STREAMS: usize = 64;

// Arm SMMUv3 Stream Table Entry (IHI 0070 §5.2) 512-bit (`8 × u64`) bit positions:
const STE_W0_V: u64 = 1 << 0;
const STE_W0_CONFIG_SHIFT: u32 = 1;
const STE_W0_CONFIG_MASK: u64 = 0b111 << STE_W0_CONFIG_SHIFT;
/// `Config = 0b000`: Abort all incoming traffic (`V=0` unmapped stream).
pub const STE_CONFIG_ABORT: u64 = 0b000;
/// `Config = 0b110`: Stage-1 bypassed, Stage-2 translation enabled.
pub const STE_CONFIG_S2_TRANSLATE: u64 = 0b110;
/// `EATS` sits in Word 1 `[29:28]` = global STE bits `[93:92]` (IHI 0070 §3.9 / §5.2; distinct from `S2VMID[143:128]`).
/// `0b00` forbids SMMU-issued PCIe ATS Translation Completions; paired with platform `SMMU_CR0.ATSCHK=1`
/// and Root Port ACS blocking untranslated/spoofed Translated TLPs.
const STE_W1_EATS_SHIFT: u32 = 28;
const STE_W1_EATS_MASK: u64 = 0b11 << STE_W1_EATS_SHIFT;
const STE_W2_S2VMID_MASK: u64 = 0xffff; // global [143:128]
const STE_W2_S2T0SZ_SHIFT: u32 = 32; // global [165:160]
const STE_W2_S2T0SZ_MASK: u64 = 0x3f << STE_W2_S2T0SZ_SHIFT;
const STE_W2_S2SL0_SHIFT: u32 = 38; // global [167:166]
const STE_W2_S2SL0_MASK: u64 = 0b11 << STE_W2_S2SL0_SHIFT;
const STE_W2_S2TG_SHIFT: u32 = 46; // global [175:174]
const STE_W2_S2TG_MASK: u64 = 0b11 << STE_W2_S2TG_SHIFT;
const STE_W2_S2PS_SHIFT: u32 = 48; // global [178:176]
const STE_W2_S2PS_MASK: u64 = 0b111 << STE_W2_S2PS_SHIFT;
const STE_W2_S2AA64_BIT: u64 = 1 << 51; // global [179]
const STE_W2_S2S_BIT: u64 = 1 << 57; // global [185]: 0 = terminate on fault (no stall hang)
const STE_W2_S2R_BIT: u64 = 1 << 58; // global [186]: 1 = record fault event
const STE_W2_ALLOWED_MASK: u64 = STE_W2_S2VMID_MASK
    | STE_W2_S2T0SZ_MASK
    | STE_W2_S2SL0_MASK
    | STE_W2_S2TG_MASK
    | STE_W2_S2PS_MASK
    | STE_W2_S2AA64_BIT
    | STE_W2_S2S_BIT
    | STE_W2_S2R_BIT;
/// `S2TTB[243:196]` occupies Word 3 `[51:4]`; for 48-bit 4KiB-aligned L0 root, bits `[47:12]` are active.
const STE_W3_S2TTB_FIELD_MASK: u64 = 0x000f_ffff_ffff_fff0;
const STE_W3_S2TTB_48BIT_4K_MASK: u64 = 0x0000_ffff_ffff_f000;

/// Bit-accurate 512-bit (`64`-byte, `[u64; 8]`) Armv8 SMMUv3 Stream Table Entry (`STE`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(64))]
pub struct SmmuV3Ste {
    pub words: [u64; 8],
}

/// Decoded architectural meaning of a validated `SmmuV3Ste`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedSmmuV3Ste {
    Abort,
    Stage2Translate { vmid: u16, s2ttb_paddr: u64 },
}

/// Exact hardware STE validation / `C_BAD_STE` fault reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SteDecodeError {
    MalformedAbortEntry,
    ForbiddenConfigMode(u8),
    PcieAtsBypassEnabled(u8),
    NonZeroWord1Reserved,
    InvalidVmidZero,
    InvalidS2T0Sz(u8),
    InvalidS2Sl0(u8),
    InvalidS2Tg(u8),
    InvalidS2Ps(u8),
    S2Aa64Disabled,
    StallWithoutHandler,
    FaultRecordDisabled,
    NonZeroWord2Reserved,
    UnalignedOrOutOfRangeS2Ttb(u64),
    NonZeroUpperWords,
}

impl SmmuV3Ste {
    /// Canonical `V=0, Config=0b000` abort STE for unmapped `StreamId`s (`FaultOnUnmappedStream`).
    pub const ABORT: Self = Self { words: [0u64; 8] };

    /// Pack a Stage-2-only 48-bit 4-level (`4 KiB` granule) Armv8 SMMUv3 STE.
    pub const fn pack_stage2(vmid: u16, s2ttb_paddr: u64) -> Result<Self, SteDecodeError> {
        if vmid == 0 {
            return Err(SteDecodeError::InvalidVmidZero);
        }
        if s2ttb_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (s2ttb_paddr & 0xfff) != 0 {
            return Err(SteDecodeError::UnalignedOrOutOfRangeS2Ttb(s2ttb_paddr));
        }
        let w0 = STE_W0_V | (STE_CONFIG_S2_TRANSLATE << STE_W0_CONFIG_SHIFT);
        let w1 = 0u64; // EATS[93:92] = 0b00 (ATS strictly forbidden)
        let w2 = (vmid as u64)
            | (16u64 << STE_W2_S2T0SZ_SHIFT)
            | (0b10u64 << STE_W2_S2SL0_SHIFT)
            | (0b00u64 << STE_W2_S2TG_SHIFT)
            | (0b101u64 << STE_W2_S2PS_SHIFT)
            | STE_W2_S2AA64_BIT
            | STE_W2_S2R_BIT;
        let w3 = s2ttb_paddr & STE_W3_S2TTB_48BIT_4K_MASK;
        Ok(Self {
            words: [w0, w1, w2, w3, 0, 0, 0, 0],
        })
    }

    /// Strict hardware STE decoder (`C_BAD_STE` check).
    pub const fn decode(&self) -> Result<DecodedSmmuV3Ste, SteDecodeError> {
        let w0 = self.words[0];
        let w1 = self.words[1];
        let w2 = self.words[2];
        let w3 = self.words[3];
        if (w0 & STE_W0_V) == 0 {
            if w0 == 0
                && w1 == 0
                && w2 == 0
                && w3 == 0
                && self.words[4] == 0
                && self.words[5] == 0
                && self.words[6] == 0
                && self.words[7] == 0
            {
                return Ok(DecodedSmmuV3Ste::Abort);
            }
            return Err(SteDecodeError::MalformedAbortEntry);
        }
        let cfg = ((w0 & STE_W0_CONFIG_MASK) >> STE_W0_CONFIG_SHIFT) as u8;
        if cfg != (STE_CONFIG_S2_TRANSLATE as u8) {
            return Err(SteDecodeError::ForbiddenConfigMode(cfg));
        }
        if (w0 & !(STE_W0_V | STE_W0_CONFIG_MASK)) != 0 {
            return Err(SteDecodeError::ForbiddenConfigMode(cfg));
        }
        let eats = ((w1 & STE_W1_EATS_MASK) >> STE_W1_EATS_SHIFT) as u8;
        if eats != 0 {
            return Err(SteDecodeError::PcieAtsBypassEnabled(eats));
        }
        if w1 != 0 {
            return Err(SteDecodeError::NonZeroWord1Reserved);
        }
        if (w2 & !STE_W2_ALLOWED_MASK) != 0 {
            return Err(SteDecodeError::NonZeroWord2Reserved);
        }
        let vmid = (w2 & STE_W2_S2VMID_MASK) as u16;
        if vmid == 0 {
            return Err(SteDecodeError::InvalidVmidZero);
        }
        let t0sz = ((w2 & STE_W2_S2T0SZ_MASK) >> STE_W2_S2T0SZ_SHIFT) as u8;
        if t0sz != 16 {
            return Err(SteDecodeError::InvalidS2T0Sz(t0sz));
        }
        let sl0 = ((w2 & STE_W2_S2SL0_MASK) >> STE_W2_S2SL0_SHIFT) as u8;
        if sl0 != 0b10 {
            return Err(SteDecodeError::InvalidS2Sl0(sl0));
        }
        let tg = ((w2 & STE_W2_S2TG_MASK) >> STE_W2_S2TG_SHIFT) as u8;
        if tg != 0b00 {
            return Err(SteDecodeError::InvalidS2Tg(tg));
        }
        let ps = ((w2 & STE_W2_S2PS_MASK) >> STE_W2_S2PS_SHIFT) as u8;
        if ps != 0b101 {
            return Err(SteDecodeError::InvalidS2Ps(ps));
        }
        if (w2 & STE_W2_S2AA64_BIT) == 0 {
            return Err(SteDecodeError::S2Aa64Disabled);
        }
        if (w2 & STE_W2_S2S_BIT) != 0 {
            return Err(SteDecodeError::StallWithoutHandler);
        }
        if (w2 & STE_W2_S2R_BIT) == 0 {
            return Err(SteDecodeError::FaultRecordDisabled);
        }
        if (w3 & !STE_W3_S2TTB_FIELD_MASK) != 0 {
            return Err(SteDecodeError::UnalignedOrOutOfRangeS2Ttb(w3));
        }
        let s2ttb_paddr = w3 & STE_W3_S2TTB_FIELD_MASK;
        if s2ttb_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (s2ttb_paddr & 0xfff) != 0 {
            return Err(SteDecodeError::UnalignedOrOutOfRangeS2Ttb(s2ttb_paddr));
        }
        if self.words[4] != 0 || self.words[5] != 0 || self.words[6] != 0 || self.words[7] != 0 {
            return Err(SteDecodeError::NonZeroUpperWords);
        }
        Ok(DecodedSmmuV3Ste::Stage2Translate { vmid, s2ttb_paddr })
    }

    pub fn to_le_bytes(&self) -> [u8; 64] {
        let mut out = [0u8; 64];
        for (i, &w) in self.words.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        out
    }

    pub fn from_le_bytes(bytes: &[u8; 64]) -> Self {
        let mut words = [0u64; 8];
        for (i, slot) in words.iter_mut().enumerate() {
            let off = 8 * i;
            *slot = u64::from_le_bytes([
                bytes[off],
                bytes[off + 1],
                bytes[off + 2],
                bytes[off + 3],
                bytes[off + 4],
                bytes[off + 5],
                bytes[off + 6],
                bytes[off + 7],
            ]);
        }
        Self { words }
    }
}

// RISC-V IOMMU v1.0 §3.1 Base-Format Device-Context (`32`-byte, `[u64; 4]`) constants:
const RISCV_DC_TC_V: u64 = 1 << 0;
const RISCV_DC_TC_EN_ATS: u64 = 1 << 1;
const RISCV_DC_TC_EN_PRI: u64 = 1 << 2;
const RISCV_DC_IOHGATP_MODE_SHIFT: u32 = 60;
const RISCV_DC_IOHGATP_MODE_SV48X4: u64 = 9;
const RISCV_DC_IOHGATP_GSCID_SHIFT: u32 = 44;
const RISCV_DC_IOHGATP_PPN_MASK: u64 = 0x0000_0fff_ffff_ffff;

/// Bit-accurate 256-bit (`32`-byte, `[u64; 4]`) RISC-V IOMMU Base-Format Device Directory Entry (`DC`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(32))]
pub struct RiscvDdtEntry {
    pub words: [u64; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedRiscvDdte {
    Abort,
    Sv48x4Translate { gscid: u16, root_paddr: u64 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DdteDecodeError {
    MalformedAbortEntry,
    PcieAtsOrPriEnabled,
    UnsupportedTcFlags,
    BareBypassOrInvalidMode(u8),
    InvalidGscidZero,
    UnalignedOrOutOfRangeRoot(u64),
    Stage1NotBare,
}

impl RiscvDdtEntry {
    pub const ABORT: Self = Self { words: [0u64; 4] };

    pub const fn pack_sv48x4(gscid: u16, root_paddr: u64) -> Result<Self, DdteDecodeError> {
        if gscid == 0 {
            return Err(DdteDecodeError::InvalidGscidZero);
        }
        // RISC-V `Sv48x4` G-stage root table is `16 KiB` (`4 * 4 KiB`), requiring `PPN[1:0] == 0`!
        if root_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (root_paddr & 0x3fff) != 0 {
            return Err(DdteDecodeError::UnalignedOrOutOfRangeRoot(root_paddr));
        }
        let tc = RISCV_DC_TC_V;
        let iohgatp = (RISCV_DC_IOHGATP_MODE_SV48X4 << RISCV_DC_IOHGATP_MODE_SHIFT)
            | ((gscid as u64) << RISCV_DC_IOHGATP_GSCID_SHIFT)
            | ((root_paddr >> 12) & RISCV_DC_IOHGATP_PPN_MASK);
        Ok(Self {
            words: [tc, iohgatp, 0, 0],
        })
    }

    pub const fn decode(&self) -> Result<DecodedRiscvDdte, DdteDecodeError> {
        let [tc, iohgatp, ta, fsc] = self.words;
        if (tc & RISCV_DC_TC_V) == 0 {
            if tc == 0 && iohgatp == 0 && ta == 0 && fsc == 0 {
                return Ok(DecodedRiscvDdte::Abort);
            }
            return Err(DdteDecodeError::MalformedAbortEntry);
        }
        if (tc & (RISCV_DC_TC_EN_ATS | RISCV_DC_TC_EN_PRI)) != 0 {
            return Err(DdteDecodeError::PcieAtsOrPriEnabled);
        }
        if tc != RISCV_DC_TC_V {
            return Err(DdteDecodeError::UnsupportedTcFlags);
        }
        let mode = (iohgatp >> RISCV_DC_IOHGATP_MODE_SHIFT) as u8;
        if mode != (RISCV_DC_IOHGATP_MODE_SV48X4 as u8) {
            return Err(DdteDecodeError::BareBypassOrInvalidMode(mode));
        }
        let gscid = ((iohgatp >> RISCV_DC_IOHGATP_GSCID_SHIFT) & 0xffff) as u16;
        if gscid == 0 {
            return Err(DdteDecodeError::InvalidGscidZero);
        }
        let root_paddr = (iohgatp & RISCV_DC_IOHGATP_PPN_MASK) << 12;
        if root_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (root_paddr & 0x3fff) != 0 {
            return Err(DdteDecodeError::UnalignedOrOutOfRangeRoot(root_paddr));
        }
        if ta != 0 || fsc != 0 {
            return Err(DdteDecodeError::Stage1NotBare);
        }
        Ok(DecodedRiscvDdte::Sv48x4Translate { gscid, root_paddr })
    }
}

// Armv8-A VMSAv8-64 Stage-2 64-bit descriptor encodings (`4 KiB` granule, 48-bit OA):
pub const STAGE2_DESC_INVALID: u64 = 0b00;
pub const STAGE2_DESC_BLOCK: u64 = 0b01;
pub const STAGE2_DESC_TABLE_OR_PAGE: u64 = 0b11;
pub const STAGE2_S2AP_SHIFT: u32 = 6;
pub const STAGE2_S2AP_MASK: u64 = 0b11 << STAGE2_S2AP_SHIFT;
pub const STAGE2_AF_BIT: u64 = 1 << 10;
/// Armv8 Stage-2 `XN[54:53] = 0b10`: Execute-Never at ALL privilege levels (`EL1 & EL0`, DDI 0487 Table D5-35).
pub const STAGE2_S2XN_SHIFT: u32 = 53;
pub const STAGE2_S2XN_MASK: u64 = 0b11 << STAGE2_S2XN_SHIFT;
pub const STAGE2_S2XN_ALL: u64 = 0b10 << STAGE2_S2XN_SHIFT;
pub const STAGE2_OA_4K_MASK: u64 = 0x0000_ffff_ffff_f000;
pub const STAGE2_OA_2M_MASK: u64 = 0x0000_ffff_ffe0_0000;

impl IoPerm {
    pub const fn to_s2ap(self) -> u64 {
        match self {
            Self::ReadOnly => 0b01,
            Self::WriteOnly => 0b10,
            Self::ReadWrite => 0b11,
        }
    }

    pub const fn from_s2ap(bits: u64) -> Option<Self> {
        match bits {
            0b01 => Some(Self::ReadOnly),
            0b10 => Some(Self::WriteOnly),
            0b11 => Some(Self::ReadWrite),
            _ => None,
        }
    }
}

/// Encode an L0/L1/L2 Stage-2 table descriptor pointing to a `4 KiB`-aligned next-level table.
pub const fn encode_stage2_table_desc(next_table_paddr: u64) -> Option<u64> {
    if next_table_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (next_table_paddr & 0xfff) != 0 {
        return None;
    }
    Some((next_table_paddr & STAGE2_OA_4K_MASK) | STAGE2_DESC_TABLE_OR_PAGE)
}

/// Encode an L2 Stage-2 `2 MiB` block descriptor (`[1:0]=0b01`, `OA[47:21]`, `AF[10]=1`, `S2XN[54:53]=0b10`).
pub const fn encode_stage2_block2m_desc(oa_paddr: u64, perm: IoPerm) -> Option<u64> {
    if oa_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (oa_paddr & (PAGE_SIZE_2M - 1)) != 0 {
        return None;
    }
    Some(
        STAGE2_S2XN_ALL
            | (oa_paddr & STAGE2_OA_2M_MASK)
            | STAGE2_AF_BIT
            | (perm.to_s2ap() << STAGE2_S2AP_SHIFT)
            | STAGE2_DESC_BLOCK,
    )
}

/// Encode an L3 Stage-2 `4 KiB` page descriptor (`[1:0]=0b11`, `OA[47:12]`, `AF[10]=1`, `S2XN[54:53]=0b10`).
pub const fn encode_stage2_page4k_desc(oa_paddr: u64, perm: IoPerm) -> Option<u64> {
    if oa_paddr >= SMMUV3_ADDR_LIMIT_48BIT || (oa_paddr & 0xfff) != 0 {
        return None;
    }
    Some(
        STAGE2_S2XN_ALL
            | (oa_paddr & STAGE2_OA_4K_MASK)
            | STAGE2_AF_BIT
            | (perm.to_s2ap() << STAGE2_S2AP_SHIFT)
            | STAGE2_DESC_TABLE_OR_PAGE,
    )
}

/// Decode an L0 or L1 Stage-2 table descriptor (`0b01` block descriptors at L0/L1 are rejected).
pub const fn decode_stage2_table_desc(desc: u64) -> Option<u64> {
    if (desc & 0b11) != STAGE2_DESC_TABLE_OR_PAGE {
        return None;
    }
    if (desc & !(STAGE2_OA_4K_MASK | 0b11)) != 0 {
        return None;
    }
    Some(desc & STAGE2_OA_4K_MASK)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedL2Desc {
    Invalid,
    Table { next_table_paddr: u64 },
    Block2MiB { oa_paddr: u64, perm: IoPerm },
}

/// Decode an L2 Stage-2 descriptor (`0b00` invalid, `0b11` L3 table pointer, `0b01` `2 MiB` block).
pub const fn decode_stage2_l2_desc(desc: u64) -> Option<DecodedL2Desc> {
    if desc == 0 {
        return Some(DecodedL2Desc::Invalid);
    }
    match desc & 0b11 {
        STAGE2_DESC_TABLE_OR_PAGE => match decode_stage2_table_desc(desc) {
            Some(next_table_paddr) => Some(DecodedL2Desc::Table { next_table_paddr }),
            None => None,
        },
        STAGE2_DESC_BLOCK => {
            if (desc & STAGE2_AF_BIT) == 0 || (desc & STAGE2_S2XN_MASK) != STAGE2_S2XN_ALL {
                return None;
            }
            // Bits [20:12] MUST be zero on a 2 MiB L2 block descriptor!
            let allowed =
                STAGE2_S2XN_MASK | STAGE2_OA_2M_MASK | STAGE2_AF_BIT | STAGE2_S2AP_MASK | 0b11;
            if (desc & !allowed) != 0 {
                return None;
            }
            let Some(perm) = IoPerm::from_s2ap((desc & STAGE2_S2AP_MASK) >> STAGE2_S2AP_SHIFT)
            else {
                return None;
            };
            Some(DecodedL2Desc::Block2MiB {
                oa_paddr: desc & STAGE2_OA_2M_MASK,
                perm,
            })
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedL3Desc {
    Invalid,
    Page4KiB { oa_paddr: u64, perm: IoPerm },
}

/// Decode an L3 Stage-2 descriptor (`0b00` invalid, `0b11` `4 KiB` page; `0b01` is reserved/fault at L3!).
pub const fn decode_stage2_l3_desc(desc: u64) -> Option<DecodedL3Desc> {
    if desc == 0 {
        return Some(DecodedL3Desc::Invalid);
    }
    if (desc & 0b11) != STAGE2_DESC_TABLE_OR_PAGE {
        return None;
    }
    if (desc & STAGE2_AF_BIT) == 0 || (desc & STAGE2_S2XN_MASK) != STAGE2_S2XN_ALL {
        return None;
    }
    let allowed = STAGE2_S2XN_MASK | STAGE2_OA_4K_MASK | STAGE2_AF_BIT | STAGE2_S2AP_MASK | 0b11;
    if (desc & !allowed) != 0 {
        return None;
    }
    let Some(perm) = IoPerm::from_s2ap((desc & STAGE2_S2AP_MASK) >> STAGE2_S2AP_SHIFT) else {
        return None;
    };
    Some(DecodedL3Desc::Page4KiB {
        oa_paddr: desc & STAGE2_OA_4K_MASK,
        perm,
    })
}

/// Error returned when compiling a `ChokepointIommuPolicy` into a concrete `RadixTableArena`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RadixBuildError {
    UnsupportedArchForSmmuV3Radix(IommuArch),
    InvalidPolicy(IommuRefusal),
    UnalignedOrOutOfRangeArenaBase(u64),
    ArenaNotInKernelPageTableRange {
        arena_base: u64,
        arena_bytes: u64,
    },
    StreamIdExceedsLinearTable {
        stream_id: u32,
        max_entries: usize,
    },
    TooManyCompiledRegions {
        count: usize,
        max_regions: usize,
    },
    AddressExceeds48Bit {
        stream_id: u32,
        addr: u64,
    },
    ArenaTableCapacityExhausted {
        max_tables: usize,
    },
    DescriptorCollision {
        stream_id: u32,
        iova: u64,
    },
    CoalescableAdjacentRegions {
        stream_id: u32,
        first_iova: u64,
        second_iova: u64,
    },
    TooManyProtectedRanges {
        count: usize,
        max_ranges: usize,
    },
    TooManyDeclaredStreams {
        count: usize,
        max_streams: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompiledStreamMeta {
    stream_id: StreamId,
    role: DeviceRole,
    owner_pd: ChokepointRole,
    region_count: usize,
}

impl CompiledStreamMeta {
    const ZERO: Self = Self {
        stream_id: StreamId::UNASSIGNED,
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        region_count: 0,
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompiledRegionSpan {
    stream_id: StreamId,
    role: DeviceRole,
    owner_pd: ChokepointRole,
    region: DmaRegion,
    iova_end: u64,
}

impl CompiledRegionSpan {
    const ZERO: Self = Self {
        stream_id: StreamId::UNASSIGNED,
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        region: DmaRegion {
            iova: 0,
            paddr: 0,
            size: 0,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadOnly,
            kind: DmaRegionKind::IngressRing,
        },
        iova_end: 0,
    };
}

/// Deterministic `#![no_std]` static-arena 4-level (`L0 -> L1 -> L2 -> L3`) Armv8 VMSAv8-64
/// Stage-2 radix table materializer + linear SMMUv3 Stream Table placed in `KernelPageTable` frames.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RadixTableArena<const MAX_TABLES: usize> {
    default_deny: bool,
    built_epoch: u64,
    policy_digest: Digest,
    rootserver_phys_start: u64,
    rootserver_phys_end: u64,
    arena_base_paddr: u64,
    stream_table_frames: usize,
    cmdq_frames: usize,
    used_tables: usize,
    active_stream_limit: usize,
    stream_table: [SmmuV3Ste; MAX_STREAM_TABLE_ENTRIES],
    table_paddrs: [u64; MAX_TABLES],
    tables: [[u64; 512]; MAX_TABLES],
    protected_ranges: [ProtectedFrameRange; MAX_PROTECTED_RANGES],
    protected_range_count: usize,
    compiled_streams: [CompiledStreamMeta; MAX_DECLARED_STREAMS],
    compiled_stream_count: usize,
    outbox_spans: [(u64, u64); MAX_COMPILED_REGIONS],
    outbox_span_count: usize,
    region_spans: [CompiledRegionSpan; MAX_COMPILED_REGIONS],
    region_span_count: usize,
}

impl<const MAX_TABLES: usize> RadixTableArena<MAX_TABLES> {
    pub const fn default_deny(&self) -> bool {
        self.default_deny
    }

    pub const fn built_epoch(&self) -> u64 {
        self.built_epoch
    }

    pub const fn policy_digest(&self) -> &Digest {
        &self.policy_digest
    }

    pub const fn arena_base_paddr(&self) -> u64 {
        self.arena_base_paddr
    }

    pub const fn active_stream_limit(&self) -> usize {
        self.active_stream_limit
    }

    pub const fn used_tables(&self) -> usize {
        self.used_tables
    }

    pub const fn stream_table(&self) -> &[SmmuV3Ste; MAX_STREAM_TABLE_ENTRIES] {
        &self.stream_table
    }
    fn alloc_table(&mut self) -> Result<(usize, u64), RadixBuildError> {
        if self.used_tables >= MAX_TABLES {
            return Err(RadixBuildError::ArenaTableCapacityExhausted {
                max_tables: MAX_TABLES,
            });
        }
        let idx = self.used_tables;
        let frame_idx = (self.stream_table_frames + self.cmdq_frames + idx) as u64;
        let paddr = self
            .arena_base_paddr
            .checked_add(frame_idx.checked_mul(PAGE_SIZE_4K).ok_or(
                RadixBuildError::UnalignedOrOutOfRangeArenaBase(self.arena_base_paddr),
            )?)
            .ok_or(RadixBuildError::UnalignedOrOutOfRangeArenaBase(
                self.arena_base_paddr,
            ))?;
        if paddr
            .checked_add(PAGE_SIZE_4K)
            .is_none_or(|end| end > SMMUV3_ADDR_LIMIT_48BIT)
        {
            return Err(RadixBuildError::UnalignedOrOutOfRangeArenaBase(paddr));
        }
        self.used_tables += 1;
        self.table_paddrs[idx] = paddr;
        self.tables[idx] = [0u64; 512];
        Ok((idx, paddr))
    }

    fn lookup_table_index(&self, paddr: u64) -> Option<usize> {
        let pt_base = self.pt_base_paddr()?;
        if paddr < pt_base || !(paddr - pt_base).is_multiple_of(PAGE_SIZE_4K) {
            return None;
        }
        let idx = usize::try_from((paddr - pt_base) / PAGE_SIZE_4K).ok()?;
        if idx < self.used_tables && self.table_paddrs[idx] == paddr {
            Some(idx)
        } else {
            None
        }
    }

    pub const fn pt_base_paddr(&self) -> Option<u64> {
        let header_frames = (self.stream_table_frames + self.cmdq_frames) as u64;
        let Some(off) = header_frames.checked_mul(PAGE_SIZE_4K) else {
            return None;
        };
        self.arena_base_paddr.checked_add(off)
    }

    pub const fn total_allocated_frames(&self) -> usize {
        self.stream_table_frames + self.cmdq_frames + self.used_tables
    }

    pub const fn total_allocated_bytes(&self) -> u64 {
        (self.total_allocated_frames() as u64) * PAGE_SIZE_4K
    }

    /// Return the 16-bit Stage-2 VMID assigned to `stream_id` in the active SMMUv3 Stream Table.
    pub fn stream_vmid(&self, stream_id: StreamId) -> Option<u16> {
        let idx = stream_id.0 as usize;
        if idx >= self.active_stream_limit {
            return None;
        }
        match self.stream_table[idx].decode().ok()? {
            DecodedSmmuV3Ste::Stage2Translate { vmid, .. } => Some(vmid),
            DecodedSmmuV3Ste::Abort => None,
        }
    }

    fn ensure_child_table(
        &mut self,
        parent_idx: usize,
        slot: usize,
        stream_id: u32,
        iova: u64,
    ) -> Result<usize, RadixBuildError> {
        let cur = self.tables[parent_idx][slot];
        if cur == 0 {
            let (child_idx, child_pa) = self.alloc_table()?;
            let desc = encode_stage2_table_desc(child_pa)
                .ok_or(RadixBuildError::DescriptorCollision { stream_id, iova })?;
            self.tables[parent_idx][slot] = desc;
            Ok(child_idx)
        } else {
            let child_pa = decode_stage2_table_desc(cur)
                .ok_or(RadixBuildError::DescriptorCollision { stream_id, iova })?;
            self.lookup_table_index(child_pa)
                .ok_or(RadixBuildError::DescriptorCollision { stream_id, iova })
        }
    }

    /// Construct an empty default-abort arena (`#![no_std]`, `const`-friendly for static/stack reuse).
    pub const fn empty() -> Self {
        Self {
            default_deny: true,
            built_epoch: 0,
            policy_digest: [0u8; 32],
            rootserver_phys_start: 0,
            rootserver_phys_end: 0,
            arena_base_paddr: 0,
            stream_table_frames: 0,
            cmdq_frames: 0,
            used_tables: 0,
            active_stream_limit: 0,
            stream_table: [SmmuV3Ste::ABORT; MAX_STREAM_TABLE_ENTRIES],
            table_paddrs: [0u64; MAX_TABLES],
            tables: [[0u64; 512]; MAX_TABLES],
            protected_ranges: [ProtectedFrameRange {
                class: ProtectedFrameClass::CommitPrivate,
                base_paddr: 0,
                size: 0,
            }; MAX_PROTECTED_RANGES],
            protected_range_count: 0,
            compiled_streams: [CompiledStreamMeta::ZERO; MAX_DECLARED_STREAMS],
            compiled_stream_count: 0,
            outbox_spans: [(0u64, 0u64); MAX_COMPILED_REGIONS],
            outbox_span_count: 0,
            region_spans: [CompiledRegionSpan::ZERO; MAX_COMPILED_REGIONS],
            region_span_count: 0,
        }
    }

    fn clear_in_place(&mut self) {
        self.default_deny = true;
        self.built_epoch = 0;
        self.policy_digest = [0u8; 32];
        self.rootserver_phys_start = 0;
        self.rootserver_phys_end = 0;
        self.arena_base_paddr = 0;
        self.stream_table_frames = 0;
        self.cmdq_frames = 0;
        self.used_tables = 0;
        self.active_stream_limit = 0;
        self.stream_table.fill(SmmuV3Ste::ABORT);
        self.table_paddrs.fill(0);
        for tbl in &mut self.tables {
            tbl.fill(0);
        }
        self.protected_ranges.fill(ProtectedFrameRange {
            class: ProtectedFrameClass::CommitPrivate,
            base_paddr: 0,
            size: 0,
        });
        self.protected_range_count = 0;
        self.compiled_streams.fill(CompiledStreamMeta::ZERO);
        self.compiled_stream_count = 0;
        self.outbox_spans.fill((0, 0));
        self.outbox_span_count = 0;
        self.region_spans.fill(CompiledRegionSpan::ZERO);
        self.region_span_count = 0;
    }

    /// Deterministically compile a verified `ChokepointIommuPolicy` in-place into `self`
    /// without allocating large `[[u64; 512]; MAX_TABLES]` stack temporaries.
    /// Any failure leaves `self` completely disarmed (`active_stream_limit == 0`, all STEs `ABORT`).
    pub fn compile_into(
        &mut self,
        policy: &ChokepointIommuPolicy<'_>,
        arena_base_paddr: u64,
    ) -> Result<(), RadixBuildError> {
        let res = self.compile_into_inner(policy, arena_base_paddr);
        if res.is_err() {
            self.clear_in_place();
        }
        res
    }

    fn compile_into_inner(
        &mut self,
        policy: &ChokepointIommuPolicy<'_>,
        arena_base_paddr: u64,
    ) -> Result<(), RadixBuildError> {
        if policy.arch != IommuArch::ArmSmmuV3 {
            return Err(RadixBuildError::UnsupportedArchForSmmuV3Radix(policy.arch));
        }
        let policy_digest = verify_iommu_policy(policy).map_err(RadixBuildError::InvalidPolicy)?;
        if !arena_base_paddr.is_multiple_of(PAGE_SIZE_4K)
            || arena_base_paddr >= SMMUV3_ADDR_LIMIT_48BIT
        {
            return Err(RadixBuildError::UnalignedOrOutOfRangeArenaBase(
                arena_base_paddr,
            ));
        }

        let mut max_sid = 0usize;
        for st in policy.streams {
            let sid = st.stream_id.0 as usize;
            if sid >= MAX_STREAM_TABLE_ENTRIES {
                return Err(RadixBuildError::StreamIdExceedsLinearTable {
                    stream_id: st.stream_id.0,
                    max_entries: MAX_STREAM_TABLE_ENTRIES,
                });
            }
            if sid > max_sid {
                max_sid = sid;
            }
        }
        // Arm IHI 0070 §6.3.25 `SMMU_STRTAB_BASE`: linear Stream Table size is `2^LOG2SIZE * 64` bytes
        // and the base address MUST be naturally aligned to `st_bytes`!
        let active_stream_limit = (max_sid + 1).max(64).next_power_of_two();
        let st_bytes = active_stream_limit * 64;
        if !arena_base_paddr.is_multiple_of(st_bytes as u64) {
            return Err(RadixBuildError::UnalignedOrOutOfRangeArenaBase(
                arena_base_paddr,
            ));
        }
        let stream_table_frames = st_bytes.div_ceil(PAGE_SIZE_4K as usize);
        let cmdq_frames = 1usize;

        if policy.protected_ranges.len() > MAX_PROTECTED_RANGES {
            return Err(RadixBuildError::TooManyProtectedRanges {
                count: policy.protected_ranges.len(),
                max_ranges: MAX_PROTECTED_RANGES,
            });
        }
        if policy.streams.len() > MAX_DECLARED_STREAMS {
            return Err(RadixBuildError::TooManyDeclaredStreams {
                count: policy.streams.len(),
                max_streams: MAX_DECLARED_STREAMS,
            });
        }

        self.clear_in_place();
        self.default_deny = policy.default_deny_unmapped;
        self.policy_digest = policy_digest;
        self.rootserver_phys_start = policy.rootserver_phys_start;
        self.rootserver_phys_end = policy.rootserver_phys_end;
        self.arena_base_paddr = arena_base_paddr;
        self.stream_table_frames = stream_table_frames;
        self.cmdq_frames = cmdq_frames;
        self.active_stream_limit = active_stream_limit;
        for (idx, pr) in policy.protected_ranges.iter().enumerate() {
            self.protected_ranges[idx] = *pr;
        }
        self.protected_range_count = policy.protected_ranges.len();

        for (s_idx, st) in policy.streams.iter().enumerate() {
            self.compiled_streams[s_idx] = CompiledStreamMeta {
                stream_id: st.stream_id,
                role: st.role,
                owner_pd: st.owner_pd,
                region_count: st.regions.len(),
            };
            self.compiled_stream_count += 1;
            for (idx_a, reg_a) in st.regions.iter().enumerate() {
                for (idx_b, reg_b) in st.regions.iter().enumerate() {
                    if idx_a != idx_b
                        && reg_a.iova.checked_add(reg_a.size) == Some(reg_b.iova)
                        && reg_a.paddr.checked_add(reg_a.size) == Some(reg_b.paddr)
                        && reg_a.perm == reg_b.perm
                    {
                        return Err(RadixBuildError::CoalescableAdjacentRegions {
                            stream_id: st.stream_id.0,
                            first_iova: reg_a.iova,
                            second_iova: reg_b.iova,
                        });
                    }
                }
            }
            // Stable per-StreamID non-zero 16-bit S2VMID/GSCID (`1 <= sid < MAX_STREAM_TABLE_ENTRIES`).
            let vmid = st.stream_id.0 as u16;
            let (l0_idx, l0_pa) = self.alloc_table()?;
            for reg in st.regions {
                let reg_iova_end =
                    reg.iova
                        .checked_add(reg.size)
                        .ok_or(RadixBuildError::AddressExceeds48Bit {
                            stream_id: st.stream_id.0,
                            addr: reg.iova,
                        })?;
                let reg_paddr_end = reg.paddr.checked_add(reg.size).ok_or(
                    RadixBuildError::AddressExceeds48Bit {
                        stream_id: st.stream_id.0,
                        addr: reg.paddr,
                    },
                )?;
                if reg_iova_end > SMMUV3_ADDR_LIMIT_48BIT {
                    return Err(RadixBuildError::AddressExceeds48Bit {
                        stream_id: st.stream_id.0,
                        addr: reg_iova_end,
                    });
                }
                if reg_paddr_end > SMMUV3_ADDR_LIMIT_48BIT {
                    return Err(RadixBuildError::AddressExceeds48Bit {
                        stream_id: st.stream_id.0,
                        addr: reg_paddr_end,
                    });
                }
                if self.region_span_count >= MAX_COMPILED_REGIONS {
                    return Err(RadixBuildError::TooManyCompiledRegions {
                        count: self.region_span_count + 1,
                        max_regions: MAX_COMPILED_REGIONS,
                    });
                }
                self.region_spans[self.region_span_count] = CompiledRegionSpan {
                    stream_id: st.stream_id,
                    role: st.role,
                    owner_pd: st.owner_pd,
                    region: *reg,
                    iova_end: reg_iova_end,
                };
                self.region_span_count += 1;
                if reg.kind == DmaRegionKind::EgressOutboxRing {
                    self.outbox_spans[self.outbox_span_count] = (reg.paddr, reg.size);
                    self.outbox_span_count += 1;
                }

                let step = reg.granule.bytes();
                let mut off = 0u64;
                while off < reg.size {
                    let cur_iova = reg.iova + off;
                    let cur_pa = reg.paddr + off;
                    let i0 = ((cur_iova >> 39) & 0x1ff) as usize;
                    let i1 = ((cur_iova >> 30) & 0x1ff) as usize;
                    let i2 = ((cur_iova >> 21) & 0x1ff) as usize;
                    let i3 = ((cur_iova >> 12) & 0x1ff) as usize;

                    let l1_idx = self.ensure_child_table(l0_idx, i0, st.stream_id.0, cur_iova)?;
                    let l2_idx = self.ensure_child_table(l1_idx, i1, st.stream_id.0, cur_iova)?;

                    match reg.granule {
                        PageGranule::Huge2MiB => {
                            if self.tables[l2_idx][i2] != 0 {
                                return Err(RadixBuildError::DescriptorCollision {
                                    stream_id: st.stream_id.0,
                                    iova: cur_iova,
                                });
                            }
                            self.tables[l2_idx][i2] = encode_stage2_block2m_desc(cur_pa, reg.perm)
                                .ok_or(RadixBuildError::AddressExceeds48Bit {
                                    stream_id: st.stream_id.0,
                                    addr: cur_pa,
                                })?;
                        }
                        PageGranule::Page4KiB => {
                            let l3_idx =
                                self.ensure_child_table(l2_idx, i2, st.stream_id.0, cur_iova)?;
                            if self.tables[l3_idx][i3] != 0 {
                                return Err(RadixBuildError::DescriptorCollision {
                                    stream_id: st.stream_id.0,
                                    iova: cur_iova,
                                });
                            }
                            self.tables[l3_idx][i3] = encode_stage2_page4k_desc(cur_pa, reg.perm)
                                .ok_or(
                                RadixBuildError::AddressExceeds48Bit {
                                    stream_id: st.stream_id.0,
                                    addr: cur_pa,
                                },
                            )?;
                        }
                    }
                    off += step;
                }
            }
            let sid_idx = st.stream_id.0 as usize;
            self.stream_table[sid_idx] = SmmuV3Ste::pack_stage2(vmid, l0_pa)
                .map_err(|_| RadixBuildError::UnalignedOrOutOfRangeArenaBase(l0_pa))?;
        }

        // Enforce that the entire allocated SMMU arena (Stream Table + CmdQ + all L0..L3 tables)
        // sits strictly inside a `KernelPageTable` protected physical range!
        let total_bytes = self.total_allocated_bytes();
        let covered_by_kernel_pt = policy.protected_ranges.iter().any(|pr| {
            pr.class == ProtectedFrameClass::KernelPageTable
                && range_contains(pr.base_paddr, pr.size, arena_base_paddr, total_bytes)
                    .unwrap_or(false)
        });
        if !covered_by_kernel_pt {
            return Err(RadixBuildError::ArenaNotInKernelPageTableRange {
                arena_base: arena_base_paddr,
                arena_bytes: total_bytes,
            });
        }

        Ok(())
    }

    /// Deterministically compile a verified `ArmSmmuV3` `ChokepointIommuPolicy` into real 512-entry `4 KiB`
    /// Armv8 Stage-2 radix page tables + linear SMMUv3 Stream Table + Command Queue frame inside
    /// `ProtectedFrameClass::KernelPageTable` physical frames starting at `arena_base_paddr`.
    pub fn compile(
        policy: &ChokepointIommuPolicy<'_>,
        arena_base_paddr: u64,
    ) -> Result<Self, RadixBuildError> {
        let mut arena = Self::empty();
        arena.compile_into(policy, arena_base_paddr)?;
        Ok(arena)
    }

    /// Returns `true` iff every Stream Table frame, Command Queue frame, and L0..L3 radix page-table
    /// frame lies inside `KernelPageTable` protected memory and is 100% unreachable by peripheral DMA.
    pub fn smmu_tables_dma_unreachable(&self, policy: &ChokepointIommuPolicy<'_>) -> bool {
        let total_bytes = self.total_allocated_bytes();
        let in_kernel_pt = policy.protected_ranges.iter().any(|pr| {
            pr.class == ProtectedFrameClass::KernelPageTable
                && range_contains(pr.base_paddr, pr.size, self.arena_base_paddr, total_bytes)
                    .unwrap_or(false)
        });
        in_kernel_pt && policy.physical_range_is_dma_unreachable(self.arena_base_paddr, total_bytes)
    }

    fn lookup_region_span(&self, stream_id: StreamId, iova: u64) -> Option<CompiledRegionSpan> {
        let mut idx = 0usize;
        while idx < self.region_span_count {
            let sp = self.region_spans[idx];
            if sp.stream_id == stream_id && iova >= sp.region.iova && iova < sp.iova_end {
                return Some(sp);
            }
            idx += 1;
        }
        None
    }

    fn table_identical_at(&self, other: &Self, paddr: u64) -> Option<usize> {
        let idx_a = self.lookup_table_index(paddr)?;
        let idx_b = other.lookup_table_index(paddr)?;
        if self.tables[idx_a] == other.tables[idx_b] {
            Some(idx_a)
        } else {
            None
        }
    }

    /// Returns `true` iff `stream_id`'s STE AND every reachable L0..L3 physical radix table address
    /// and 512-word descriptor array are bit-for-bit identical between `self` and `other`.
    pub fn stream_subtree_identical(&self, other: &Self, stream_id: StreamId) -> bool {
        let sid_idx = stream_id.0 as usize;
        let ste_a = if sid_idx < self.active_stream_limit {
            self.stream_table[sid_idx]
        } else {
            SmmuV3Ste::ABORT
        };
        let ste_b = if sid_idx < other.active_stream_limit {
            other.stream_table[sid_idx]
        } else {
            SmmuV3Ste::ABORT
        };
        if ste_a != ste_b {
            return false;
        }
        match ste_a.decode() {
            Ok(DecodedSmmuV3Ste::Abort) => true,
            Ok(DecodedSmmuV3Ste::Stage2Translate { s2ttb_paddr, .. }) => {
                let Some(l0_idx) = self.table_identical_at(other, s2ttb_paddr) else {
                    return false;
                };
                for &d0 in &self.tables[l0_idx] {
                    if let Some(l1_pa) = decode_stage2_table_desc(d0) {
                        let Some(l1_idx) = self.table_identical_at(other, l1_pa) else {
                            return false;
                        };
                        for &d1 in &self.tables[l1_idx] {
                            if let Some(l2_pa) = decode_stage2_table_desc(d1) {
                                let Some(l2_idx) = self.table_identical_at(other, l2_pa) else {
                                    return false;
                                };
                                for &d2 in &self.tables[l2_idx] {
                                    if let Some(DecodedL2Desc::Table {
                                        next_table_paddr: l3_pa,
                                    }) = decode_stage2_l2_desc(d2)
                                    {
                                        if self.table_identical_at(other, l3_pa).is_none() {
                                            return false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                true
            }
            Err(_) => false,
        }
    }

    /// Pure hardware 4-level (`L0 -> L1 -> L2 -> L3`) bit-packed descriptor walk for a single IOVA.
    /// Returns `(leaf_base_oa, translated_paddr, granule, perm)`.
    pub fn walk_single_iova(
        &self,
        l0_paddr: u64,
        stream_id: StreamId,
        iova: u64,
    ) -> Result<(u64, u64, PageGranule, IoPerm), DmaFault> {
        if iova >= SMMUV3_ADDR_LIMIT_48BIT {
            return Err(DmaFault::UnmappedIova {
                stream_id: stream_id.0,
                iova,
            });
        }
        let l0_idx = self
            .lookup_table_index(l0_paddr)
            .ok_or(DmaFault::UnmappedIova {
                stream_id: stream_id.0,
                iova,
            })?;
        let d0 = self.tables[l0_idx][((iova >> 39) & 0x1ff) as usize];
        let l1_pa = decode_stage2_table_desc(d0).ok_or(DmaFault::UnmappedIova {
            stream_id: stream_id.0,
            iova,
        })?;

        let l1_idx = self
            .lookup_table_index(l1_pa)
            .ok_or(DmaFault::UnmappedIova {
                stream_id: stream_id.0,
                iova,
            })?;
        let d1 = self.tables[l1_idx][((iova >> 30) & 0x1ff) as usize];
        let l2_pa = decode_stage2_table_desc(d1).ok_or(DmaFault::UnmappedIova {
            stream_id: stream_id.0,
            iova,
        })?;

        let l2_idx = self
            .lookup_table_index(l2_pa)
            .ok_or(DmaFault::UnmappedIova {
                stream_id: stream_id.0,
                iova,
            })?;
        let d2 = self.tables[l2_idx][((iova >> 21) & 0x1ff) as usize];
        match decode_stage2_l2_desc(d2).ok_or(DmaFault::UnmappedIova {
            stream_id: stream_id.0,
            iova,
        })? {
            DecodedL2Desc::Invalid => Err(DmaFault::UnmappedIova {
                stream_id: stream_id.0,
                iova,
            }),
            DecodedL2Desc::Block2MiB { oa_paddr, perm } => {
                let off = iova & (PAGE_SIZE_2M - 1);
                Ok((oa_paddr, oa_paddr + off, PageGranule::Huge2MiB, perm))
            }
            DecodedL2Desc::Table { next_table_paddr } => {
                let l3_idx =
                    self.lookup_table_index(next_table_paddr)
                        .ok_or(DmaFault::UnmappedIova {
                            stream_id: stream_id.0,
                            iova,
                        })?;
                let d3 = self.tables[l3_idx][((iova >> 12) & 0x1ff) as usize];
                match decode_stage2_l3_desc(d3).ok_or(DmaFault::UnmappedIova {
                    stream_id: stream_id.0,
                    iova,
                })? {
                    DecodedL3Desc::Invalid => Err(DmaFault::UnmappedIova {
                        stream_id: stream_id.0,
                        iova,
                    }),
                    DecodedL3Desc::Page4KiB { oa_paddr, perm } => {
                        let off = iova & (PAGE_SIZE_4K - 1);
                        Ok((oa_paddr, oa_paddr + off, PageGranule::Page4KiB, perm))
                    }
                }
            }
        }
    }

    pub fn walk_smmuv3_stage2(
        &self,
        stream_id: StreamId,
        iova: u64,
        len: u64,
        access: DmaAccess,
    ) -> Result<DmaTranslation, DmaFault> {
        walk_smmuv3_stage2(self, stream_id, iova, len, access)
    }
}

/// Hardware-real Armv8 SMMUv3 Stage-2 page-table walker:
/// 1. Validates global `default_deny`, non-zero length, non-wrapping `[iova, iova + len)`, and `StreamId`.
/// 2. Fetches & decodes the 512-bit `SmmuV3Ste` (`EATS[93:92]=0`, `S2S=0`, `S2R=1`, `S2TTB[243:196]`).
/// 3. Walks the 4-level (`9+9+9+9+12`) bit-packed radix descriptor tree across every leaf covering
///    `[iova, iova + len)`, verifying physical contiguity, `AF=1`, `S2XN=0b10`, and `S2AP` permissions
///    purely from hardware PTEs (`== translate_dma` for non-coalescable manifests).
pub fn walk_smmuv3_stage2<const MAX_TABLES: usize>(
    arena: &RadixTableArena<MAX_TABLES>,
    stream_id: StreamId,
    iova: u64,
    len: u64,
    access: DmaAccess,
) -> Result<DmaTranslation, DmaFault> {
    if !arena.default_deny {
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
    let sid_idx = stream_id.0 as usize;
    if sid_idx >= arena.active_stream_limit {
        return Err(DmaFault::UnmappedStream {
            stream_id: stream_id.0,
        });
    }

    let l0_paddr = match arena.stream_table[sid_idx].decode() {
        Ok(DecodedSmmuV3Ste::Stage2Translate { s2ttb_paddr, .. }) => s2ttb_paddr,
        Ok(DecodedSmmuV3Ste::Abort) | Err(_) => {
            return Err(DmaFault::UnmappedStream {
                stream_id: stream_id.0,
            });
        }
    };

    // Walk first leaf at `iova` through the 4-level radix descriptor tree.
    let (_first_oa, first_paddr, first_granule, first_perm) =
        arena.walk_single_iova(l0_paddr, stream_id, iova)?;
    if req_end > SMMUV3_ADDR_LIMIT_48BIT {
        return Err(DmaFault::CrossRegionSpanDenied {
            stream_id: stream_id.0,
            iova,
            len,
        });
    }

    // Walk every subsequent leaf page/block touched by `[iova, req_end)` in the 4-level radix tree
    // FIRST, enforcing physical contiguity and uniform permissions directly from the 64-bit PTEs!
    let first_gran_bytes = first_granule.bytes();
    let mut next_leaf_iova = (iova & !(first_gran_bytes - 1)).saturating_add(first_gran_bytes);
    while next_leaf_iova < req_end {
        let Ok((leaf_oa, leaf_pa, leaf_gran, leaf_perm)) =
            arena.walk_single_iova(l0_paddr, stream_id, next_leaf_iova)
        else {
            return Err(DmaFault::CrossRegionSpanDenied {
                stream_id: stream_id.0,
                iova,
                len,
            });
        };
        let expected_pa = first_paddr
            .checked_add(next_leaf_iova - iova)
            .ok_or(DmaFault::AddressWrap)?;
        if leaf_pa != expected_pa || leaf_oa != leaf_pa || leaf_perm != first_perm {
            return Err(DmaFault::CrossRegionSpanDenied {
                stream_id: stream_id.0,
                iova,
                len,
            });
        }
        next_leaf_iova = next_leaf_iova.saturating_add(leaf_gran.bytes());
    }

    if !first_perm.allows(access) {
        return Err(DmaFault::PermissionDenied {
            stream_id: stream_id.0,
            iova,
            perm: first_perm,
            access,
        });
    }
    if first_paddr.checked_add(len).is_none() {
        return Err(DmaFault::AddressWrap);
    }

    let kind = arena
        .lookup_region_span(stream_id, iova)
        .map_or(DmaRegionKind::IngressRing, |sp| sp.region.kind);

    Ok(DmaTranslation {
        paddr: first_paddr,
        len,
        kind,
        perm: first_perm,
    })
}

// ============================================================================
// SMMUv3 128-Bit Command Queue (`CMD_CFGI_STE`, `CMD_TLBI_S2_IPA`, `CMD_SYNC`)
// & Stateful IOTLB Epoch Invalidation Engine
// ============================================================================

pub const CMD_OP_CFGI_STE: u8 = 0x03;
pub const CMD_OP_TLBI_S12_VMALL: u8 = 0x28;
pub const CMD_OP_TLBI_S2_IPA: u8 = 0x2a;
pub const CMD_OP_SYNC: u8 = 0x46;

/// 128-bit (`[u64; 2]`) Arm SMMUv3 Command Queue Entry (IHI 0070 §4.1 / §4.3.1 / §4.4.3.1–2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmmuCmd {
    CfgiSte { stream_id: StreamId, leaf: bool },
    TlbiS2Ipa { vmid: u16, ipa: u64, leaf: bool },
    TlbiS12Vmall { vmid: u16 },
    Sync,
}

impl SmmuCmd {
    /// Pack into 128-bit SMMUv3 command-queue format (`VMID` in Word 0 `[47:32]`, `[63:48]` & `[31:8]` RES0).
    pub const fn pack(self) -> Option<[u64; 2]> {
        match self {
            Self::CfgiSte { stream_id, leaf } => {
                let q0 = (CMD_OP_CFGI_STE as u64) | ((stream_id.0 as u64) << 32);
                let q1 = if leaf { 1 } else { 0 };
                Some([q0, q1])
            }
            Self::TlbiS2Ipa { vmid, ipa, leaf } => {
                if ipa >= SMMUV3_ADDR_LIMIT_48BIT || (ipa & 0xfff) != 0 {
                    return None;
                }
                let q0 = (CMD_OP_TLBI_S2_IPA as u64) | ((vmid as u64) << 32);
                let q1 = (ipa & STAGE2_OA_4K_MASK) | if leaf { 1 } else { 0 };
                Some([q0, q1])
            }
            Self::TlbiS12Vmall { vmid } => {
                let q0 = (CMD_OP_TLBI_S12_VMALL as u64) | ((vmid as u64) << 32);
                Some([q0, 0])
            }
            Self::Sync => Some([CMD_OP_SYNC as u64, 0]),
        }
    }

    pub const fn decode(words: [u64; 2]) -> Option<Self> {
        let [q0, q1] = words;
        match (q0 & 0xff) as u8 {
            CMD_OP_CFGI_STE => {
                if (q0 & 0xffff_ff00) != 0 || (q1 & !1) != 0 {
                    return None;
                }
                Some(Self::CfgiSte {
                    stream_id: StreamId((q0 >> 32) as u32),
                    leaf: (q1 & 1) != 0,
                })
            }
            CMD_OP_TLBI_S2_IPA => {
                if (q0 & 0xffff_0000_ffff_ff00) != 0 {
                    return None;
                }
                let allowed_q1 = STAGE2_OA_4K_MASK | 1;
                if (q1 & !allowed_q1) != 0 {
                    return None;
                }
                Some(Self::TlbiS2Ipa {
                    vmid: ((q0 >> 32) & 0xffff) as u16,
                    ipa: q1 & STAGE2_OA_4K_MASK,
                    leaf: (q1 & 1) != 0,
                })
            }
            CMD_OP_TLBI_S12_VMALL => {
                if (q0 & 0xffff_0000_ffff_ff00) != 0 || q1 != 0 {
                    return None;
                }
                Some(Self::TlbiS12Vmall {
                    vmid: ((q0 >> 32) & 0xffff) as u16,
                })
            }
            CMD_OP_SYNC => {
                if (q0 & !0xff) != 0 || q1 != 0 {
                    return None;
                }
                Some(Self::Sync)
            }
            _ => None,
        }
    }
}

/// Hardware IOTLB cached Stage-2 translation entry.
/// Remains live across software table edits until invalidated by `CMD_TLBI_*` + `CMD_SYNC`!
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CachedTlbiEntry {
    pub live: bool,
    pub stream_id: StreamId,
    pub vmid: u16,
    pub iova_base: u64,
    pub paddr_base: u64,
    pub granule: PageGranule,
    pub perm: IoPerm,
    pub kind: DmaRegionKind,
    pub installed_epoch: u64,
}

impl CachedTlbiEntry {
    pub const EMPTY: Self = Self {
        live: false,
        stream_id: StreamId::UNASSIGNED,
        vmid: 0,
        iova_base: 0,
        paddr_base: 0,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadOnly,
        kind: DmaRegionKind::IngressRing,
        installed_epoch: 0,
    };
}

/// Failure modes for epoch DMA unmap/reassignment when IOTLB invalidation is incomplete.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TlbiReconfigError {
    MalformedCommandWords([u64; 2]),
    CommandQueueFull,
    EpochOverflow,
    StaleOrMismatchedOldArena,
    TargetRegionUnchanged,
    UnsyncedCommandsPending,
    InvalidOldStreamVmidOrRegion {
        stream_id: u32,
        claimed_vmid: u16,
    },
    MissingCfgiSte {
        stream_id: u32,
    },
    MissingWalkCacheTlbiVmall {
        vmid: u16,
    },
    MissingCoveringTlbiS2Ipa {
        vmid: u16,
        iova: u64,
    },
    UnannouncedMappingChange {
        stream_id: u32,
        iova_base: u64,
    },
    ProtectedRangeWeakened {
        class: ProtectedFrameClass,
        base_paddr: u64,
    },
    OutboxFrameWriteEscalation {
        paddr: u64,
    },
    StaleIotlbEntrySurvived {
        stream_id: u32,
        iova_base: u64,
    },
    RadixRebuildFailed(RadixBuildError),
}

/// Stateful `#![no_std]` SMMUv3 IOTLB + Command Queue epoch engine.
pub struct SmmuIotlbEngine<const MAX_IOTLB: usize, const MAX_CMDS: usize> {
    epoch: u64,
    active_policy_digest: Option<Digest>,
    active_arena_base: Option<u64>,
    pinned_rootserver_span: Option<(u64, u64)>,
    pinned_protected_ranges: [ProtectedFrameRange; MAX_PROTECTED_RANGES],
    pinned_protected_count: usize,
    pinned_outbox_spans: [(u64, u64); MAX_COMPILED_REGIONS],
    pinned_outbox_count: usize,
    iotlb: [CachedTlbiEntry; MAX_IOTLB],
    pending_cmds: [SmmuCmd; MAX_CMDS],
    pending_len: usize,
    synced_cmds: [SmmuCmd; MAX_CMDS],
    synced_batches: [u32; MAX_CMDS],
    synced_len: usize,
    sync_batch_id: u32,
    refill_cursor: usize,
}

impl<const MAX_IOTLB: usize, const MAX_CMDS: usize> Default
    for SmmuIotlbEngine<MAX_IOTLB, MAX_CMDS>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const MAX_IOTLB: usize, const MAX_CMDS: usize> SmmuIotlbEngine<MAX_IOTLB, MAX_CMDS> {
    pub const fn new() -> Self {
        Self {
            epoch: 0,
            active_policy_digest: None,
            active_arena_base: None,
            pinned_rootserver_span: None,
            pinned_protected_ranges: [ProtectedFrameRange {
                class: ProtectedFrameClass::CommitPrivate,
                base_paddr: 0,
                size: 0,
            }; MAX_PROTECTED_RANGES],
            pinned_protected_count: 0,
            pinned_outbox_spans: [(0u64, 0u64); MAX_COMPILED_REGIONS],
            pinned_outbox_count: 0,
            iotlb: [CachedTlbiEntry::EMPTY; MAX_IOTLB],
            pending_cmds: [SmmuCmd::Sync; MAX_CMDS],
            pending_len: 0,
            synced_cmds: [SmmuCmd::Sync; MAX_CMDS],
            synced_batches: [0u32; MAX_CMDS],
            synced_len: 0,
            sync_batch_id: 0,
            refill_cursor: 0,
        }
    }

    fn arena_matches_pinned<const MAX_TABLES: usize>(
        &self,
        arena: &RadixTableArena<MAX_TABLES>,
    ) -> bool {
        if arena.built_epoch != self.epoch || arena.active_stream_limit == 0 {
            return false;
        }
        if let Some(pinned) = &self.active_policy_digest {
            if !ct_eq_digest(pinned, &arena.policy_digest) {
                return false;
            }
            if self.active_arena_base != Some(arena.arena_base_paddr) {
                return false;
            }
            if self.pinned_rootserver_span
                != Some((arena.rootserver_phys_start, arena.rootserver_phys_end))
            {
                return false;
            }
            if arena.protected_ranges[..arena.protected_range_count]
                != self.pinned_protected_ranges[..self.pinned_protected_count]
            {
                return false;
            }
            if arena.outbox_spans[..arena.outbox_span_count]
                != self.pinned_outbox_spans[..self.pinned_outbox_count]
            {
                return false;
            }
        }
        true
    }

    fn pin_arena_state<const MAX_TABLES: usize>(&mut self, arena: &RadixTableArena<MAX_TABLES>) {
        self.active_policy_digest = Some(arena.policy_digest);
        self.active_arena_base = Some(arena.arena_base_paddr);
        self.pinned_rootserver_span =
            Some((arena.rootserver_phys_start, arena.rootserver_phys_end));
        self.pinned_protected_ranges[..arena.protected_range_count]
            .copy_from_slice(&arena.protected_ranges[..arena.protected_range_count]);
        self.pinned_protected_count = arena.protected_range_count;
        self.pinned_outbox_spans[..arena.outbox_span_count]
            .copy_from_slice(&arena.outbox_spans[..arena.outbox_span_count]);
        self.pinned_outbox_count = arena.outbox_span_count;
    }

    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    pub const fn active_arena_base(&self) -> Option<u64> {
        self.active_arena_base
    }

    pub const fn active_policy_digest(&self) -> Option<&Digest> {
        self.active_policy_digest.as_ref()
    }

    pub const fn iotlb_entries(&self) -> &[CachedTlbiEntry; MAX_IOTLB] {
        &self.iotlb
    }

    pub const fn has_unsynced_cmds(&self) -> bool {
        self.pending_len > 0
    }

    pub fn live_entry_count(&self) -> usize {
        self.iotlb.iter().filter(|e| e.live).count()
    }

    /// Decode a 128-bit (`[u64; 2]`) SMMUv3 command-queue entry and submit it to the queue.
    pub fn submit_raw_cmd(&mut self, words: [u64; 2]) -> Result<(), TlbiReconfigError> {
        let cmd = SmmuCmd::decode(words).ok_or(TlbiReconfigError::MalformedCommandWords(words))?;
        self.submit_cmd(cmd)
    }

    /// Enqueue a command into the SMMU command queue (`PROD` advances).
    /// Per Arm IHI 0070 §4.3.1 / §4.4.3:
    /// - `CMD_CFGI_STE` invalidates ONLY the STE configuration cache (NOT VMID-tagged IOTLB entries!).
    /// - `CMD_TLBI_S2_IPA` / `CMD_TLBI_S12_VMALL` evict matching VMID-tagged IOTLB entries upon `CMD_SYNC`.
    pub fn submit_cmd(&mut self, cmd: SmmuCmd) -> Result<(), TlbiReconfigError> {
        if let SmmuCmd::Sync = cmd {
            if self.synced_len.saturating_add(self.pending_len) > MAX_CMDS {
                return Err(TlbiReconfigError::CommandQueueFull);
            }
            for idx in 0..self.pending_len {
                let c = self.pending_cmds[idx];
                match c {
                    SmmuCmd::TlbiS12Vmall { vmid } => {
                        for slot in &mut self.iotlb {
                            if slot.live && slot.vmid == vmid {
                                *slot = CachedTlbiEntry::EMPTY;
                            }
                        }
                    }
                    SmmuCmd::TlbiS2Ipa { vmid, ipa, leaf: _ } => {
                        for slot in &mut self.iotlb {
                            if slot.live && slot.vmid == vmid {
                                let gran = slot.granule.bytes();
                                if ranges_overlap(slot.iova_base, gran, ipa, PAGE_SIZE_4K)
                                    .unwrap_or(false)
                                {
                                    *slot = CachedTlbiEntry::EMPTY;
                                }
                            }
                        }
                    }
                    // IHI 0070 §4.3.1: `CMD_CFGI_STE` flushes STE config cache only, NOT IOTLB!
                    SmmuCmd::CfgiSte { .. } | SmmuCmd::Sync => {}
                }
                self.synced_cmds[self.synced_len] = c;
                self.synced_batches[self.synced_len] = self.sync_batch_id;
                self.synced_len += 1;
            }
            self.pending_len = 0;
            self.sync_batch_id = self.sync_batch_id.saturating_add(1);
            Ok(())
        } else {
            if self.pending_len >= MAX_CMDS {
                return Err(TlbiReconfigError::CommandQueueFull);
            }
            self.pending_cmds[self.pending_len] = cmd;
            self.pending_len += 1;
            Ok(())
        }
    }

    /// Translate a DMA transaction using the hardware IOTLB FIRST (exposing stale-IOTLB hits if
    /// page tables changed without `CMD_TLBI_S2_IPA` + `CMD_SYNC`!), falling back to
    /// `walk_smmuv3_stage2` and refilling the IOTLB on a miss.
    pub fn translate_with_iotlb<const MAX_TABLES: usize>(
        &mut self,
        arena: &RadixTableArena<MAX_TABLES>,
        stream_id: StreamId,
        iova: u64,
        len: u64,
        access: DmaAccess,
    ) -> Result<DmaTranslation, DmaFault> {
        if !arena.default_deny {
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
        // Reject retired old-epoch OR foreign/different-base/different-history arenas BEFORE consulting IOTLB!
        if !self.arena_matches_pinned(arena) {
            return Err(DmaFault::StaleOrForeignArenaEpoch);
        }

        // 1. Check live IOTLB cache first (exposing any un-invalidated stale IOTLB entry!).
        for entry in &self.iotlb {
            if !entry.live || entry.stream_id != stream_id {
                continue;
            }
            let gran_bytes = entry.granule.bytes();
            if iova >= entry.iova_base && req_end <= entry.iova_base + gran_bytes {
                if !entry.perm.allows(access) {
                    return Err(DmaFault::PermissionDenied {
                        stream_id: stream_id.0,
                        iova,
                        perm: entry.perm,
                        access,
                    });
                }
                let off = iova - entry.iova_base;
                return Ok(DmaTranslation {
                    paddr: entry.paddr_base + off,
                    len,
                    kind: entry.kind,
                    perm: entry.perm,
                });
            }
        }

        // 2. Miss: walk the active 4-level radix arena, invalidate stale `synced_cmds` proof window,
        //    and install into IOTLB.
        let tr = walk_smmuv3_stage2(arena, stream_id, iova, len, access)?;
        self.pin_arena_state(arena);
        self.synced_len = 0;
        self.sync_batch_id = 0;
        if let Some(vmid) = arena.stream_vmid(stream_id) {
            let sid_idx = stream_id.0 as usize;
            let l0_pa = match arena.stream_table[sid_idx].decode() {
                Ok(DecodedSmmuV3Ste::Stage2Translate { s2ttb_paddr, .. }) => s2ttb_paddr,
                _ => 0,
            };
            if let Ok((leaf_oa, _pa, gran, perm)) = arena.walk_single_iova(l0_pa, stream_id, iova) {
                let gran_bytes = gran.bytes();
                let iova_base = iova & !(gran_bytes - 1);
                let new_entry = CachedTlbiEntry {
                    live: true,
                    stream_id,
                    vmid,
                    iova_base,
                    paddr_base: leaf_oa,
                    granule: gran,
                    perm,
                    kind: tr.kind,
                    installed_epoch: self.epoch,
                };
                if let Some(free_slot) = self.iotlb.iter_mut().find(|s| !s.live) {
                    *free_slot = new_entry;
                } else if MAX_IOTLB > 0 {
                    let slot_idx = self.refill_cursor % MAX_IOTLB;
                    self.refill_cursor = self.refill_cursor.wrapping_add(1);
                    self.iotlb[slot_idx] = new_entry;
                }
            }
        }
        Ok(tr)
    }

    /// Arm IHI 0070 §3.21.1.1 two-barrier completion ordering: returns the slice of synced commands
    /// executed in a strictly LATER `CMD_SYNC` batch AFTER `CMD_CFGI_STE(stream_id, leaf=false)` + `CMD_SYNC`!
    fn synced_after_cfgi(&self, stream_id: StreamId) -> Option<&[SmmuCmd]> {
        let pos = self.synced_cmds[..self.synced_len].iter().position(
            |c| matches!(c, SmmuCmd::CfgiSte { stream_id: s, leaf: false } if *s == stream_id),
        )?;
        let cfgi_batch = self.synced_batches[pos];
        let mut after = pos + 1;
        while after < self.synced_len && self.synced_batches[after] <= cfgi_batch {
            after += 1;
        }
        Some(&self.synced_cmds[after..self.synced_len])
    }

    fn synced_has_cfgi(&self, stream_id: StreamId) -> bool {
        self.synced_cmds[..self.synced_len]
            .iter()
            .any(|c| matches!(c, SmmuCmd::CfgiSte { stream_id: s, leaf: false } if *s == stream_id))
    }

    fn synced_cfgi_precedes_vmall(&self, stream_id: StreamId, vmid: u16) -> bool {
        let Some(tail) = self.synced_after_cfgi(stream_id) else {
            return false;
        };
        tail.iter()
            .any(|c| matches!(c, SmmuCmd::TlbiS12Vmall { vmid: v } if *v == vmid))
    }

    fn synced_cfgi_precedes_tlbi_page(
        &self,
        stream_id: StreamId,
        vmid: u16,
        page_iova: u64,
    ) -> bool {
        let Some(tail) = self.synced_after_cfgi(stream_id) else {
            return false;
        };
        tail.iter().any(|c| match *c {
            SmmuCmd::TlbiS12Vmall { vmid: v } => v == vmid,
            SmmuCmd::TlbiS2Ipa {
                vmid: v,
                ipa,
                leaf: false,
            } => v == vmid && ipa == page_iova,
            _ => false,
        })
    }

    /// Safely unmap or reassign `old_region` from `(stream_id, old_vmid)` in `old_arena` into
    /// `out_arena` (`new_policy`) at `epoch + 1`:
    /// - Hardware break-before-make driver sequence (Arm IHI 0070 §3.21.1.1):
    ///   (1) break/write updated STE/PTE in `KernelPageTable` RAM + `DSB ISHST`,
    ///   (2) issue `CMD_CFGI_STE(stream_id, leaf=false)` + `CMD_SYNC` (completing STE cache flush),
    ///   (3) issue covering `CMD_TLBI_S2_IPA` / `CMD_TLBI_S12_VMALL` + `CMD_SYNC` (completing IOTLB/walk-cache flush),
    ///   (4) commit `out_arena` and repurpose retired physical DMA frames ONLY after step (3) returns `Ok(())`.
    /// - Enforces cross-epoch preservation of `rootserver_phys_start..rootserver_phys_end`, all prior
    ///   `ProtectedFrameRange` spans, read-only outbox physical frames, and bidirectional whole-stream
    ///   symmetry (including empty non-target streams) + full L0..L3 `stream_subtree_identical` coherence.
    #[allow(clippy::too_many_arguments)]
    pub fn unmap_or_reassign_dma_region<const MAX_TABLES: usize>(
        &mut self,
        old_arena: &RadixTableArena<MAX_TABLES>,
        stream_id: StreamId,
        old_vmid: u16,
        old_region: &DmaRegion,
        new_policy: &ChokepointIommuPolicy<'_>,
        new_arena_base: u64,
        out_arena: &mut RadixTableArena<MAX_TABLES>,
    ) -> Result<(), TlbiReconfigError> {
        let next_epoch = self
            .epoch
            .checked_add(1)
            .ok_or(TlbiReconfigError::EpochOverflow)?;
        if !self.arena_matches_pinned(old_arena) {
            return Err(TlbiReconfigError::StaleOrMismatchedOldArena);
        }
        let old_reg_present = old_arena.region_spans[..old_arena.region_span_count]
            .iter()
            .any(|sp| sp.stream_id == stream_id && sp.region == *old_region);
        if old_arena.stream_vmid(stream_id) != Some(old_vmid)
            || !old_reg_present
            || old_region.size == 0
            || !old_region.iova.is_multiple_of(PAGE_SIZE_4K)
            || !old_region.size.is_multiple_of(PAGE_SIZE_4K)
            || old_region
                .iova
                .checked_add(old_region.size)
                .is_none_or(|end| end > SMMUV3_ADDR_LIMIT_48BIT)
        {
            return Err(TlbiReconfigError::InvalidOldStreamVmidOrRegion {
                stream_id: stream_id.0,
                claimed_vmid: old_vmid,
            });
        }
        let still_present_unchanged = new_policy
            .streams
            .iter()
            .any(|st| st.stream_id == stream_id && st.regions.contains(old_region));
        if still_present_unchanged {
            return Err(TlbiReconfigError::TargetRegionUnchanged);
        }
        if self.has_unsynced_cmds() {
            return Err(TlbiReconfigError::UnsyncedCommandsPending);
        }
        if !self.synced_has_cfgi(stream_id) {
            return Err(TlbiReconfigError::MissingCfgiSte {
                stream_id: stream_id.0,
            });
        }
        let mut off = 0u64;
        while off < old_region.size {
            let page_iova = old_region.iova + off;
            if !self.synced_cfgi_precedes_tlbi_page(stream_id, old_vmid, page_iova) {
                return Err(TlbiReconfigError::MissingCoveringTlbiS2Ipa {
                    vmid: old_vmid,
                    iova: page_iova,
                });
            }
            off += PAGE_SIZE_4K;
        }

        // Cross-epoch protected memory & outbox immutability (matching Lean `runSmmuEpochTrace`):
        if new_policy.rootserver_phys_start != old_arena.rootserver_phys_start
            || new_policy.rootserver_phys_end != old_arena.rootserver_phys_end
        {
            return Err(TlbiReconfigError::ProtectedRangeWeakened {
                class: ProtectedFrameClass::PdCodeStackCspace,
                base_paddr: old_arena.rootserver_phys_start,
            });
        }
        for old_pr in &old_arena.protected_ranges[..old_arena.protected_range_count] {
            let still_covered = new_policy.protected_ranges.iter().any(|new_pr| {
                new_pr.class == old_pr.class
                    && range_contains(
                        new_pr.base_paddr,
                        new_pr.size,
                        old_pr.base_paddr,
                        old_pr.size,
                    )
                    .unwrap_or(false)
            });
            if !still_covered {
                return Err(TlbiReconfigError::ProtectedRangeWeakened {
                    class: old_pr.class,
                    base_paddr: old_pr.base_paddr,
                });
            }
        }
        for &(ob_paddr, ob_size) in self.pinned_outbox_spans[..self.pinned_outbox_count]
            .iter()
            .chain(old_arena.outbox_spans[..old_arena.outbox_span_count].iter())
        {
            for st in new_policy.streams {
                for reg in st.regions {
                    if reg.perm.can_write()
                        && ranges_overlap(ob_paddr, ob_size, reg.paddr, reg.size).unwrap_or(true)
                    {
                        return Err(TlbiReconfigError::OutboxFrameWriteEscalation {
                            paddr: reg.paddr,
                        });
                    }
                }
            }
        }

        // Bidirectional whole-stream `onlyOldRegChanged` (including empty non-target streams!):
        for old_sm in &old_arena.compiled_streams[..old_arena.compiled_stream_count] {
            if old_sm.stream_id == stream_id {
                continue;
            }
            let exact_match = new_policy.streams.iter().any(|st| {
                st.stream_id == old_sm.stream_id
                    && st.role == old_sm.role
                    && st.owner_pd == old_sm.owner_pd
                    && st.regions.len() == old_sm.region_count
            });
            if !exact_match {
                return Err(TlbiReconfigError::UnannouncedMappingChange {
                    stream_id: old_sm.stream_id.0,
                    iova_base: 0,
                });
            }
        }
        // (a) Every compiled region in `old_arena` other than `(stream_id, *old_region)` must remain in `new_policy`.
        for sp in &old_arena.region_spans[..old_arena.region_span_count] {
            if sp.stream_id == stream_id && sp.region == *old_region {
                continue;
            }
            let preserved = new_policy.streams.iter().any(|st| {
                st.stream_id == sp.stream_id
                    && st.role == sp.role
                    && st.owner_pd == sp.owner_pd
                    && st.regions.contains(&sp.region)
            });
            if !preserved {
                return Err(TlbiReconfigError::UnannouncedMappingChange {
                    stream_id: sp.stream_id.0,
                    iova_base: sp.region.iova,
                });
            }
        }
        // (b) No non-target stream in `new_policy` may add unannounced streams, change role/owner, or add regions.
        for st in new_policy.streams {
            if st.stream_id == stream_id {
                continue;
            }
            let old_meta_match = old_arena.compiled_streams[..old_arena.compiled_stream_count]
                .iter()
                .any(|sm| {
                    sm.stream_id == st.stream_id
                        && sm.role == st.role
                        && sm.owner_pd == st.owner_pd
                        && sm.region_count == st.regions.len()
                });
            if !old_meta_match {
                return Err(TlbiReconfigError::UnannouncedMappingChange {
                    stream_id: st.stream_id.0,
                    iova_base: st.regions.first().map_or(0, |r| r.iova),
                });
            }
            for reg in st.regions {
                let existed = old_arena.region_spans[..old_arena.region_span_count]
                    .iter()
                    .any(|sp| {
                        sp.stream_id == st.stream_id
                            && sp.role == st.role
                            && sp.owner_pd == st.owner_pd
                            && sp.region == *reg
                    });
                if !existed {
                    return Err(TlbiReconfigError::UnannouncedMappingChange {
                        stream_id: st.stream_id.0,
                        iova_base: reg.iova,
                    });
                }
            }
        }

        out_arena
            .compile_into(new_policy, new_arena_base)
            .map_err(TlbiReconfigError::RadixRebuildFailed)?;

        // Monotonically retain all historical outbox physical spans across arbitrary multi-epoch
        // transitions (matching Lean `runSmmuEpochTrace`'s invariant `egressOutboxFrames`!):
        for &span in self.pinned_outbox_spans[..self.pinned_outbox_count]
            .iter()
            .chain(old_arena.outbox_spans[..old_arena.outbox_span_count].iter())
        {
            if !out_arena.outbox_spans[..out_arena.outbox_span_count].contains(&span) {
                if out_arena.outbox_span_count >= MAX_COMPILED_REGIONS {
                    out_arena.clear_in_place();
                    return Err(TlbiReconfigError::RadixRebuildFailed(
                        RadixBuildError::TooManyCompiledRegions {
                            count: out_arena.outbox_span_count + 1,
                            max_regions: MAX_COMPILED_REGIONS,
                        },
                    ));
                }
                out_arena.outbox_spans[out_arena.outbox_span_count] = span;
                out_arena.outbox_span_count += 1;
            }
        }

        // Target-stream walk-cache coherence: if `stream_id` had surviving regions (`!= old_region`) AND
        // its physical L0..L3 subtree changed, require `CMD_CFGI_STE(stream_id) -> CMD_TLBI_S12_VMALL(old_vmid)`!
        let target_has_survivors = old_arena.region_spans[..old_arena.region_span_count]
            .iter()
            .any(|sp| sp.stream_id == stream_id && sp.region != *old_region);
        if target_has_survivors
            && !old_arena.stream_subtree_identical(out_arena, stream_id)
            && !self.synced_cfgi_precedes_vmall(stream_id, old_vmid)
        {
            out_arena.clear_in_place();
            return Err(TlbiReconfigError::MissingWalkCacheTlbiVmall { vmid: old_vmid });
        }

        // Non-target streams: check full L0..L3 physical subtree identity (`stream_subtree_identical`)
        // across BOTH old and new linear stream-table limits!
        let check_limit = old_arena
            .active_stream_limit
            .max(out_arena.active_stream_limit);
        for idx in 0..check_limit {
            let sid = StreamId(idx as u32);
            if sid == stream_id {
                continue;
            }
            if !old_arena.stream_subtree_identical(out_arena, sid) {
                if !self.synced_has_cfgi(sid) {
                    out_arena.clear_in_place();
                    return Err(TlbiReconfigError::MissingCfgiSte { stream_id: sid.0 });
                }
                if let Some(other_vmid) = old_arena.stream_vmid(sid) {
                    if !self.synced_cfgi_precedes_vmall(sid, other_vmid) {
                        out_arena.clear_in_place();
                        return Err(TlbiReconfigError::MissingWalkCacheTlbiVmall {
                            vmid: other_vmid,
                        });
                    }
                }
            }
        }

        // Defense-in-depth postcondition: verify every surviving live IOTLB entry reproduces
        // identically under `out_arena`'s 4-level Stage-2 radix tables!
        for slot in &self.iotlb {
            if !slot.live {
                continue;
            }
            let req_acc = if slot.perm.can_write() {
                DmaAccess::Write
            } else {
                DmaAccess::Read
            };
            let reproduced = out_arena.stream_vmid(slot.stream_id) == Some(slot.vmid)
                && walk_smmuv3_stage2(
                    out_arena,
                    slot.stream_id,
                    slot.iova_base,
                    slot.granule.bytes(),
                    req_acc,
                )
                .is_ok_and(|tr| {
                    tr.paddr == slot.paddr_base && tr.perm == slot.perm && tr.kind == slot.kind
                });
            if !reproduced {
                out_arena.clear_in_place();
                return Err(TlbiReconfigError::StaleIotlbEntrySurvived {
                    stream_id: slot.stream_id.0,
                    iova_base: slot.iova_base,
                });
            }
        }

        self.epoch = next_epoch;
        out_arena.built_epoch = next_epoch;
        self.pin_arena_state(out_arena);
        self.synced_len = 0;
        self.sync_batch_id = 0;
        Ok(())
    }
}

#[cfg(test)]
mod whitebox_iotlb_tests {
    use super::*;

    const WB_PROT: [ProtectedFrameRange; 3] = [
        ProtectedFrameRange {
            class: ProtectedFrameClass::CommitPrivate,
            base_paddr: 0x6010_0000,
            size: PAGE_SIZE_4K,
        },
        ProtectedFrameRange {
            class: ProtectedFrameClass::PdCodeStackCspace,
            base_paddr: 0x6020_0000,
            size: 0x20_0000,
        },
        ProtectedFrameRange {
            class: ProtectedFrameClass::KernelPageTable,
            base_paddr: 0x6015_0000,
            size: 0x2_0000,
        },
    ];

    #[test]
    fn whitebox_refuses_u64_max_epoch_overflow_and_corrupted_surviving_iotlb_entry() {
        let r0 = [DmaRegion {
            iova: 0x1000_0000,
            paddr: 0x6080_0000,
            size: PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::WriteOnly,
            kind: DmaRegionKind::IngressRing,
        }];
        let r1 = [DmaRegion {
            iova: 0x1000_0000,
            paddr: 0x6080_1000,
            size: PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::WriteOnly,
            kind: DmaRegionKind::IngressRing,
        }];
        let r_persist = [DmaRegion {
            iova: 0x2000_0000,
            paddr: 0x6081_0000,
            size: PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::PersistWalPool,
        }];
        let s0 = [
            DeviceStreamBinding {
                stream_id: StreamId(0x10),
                role: DeviceRole::IngressNic,
                owner_pd: ChokepointRole::Ingress,
                regions: &r0,
            },
            DeviceStreamBinding {
                stream_id: StreamId(0x20),
                role: DeviceRole::PersistNvme,
                owner_pd: ChokepointRole::Persist,
                regions: &r_persist,
            },
        ];
        let s1 = [
            DeviceStreamBinding {
                stream_id: StreamId(0x10),
                role: DeviceRole::IngressNic,
                owner_pd: ChokepointRole::Ingress,
                regions: &r1,
            },
            s0[1],
        ];
        let pol0 = ChokepointIommuPolicy {
            arch: IommuArch::ArmSmmuV3,
            default_deny_unmapped: true,
            rootserver_phys_start: 0x6020_0000,
            rootserver_phys_end: 0x6040_0000,
            dma_pool_base: 0x6080_0000,
            dma_pool_size: 0x10_0000,
            protected_ranges: &WB_PROT,
            streams: &s0,
        };
        let pol1 = ChokepointIommuPolicy {
            streams: &s1,
            ..pol0
        };
        let mut arena0 = RadixTableArena::<16>::compile(&pol0, 0x6015_0000).unwrap();
        let mut out_arena = RadixTableArena::<16>::empty();
        let mut engine = SmmuIotlbEngine::<4, 8>::new();

        // 1. `u64::MAX` epoch wraparound is fail-closed (`EpochOverflow`)!
        engine.epoch = u64::MAX;
        arena0.built_epoch = u64::MAX;
        assert_eq!(
            engine.unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                0x10,
                &r0[0],
                &pol1,
                0x6015_0000,
                &mut out_arena,
            ),
            Err(TlbiReconfigError::EpochOverflow)
        );

        // 2. Defense-in-depth postcondition: a corrupted surviving IOTLB entry on stream `0x20`
        //    pointing to `0x6099_0000` instead of `0x6081_0000` is caught (`StaleIotlbEntrySurvived`)
        //    and leaves `out_arena` disarmed!
        engine.epoch = 0;
        arena0.built_epoch = 0;
        engine.iotlb[0] = CachedTlbiEntry {
            live: true,
            stream_id: StreamId(0x20),
            vmid: 0x20,
            iova_base: 0x2000_0000,
            paddr_base: 0x6099_0000,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::PersistWalPool,
            installed_epoch: 0,
        };
        engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(0x10),
                leaf: false,
            })
            .unwrap();
        engine.submit_cmd(SmmuCmd::Sync).unwrap();
        engine
            .submit_cmd(SmmuCmd::TlbiS2Ipa {
                vmid: 0x10,
                ipa: 0x1000_0000,
                leaf: false,
            })
            .unwrap();
        engine.submit_cmd(SmmuCmd::Sync).unwrap();
        assert_eq!(
            engine.unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                0x10,
                &r0[0],
                &pol1,
                0x6015_0000,
                &mut out_arena,
            ),
            Err(TlbiReconfigError::StaleIotlbEntrySurvived {
                stream_id: 0x20,
                iova_base: 0x2000_0000,
            })
        );
        assert_eq!(out_arena.active_stream_limit(), 0);
    }
}
