//! Four-PD seL4 Microkit Chokepoint (`ingress-pd -> commit-pd -> persist-pd [digest ack] -> tx-egress-pd`),
//! `< 10 MiB` root-server physical span budget check, per-PD disjoint CSpaces (`CAP-03`),
//! fail-closed `halted` monitor latch (`CAP-28`), and hardware-TRNG `GETRANDOM` confinement (`CAP-29`).

use super::*;

/// Hard ceiling (`10 MiB = 10,485,760` bytes) on the Microkit root-server physical memory span,
/// extrapolating the booted two-PD image's `0x60246000..0x60a05000` (`8,122,368` B ≈ `7.75 MiB`)
/// span and preventing `285 MiB` mathlib ELF collisions with Microkit 2.2.0's `0x7000_0000` loader.
pub const MAX_ROOTSERVER_SPAN_BYTES: u64 = 10 * 1024 * 1024;
/// Stock Microkit 2.2.0 loader base on QEMU `virt` (`aarch64`).
pub const STOCK_MICROKIT_LOADER_BASE: u64 = 0x7000_0000;
/// Maximum SPSC IPC / shared-memory frame size (`4 KiB`), blocking `CAP-03` unbounded `u32` OOM.
pub const MAX_IPC_FRAME_BYTES: usize = 4096;

/// Linux `aarch64` syscall numbers intercepted by the in-PD musl `__sysinfo` trap (`CAP-29`).
pub mod linux_aarch64_nr {
    pub const OPENAT: u64 = 56;
    pub const CLOSE: u64 = 57;
    pub const READ: u64 = 63;
    pub const WRITE: u64 = 64;
    pub const FSTAT: u64 = 80;
    pub const EXIT_GROUP: u64 = 94;
    pub const FUTEX: u64 = 98;
    pub const CLOCK_GETTIME: u64 = 113;
    pub const BRK: u64 = 214;
    pub const MMAP: u64 = 222;
    pub const GETRANDOM: u64 = 278;
}

/// Negative errno return values matching `sel4-linux-syscall-types`.
pub const ERRNO_ENOENT: i64 = 2;
pub const ERRNO_EIO: i64 = 5;
pub const ERRNO_EBADF: i64 = 9;
pub const ERRNO_EINVAL: i64 = 22;
pub const ERRNO_ENOSYS: i64 = 38;

/// Canonical Protection Domain roles in the four-PD Microkit chokepoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum ChokepointRole {
    Ingress = 0,
    Commit = 1,
    Persist = 2,
    TxEgress = 3,
}
impl ChokepointRole {
    pub const ALL: [Self; 4] = [Self::Ingress, Self::Commit, Self::Persist, Self::TxEgress];

    pub const fn expected_name(self) -> &'static [u8] {
        match self {
            Self::Ingress => b"ingress-pd",
            Self::Commit => b"commit-pd",
            Self::Persist => b"persist-pd",
            Self::TxEgress => b"tx-egress-pd",
        }
    }
    pub const fn index(self) -> usize {
        self as usize
    }
}

/// Physical MMIO or device aperture mapped into a Microkit Protection Domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ApertureKind {
    RxNicMmio,
    TxNicMmio,
    DurableLogStorage,
    HardwareTrngMmio,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PdMmioAperture {
    pub kind: ApertureKind,
    pub base_paddr: u64,
    pub byte_size: u64,
    pub writable: bool,
}
impl PdMmioAperture {
    pub fn disjoint_from(&self, other: &Self) -> bool {
        let Some(end_a) = self.base_paddr.checked_add(self.byte_size) else {
            return false;
        };
        let Some(end_b) = other.base_paddr.checked_add(other.byte_size) else {
            return false;
        };
        end_a <= other.base_paddr || end_b <= self.base_paddr
    }
}

/// Directed Microkit IPC channel kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChokepointChannelKind {
    /// One-way SPSC ring notification (`ingress-pd -> commit-pd` or `commit-pd -> tx-egress-pd`).
    OneWaySpsc,
    /// Synchronous Protected Procedure Call (`commit-pd -> persist-pd`) returning 256-bit fsync digest ack.
    ProtectedPersistPpc,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedIpcChannel {
    pub channel_id: u32,
    pub src: ChokepointRole,
    pub dst: ChokepointRole,
    pub kind: ChokepointChannelKind,
    pub max_payload_bytes: usize,
    /// True only if `dst` is granted a `Read`/wait right on `src`'s own IRQ notification
    /// (the `persist_can_wait_on_nic_irq` Microkit 2.2.0 hazard; must be `false`!).
    pub callee_consumes_caller_irq: bool,
}

/// Descriptor for one Protection Domain inside the four-PD Microkit system.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChokepointPdDesc<'a> {
    pub pd_id: u32,
    pub role: ChokepointRole,
    pub name: &'a [u8],
    pub priority: u8,
    pub elf_footprint_bytes: u64,
    pub stack_and_heap_bytes: u64,
    pub apertures: &'a [PdMmioAperture],
}

/// Complete four-PD Microkit chokepoint system descriptor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChokepointSystemDesc<'a> {
    pub rootserver_phys_start: u64,
    pub rootserver_phys_end: u64,
    pub domains: [ChokepointPdDesc<'a>; 4],
    pub channels: &'a [DirectedIpcChannel],
}

/// Capability rights mask matching `Obend.OS.Sel4MicrokitKernelCore.Rights`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapRights {
    pub read: bool,
    pub write: bool,
    pub grant: bool,
}
impl CapRights {
    pub const NONE: Self = Self {
        read: false,
        write: false,
        grant: false,
    };
    pub const RO: Self = Self {
        read: true,
        write: false,
        grant: false,
    };
    pub const WO: Self = Self {
        read: false,
        write: true,
        grant: false,
    };
    pub const RW: Self = Self {
        read: true,
        write: true,
        grant: false,
    };
    pub const RWG: Self = Self {
        read: true,
        write: true,
        grant: true,
    };

    pub const fn subset_of(self, parent: Self) -> bool {
        (!self.read || parent.read) && (!self.write || parent.write) && (!self.grant || parent.grant)
    }
}

/// Shared memory region identifiers in the four-PD chokepoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SharedRegionId {
    IngressRing,
    CommitLeafBuf,
    PersistDurableLog,
    EgressReleaseRing,
}

/// Typed kernel objects held in per-PD disjoint CSpace slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelObject {
    Notification { ntfn_id: u32 },
    PpcEndpoint { ep_id: u32 },
    SharedRegion { region: SharedRegionId, byte_len: usize },
    PrivateFrame { pfn: u64 },
    Mmio { kind: ApertureKind, base_paddr: u64, byte_size: u64 },
    HwTrng { trng_id: u32 },
}

/// Local capability handle presented by a PD (`epoch == 0` is unconditionally invalid).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapHandle {
    pub slot: usize,
    pub epoch: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapSlotEntry {
    pub global_cap_id: u64,
    pub epoch: u64,
    pub live: bool,
    pub parent_slot: Option<usize>,
    pub obj: KernelObject,
    pub rights: CapRights,
    /// Kernel-pinned badge (`0` = unbadged); callers can never supply an arbitrary badge on `Signal`.
    pub bound_badge: u64,
}
impl CapSlotEntry {
    pub const EMPTY: Self = Self {
        global_cap_id: 0,
        epoch: 0,
        live: false,
        parent_slot: None,
        obj: KernelObject::PrivateFrame { pfn: 0 },
        rights: CapRights::NONE,
        bound_badge: 0,
    };
}

/// Capability fault / refusal reason (`CAP-03` closed).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapFault {
    StaleOrZeroEpoch,
    NoSuchSlotInCallerCspace,
    WrongObjectKind,
    InsufficientRights,
    BadgeSpoofAttempt { attempted: u64, kernel_bound: u64 },
    FrameExceedsMaxBytes { requested: usize, max: usize },
    TableFull,
    AttenuationViolation,
}

/// Per-PD isolated CSpace table (indexed strictly within one PD; never shared across PDs).
#[derive(Clone, Copy, Debug)]
pub struct PdCspaceTable<const SLOTS: usize> {
    slots: [CapSlotEntry; SLOTS],
    next_epoch: u64,
}
impl<const SLOTS: usize> Default for PdCspaceTable<SLOTS> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const SLOTS: usize> PdCspaceTable<SLOTS> {
    pub const fn new() -> Self {
        Self {
            slots: [CapSlotEntry::EMPTY; SLOTS],
            next_epoch: 1,
        }
    }

    pub fn install_root(
        &mut self,
        slot: usize,
        global_cap_id: u64,
        obj: KernelObject,
        rights: CapRights,
        bound_badge: u64,
    ) -> Result<CapHandle, CapFault> {
        if slot >= SLOTS || global_cap_id == 0 {
            return Err(CapFault::TableFull);
        }
        let epoch = self.next_epoch;
        self.next_epoch = self.next_epoch.checked_add(1).ok_or(CapFault::TableFull)?;
        self.slots[slot] = CapSlotEntry {
            global_cap_id,
            epoch,
            live: true,
            parent_slot: None,
            obj,
            rights,
            bound_badge,
        };
        Ok(CapHandle { slot, epoch })
    }

    /// Mint an attenuated child capability within this PD's CSpace (`parent_slot < child_slot` DAG).
    pub fn mint_attenuated(
        &mut self,
        parent_handle: CapHandle,
        dst_slot: usize,
        global_cap_id: u64,
        rights: CapRights,
        badge: u64,
    ) -> Result<CapHandle, CapFault> {
        let parent = *self.resolve(parent_handle)?;
        if dst_slot >= SLOTS || dst_slot <= parent_handle.slot || self.slots[dst_slot].live || global_cap_id == 0 {
            return Err(CapFault::TableFull);
        }
        if !rights.subset_of(parent.rights)
            || (parent.bound_badge != 0 && badge != parent.bound_badge)
        {
            return Err(CapFault::AttenuationViolation);
        }
        let epoch = self.next_epoch;
        self.next_epoch = self.next_epoch.checked_add(1).ok_or(CapFault::TableFull)?;
        self.slots[dst_slot] = CapSlotEntry {
            global_cap_id,
            epoch,
            live: true,
            parent_slot: Some(parent_handle.slot),
            obj: parent.obj,
            rights,
            bound_badge: badge,
        };
        Ok(CapHandle {
            slot: dst_slot,
            epoch,
        })
    }

    /// Transitive revocation in one forward pass (`Obend.OS.Sel4MicrokitKernelCore.revokeCap`):
    /// revokes `target_slot` and every descendant `child > parent` at any depth, bumping epochs.
    pub fn revoke_slot_and_descendants(&mut self, target_slot: usize) -> Result<usize, CapFault> {
        if target_slot >= SLOTS || !self.slots[target_slot].live {
            return Err(CapFault::NoSuchSlotInCallerCspace);
        }
        let mut doomed = [false; SLOTS];
        doomed[target_slot] = true;
        let mut erased = 0usize;
        for i in target_slot..SLOTS {
            if i > target_slot {
                if let Some(p) = self.slots[i].parent_slot {
                    if p < i && doomed[p] {
                        doomed[i] = true;
                    }
                }
            }
            if doomed[i] && self.slots[i].live {
                self.slots[i].live = false;
                self.slots[i].epoch = self.next_epoch;
                self.next_epoch = self.next_epoch.saturating_add(1);
                erased += 1;
            }
        }
        Ok(erased)
    }

    pub fn resolve(&self, h: CapHandle) -> Result<&CapSlotEntry, CapFault> {
        if h.epoch == 0 {
            return Err(CapFault::StaleOrZeroEpoch);
        }
        let Some(entry) = self.slots.get(h.slot) else {
            return Err(CapFault::NoSuchSlotInCallerCspace);
        };
        if !entry.live {
            if entry.epoch != 0 {
                return Err(CapFault::StaleOrZeroEpoch);
            }
            return Err(CapFault::NoSuchSlotInCallerCspace);
        }
        if entry.epoch != h.epoch {
            return Err(CapFault::StaleOrZeroEpoch);
        }
        Ok(entry)
    }

    pub fn has_live_hw_trng(&self) -> bool {
        self.slots.iter().any(|s| {
            s.live && s.rights.read && matches!(s.obj, KernelObject::HwTrng { .. })
        })
    }

    pub fn slots(&self) -> &[CapSlotEntry; SLOTS] {
        &self.slots
    }
}

/// Request submitted to the capability dispatcher on a PD's authenticated channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapRequest {
    Signal {
        notif: CapHandle,
        /// If `Some(b)` and `b != entry.bound_badge`, refused as `BadgeSpoofAttempt`.
        claimed_badge: Option<u64>,
    },
    PollNotification {
        notif: CapHandle,
    },
    MapSharedRegion {
        region: CapHandle,
        writable: bool,
        frame_bytes: usize,
    },
    InvokePersistPpc {
        endpoint: CapHandle,
        frame_bytes: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapReply {
    Signalled { delivered_badge: u64 },
    Badge(u64),
    MappedRegion { region: SharedRegionId, byte_len: usize, writable: bool },
    PpcAuthorized { ep_id: u32 },
}

/// Four-PD disjoint CSpace container & notification badge state (`CAP-03` replacement).
#[derive(Clone, Copy, Debug)]
pub struct FourPdCspace<const SLOTS: usize> {
    tables: [PdCspaceTable<SLOTS>; 4],
    notif_badges: [u64; 16],
}
impl<const SLOTS: usize> Default for FourPdCspace<SLOTS> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const SLOTS: usize> FourPdCspace<SLOTS> {
    pub const fn new() -> Self {
        Self {
            tables: [const { PdCspaceTable::new() }; 4],
            notif_badges: [0u64; 16],
        }
    }

    pub fn pd_table(&self, role: ChokepointRole) -> &PdCspaceTable<SLOTS> {
        &self.tables[role.index()]
    }

    pub fn pd_table_mut(&mut self, role: ChokepointRole) -> &mut PdCspaceTable<SLOTS> {
        &mut self.tables[role.index()]
    }

    /// Dispatch a capability operation strictly against `caller_pd`'s isolated CSpace table.
    pub fn dispatch(&mut self, caller_pd: ChokepointRole, req: CapRequest) -> Result<CapReply, CapFault> {
        let table = &self.tables[caller_pd.index()];
        match req {
            CapRequest::Signal {
                notif,
                claimed_badge,
            } => {
                let entry = *table.resolve(notif)?;
                let KernelObject::Notification { ntfn_id } = entry.obj else {
                    return Err(CapFault::WrongObjectKind);
                };
                if !entry.rights.write || entry.bound_badge == 0 {
                    return Err(CapFault::InsufficientRights);
                }
                if let Some(attempted) = claimed_badge {
                    if attempted != entry.bound_badge {
                        return Err(CapFault::BadgeSpoofAttempt {
                            attempted,
                            kernel_bound: entry.bound_badge,
                        });
                    }
                }
                let slot = self
                    .notif_badges
                    .get_mut(ntfn_id as usize)
                    .ok_or(CapFault::NoSuchSlotInCallerCspace)?;
                *slot |= entry.bound_badge;
                Ok(CapReply::Signalled {
                    delivered_badge: entry.bound_badge,
                })
            }
            CapRequest::PollNotification { notif } => {
                let entry = *table.resolve(notif)?;
                let KernelObject::Notification { ntfn_id } = entry.obj else {
                    return Err(CapFault::WrongObjectKind);
                };
                if !entry.rights.read {
                    return Err(CapFault::InsufficientRights);
                }
                let slot = self
                    .notif_badges
                    .get_mut(ntfn_id as usize)
                    .ok_or(CapFault::NoSuchSlotInCallerCspace)?;
                let b = *slot;
                *slot = 0;
                Ok(CapReply::Badge(b))
            }
            CapRequest::MapSharedRegion {
                region,
                writable,
                frame_bytes,
            } => {
                if frame_bytes > MAX_IPC_FRAME_BYTES {
                    return Err(CapFault::FrameExceedsMaxBytes {
                        requested: frame_bytes,
                        max: MAX_IPC_FRAME_BYTES,
                    });
                }
                let entry = *table.resolve(region)?;
                let KernelObject::SharedRegion {
                    region: region_id,
                    byte_len,
                } = entry.obj
                else {
                    return Err(CapFault::WrongObjectKind);
                };
                if frame_bytes > byte_len {
                    return Err(CapFault::FrameExceedsMaxBytes {
                        requested: frame_bytes,
                        max: byte_len,
                    });
                }
                if !entry.rights.read || (writable && !entry.rights.write) {
                    return Err(CapFault::InsufficientRights);
                }
                Ok(CapReply::MappedRegion {
                    region: region_id,
                    byte_len,
                    writable,
                })
            }
            CapRequest::InvokePersistPpc {
                endpoint,
                frame_bytes,
            } => {
                if frame_bytes == 0 || frame_bytes > MAX_IPC_FRAME_BYTES {
                    return Err(CapFault::FrameExceedsMaxBytes {
                        requested: frame_bytes,
                        max: MAX_IPC_FRAME_BYTES,
                    });
                }
                let entry = *table.resolve(endpoint)?;
                let KernelObject::PpcEndpoint { ep_id } = entry.obj else {
                    return Err(CapFault::WrongObjectKind);
                };
                if !entry.rights.write {
                    return Err(CapFault::InsufficientRights);
                }
                Ok(CapReply::PpcAuthorized { ep_id })
            }
        }
    }
}

/// Static structural/capability violation on the four-PD Microkit chokepoint descriptor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChokepointViolation {
    InvalidRootServerSpan,
    RootServerSpanBudgetExceeded { span_bytes: u64, limit_bytes: u64 },
    LoaderCollision { phys_end: u64, loader_base: u64 },
    DomainFootprintExceedsSpan { sum_bytes: u64, span_bytes: u64 },
    RoleMismatch { slot: usize, expected: ChokepointRole, got: ChokepointRole },
    CanonicalNameMismatch { role: ChokepointRole },
    DuplicatePdId { pd_id: u32 },
    SharedWritableMmio { pd_a: ChokepointRole, pd_b: ChokepointRole },
    ForbiddenApertureOwner { role: ChokepointRole, kind: ApertureKind },
    MissingRequiredAperture { role: ChokepointRole, kind: ApertureKind },
    DirectIngressToEgressBypass,
    ForbiddenChannelTopology { src: ChokepointRole, dst: ChokepointRole },
    InvalidChannelBounds { channel_id: u32 },
    CalleeConsumesCallerIrq { channel_id: u32 },
    InvalidPpcPriority { commit_prio: u8, persist_prio: u8 },
    MissingPipelineStageEdge,
    DuplicateGlobalCapId { global_cap_id: u64 },
    CspacePrivilegeViolation { role: ChokepointRole },
}

/// Validate the four-PD Microkit chokepoint system descriptor AND per-PD CSpace least-privilege partition:
/// 1. Root-server physical span is positive, `< 10 MiB`, accommodates all PD footprints, and stays below
///    stock Microkit 2.2.0's `0x7000_0000` loader when placed in the `0x6000_0000` RAM window.
/// 2. Domains are `[ingress-pd, commit-pd, persist-pd, tx-egress-pd]` with distinct IDs, disjoint writable MMIO,
///    exclusive `RxNicMmio` in `Ingress`, exclusive writable `DurableLogStorage` in `Persist`, exclusive
///    writable `TxNicMmio` in `TxEgress`, and zero NIC/storage MMIO in `Commit`.
/// 3. Channels strictly follow `Ingress -> Commit (SPSC)`, `Commit -> Persist (PPC, persist_prio > commit_prio)`,
///    and `Commit -> TxEgress (SPSC)` with `1..=4096` byte bounds, zero `callee_consumes_caller_irq`, and
///    **zero `Ingress -> TxEgress` or `Ingress -> Persist` bypasses**.
/// 4. Per-PD CSpace tables have pairwise-disjoint `global_cap_id`s across all 4 PDs, `Commit` holds an
///    exclusive `PrivateFrame`, `Persist` maps `CommitLeafBuf` read-only, and no PD holds cross-role write caps.
pub fn verify_chokepoint_system<const SLOTS: usize>(
    desc: &ChokepointSystemDesc<'_>,
    cspaces: &FourPdCspace<SLOTS>,
) -> Result<(), ChokepointViolation> {
    if desc.rootserver_phys_end <= desc.rootserver_phys_start {
        return Err(ChokepointViolation::InvalidRootServerSpan);
    }
    let span = desc.rootserver_phys_end - desc.rootserver_phys_start;
    if span >= MAX_ROOTSERVER_SPAN_BYTES {
        return Err(ChokepointViolation::RootServerSpanBudgetExceeded {
            span_bytes: span,
            limit_bytes: MAX_ROOTSERVER_SPAN_BYTES,
        });
    }
    if desc.rootserver_phys_start < STOCK_MICROKIT_LOADER_BASE
        && desc.rootserver_phys_end > STOCK_MICROKIT_LOADER_BASE
    {
        return Err(ChokepointViolation::LoaderCollision {
            phys_end: desc.rootserver_phys_end,
            loader_base: STOCK_MICROKIT_LOADER_BASE,
        });
    }

    let mut footprint_sum = 0u64;
    for (idx, expected_role) in ChokepointRole::ALL.into_iter().enumerate() {
        let d = &desc.domains[idx];
        if d.role != expected_role {
            return Err(ChokepointViolation::RoleMismatch {
                slot: idx,
                expected: expected_role,
                got: d.role,
            });
        }
        if d.name != expected_role.expected_name() {
            return Err(ChokepointViolation::CanonicalNameMismatch {
                role: expected_role,
            });
        }
        for other in &desc.domains[idx + 1..] {
            if d.pd_id == other.pd_id {
                return Err(ChokepointViolation::DuplicatePdId { pd_id: d.pd_id });
            }
            for a in d.apertures {
                if a.byte_size == 0 {
                    return Err(ChokepointViolation::InvalidRootServerSpan);
                }
                for b in other.apertures {
                    if (a.writable || b.writable) && !a.disjoint_from(b) {
                        return Err(ChokepointViolation::SharedWritableMmio {
                            pd_a: d.role,
                            pd_b: other.role,
                        });
                    }
                }
            }
        }
        for a in d.apertures {
            if a.byte_size == 0 {
                return Err(ChokepointViolation::InvalidRootServerSpan);
            }
            let allowed = match (d.role, a.kind) {
                (ChokepointRole::Ingress, ApertureKind::RxNicMmio) => true,
                (ChokepointRole::Commit, ApertureKind::HardwareTrngMmio) => !a.writable,
                (ChokepointRole::Persist, ApertureKind::DurableLogStorage) => a.writable,
                (ChokepointRole::TxEgress, ApertureKind::TxNicMmio) => a.writable,
                _ => false,
            };
            if !allowed {
                return Err(ChokepointViolation::ForbiddenApertureOwner {
                    role: d.role,
                    kind: a.kind,
                });
            }
        }
        let pd_bytes = d
            .elf_footprint_bytes
            .checked_add(d.stack_and_heap_bytes)
            .ok_or(ChokepointViolation::InvalidRootServerSpan)?;
        footprint_sum = footprint_sum
            .checked_add(pd_bytes)
            .ok_or(ChokepointViolation::InvalidRootServerSpan)?;
    }
    if footprint_sum > span {
        return Err(ChokepointViolation::DomainFootprintExceedsSpan {
            sum_bytes: footprint_sum,
            span_bytes: span,
        });
    }

    if !desc.domains[ChokepointRole::Ingress.index()]
        .apertures
        .iter()
        .any(|a| a.kind == ApertureKind::RxNicMmio)
    {
        return Err(ChokepointViolation::MissingRequiredAperture {
            role: ChokepointRole::Ingress,
            kind: ApertureKind::RxNicMmio,
        });
    }
    if !desc.domains[ChokepointRole::Persist.index()]
        .apertures
        .iter()
        .any(|a| a.kind == ApertureKind::DurableLogStorage && a.writable)
    {
        return Err(ChokepointViolation::MissingRequiredAperture {
            role: ChokepointRole::Persist,
            kind: ApertureKind::DurableLogStorage,
        });
    }
    if !desc.domains[ChokepointRole::TxEgress.index()]
        .apertures
        .iter()
        .any(|a| a.kind == ApertureKind::TxNicMmio && a.writable)
    {
        return Err(ChokepointViolation::MissingRequiredAperture {
            role: ChokepointRole::TxEgress,
            kind: ApertureKind::TxNicMmio,
        });
    }

    let commit_prio = desc.domains[ChokepointRole::Commit.index()].priority;
    let persist_prio = desc.domains[ChokepointRole::Persist.index()].priority;
    if persist_prio <= commit_prio {
        return Err(ChokepointViolation::InvalidPpcPriority {
            commit_prio,
            persist_prio,
        });
    }

    let mut saw_ingress_to_commit = false;
    let mut saw_commit_to_persist = false;
    let mut saw_commit_to_egress = false;
    for (i, ch) in desc.channels.iter().enumerate() {
        if ch.max_payload_bytes == 0 || ch.max_payload_bytes > MAX_IPC_FRAME_BYTES {
            return Err(ChokepointViolation::InvalidChannelBounds {
                channel_id: ch.channel_id,
            });
        }
        if ch.callee_consumes_caller_irq {
            return Err(ChokepointViolation::CalleeConsumesCallerIrq {
                channel_id: ch.channel_id,
            });
        }
        for other in &desc.channels[i + 1..] {
            if ch.channel_id == other.channel_id {
                return Err(ChokepointViolation::InvalidChannelBounds {
                    channel_id: ch.channel_id,
                });
            }
        }
        match (ch.src, ch.dst, ch.kind) {
            (ChokepointRole::Ingress, ChokepointRole::TxEgress, _) => {
                return Err(ChokepointViolation::DirectIngressToEgressBypass);
            }
            (ChokepointRole::Ingress, ChokepointRole::Commit, ChokepointChannelKind::OneWaySpsc) => {
                saw_ingress_to_commit = true;
            }
            (
                ChokepointRole::Commit,
                ChokepointRole::Persist,
                ChokepointChannelKind::ProtectedPersistPpc,
            ) => {
                saw_commit_to_persist = true;
            }
            (ChokepointRole::Commit, ChokepointRole::TxEgress, ChokepointChannelKind::OneWaySpsc) => {
                saw_commit_to_egress = true;
            }
            _ => {
                return Err(ChokepointViolation::ForbiddenChannelTopology {
                    src: ch.src,
                    dst: ch.dst,
                });
            }
        }
    }
    if !(saw_ingress_to_commit && saw_commit_to_persist && saw_commit_to_egress) {
        return Err(ChokepointViolation::MissingPipelineStageEdge);
    }

    // Verify per-PD CSpace disjointness & least-privilege invariants across all 4 PDs.
    let mut commit_has_private_frame = false;
    let mut commit_private_pfn = None;
    for r_idx in 0..4 {
        let role = ChokepointRole::ALL[r_idx];
        let slots = cspaces.pd_table(role).slots();
        for (s_idx, entry) in slots.iter().enumerate() {
            if !entry.live {
                continue;
            }
            if entry.epoch == 0 || entry.global_cap_id == 0 {
                return Err(ChokepointViolation::CspacePrivilegeViolation { role });
            }
            // Check pairwise disjoint global_cap_id across remaining slots of this PD and all other PDs.
            for later in &slots[s_idx + 1..] {
                if later.live && later.global_cap_id == entry.global_cap_id {
                    return Err(ChokepointViolation::DuplicateGlobalCapId {
                        global_cap_id: entry.global_cap_id,
                    });
                }
            }
            for other_r in (r_idx + 1)..4 {
                for other_entry in cspaces.pd_table(ChokepointRole::ALL[other_r]).slots() {
                    if other_entry.live && other_entry.global_cap_id == entry.global_cap_id {
                        return Err(ChokepointViolation::DuplicateGlobalCapId {
                            global_cap_id: entry.global_cap_id,
                        });
                    }
                }
            }
            let permitted = match (role, entry.obj) {
                (ChokepointRole::Ingress, KernelObject::SharedRegion { region: SharedRegionId::IngressRing, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.write
                }
                (ChokepointRole::Ingress, KernelObject::Notification { .. }) => {
                    entry.rights.write && !entry.rights.read && entry.bound_badge != 0
                }
                (ChokepointRole::Ingress, KernelObject::Mmio { kind: ApertureKind::RxNicMmio, .. }) => true,

                (ChokepointRole::Commit, KernelObject::SharedRegion { region: SharedRegionId::IngressRing, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.read && !entry.rights.write
                }
                (ChokepointRole::Commit, KernelObject::SharedRegion { region: SharedRegionId::CommitLeafBuf, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.read && entry.rights.write
                }
                (ChokepointRole::Commit, KernelObject::SharedRegion { region: SharedRegionId::EgressReleaseRing, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.write
                }
                (ChokepointRole::Commit, KernelObject::PrivateFrame { pfn }) => {
                    if pfn == 0 || !entry.rights.read || !entry.rights.write {
                        false
                    } else {
                        commit_has_private_frame = true;
                        commit_private_pfn = Some(pfn);
                        true
                    }
                }
                (ChokepointRole::Commit, KernelObject::PpcEndpoint { .. }) => entry.rights.write,
                (ChokepointRole::Commit, KernelObject::Notification { .. }) => {
                    (entry.rights.read && !entry.rights.write)
                        || (entry.rights.write && !entry.rights.read && entry.bound_badge != 0)
                }
                (ChokepointRole::Commit, KernelObject::HwTrng { .. }) => {
                    entry.rights.read && !entry.rights.write
                }

                (ChokepointRole::Persist, KernelObject::SharedRegion { region: SharedRegionId::CommitLeafBuf, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.read && !entry.rights.write
                }
                (ChokepointRole::Persist, KernelObject::SharedRegion { region: SharedRegionId::PersistDurableLog, .. }) => {
                    entry.rights.read && entry.rights.write
                }
                (ChokepointRole::Persist, KernelObject::PpcEndpoint { .. }) => {
                    entry.rights.read && !entry.rights.write
                }
                (ChokepointRole::Persist, KernelObject::Mmio { kind: ApertureKind::DurableLogStorage, .. }) => {
                    entry.rights.read && entry.rights.write
                }

                (ChokepointRole::TxEgress, KernelObject::SharedRegion { region: SharedRegionId::EgressReleaseRing, byte_len }) => {
                    byte_len <= MAX_IPC_FRAME_BYTES && entry.rights.read && !entry.rights.write
                }
                (ChokepointRole::TxEgress, KernelObject::Notification { .. }) => {
                    entry.rights.read && !entry.rights.write
                }
                (ChokepointRole::TxEgress, KernelObject::Mmio { kind: ApertureKind::TxNicMmio, .. }) => {
                    entry.rights.write
                }

                _ => false,
            };
            if !permitted {
                return Err(ChokepointViolation::CspacePrivilegeViolation { role });
            }
        }
    }
    if !commit_has_private_frame {
        return Err(ChokepointViolation::CspacePrivilegeViolation {
            role: ChokepointRole::Commit,
        });
    }
    if let Some(priv_pfn) = commit_private_pfn {
        for role in [ChokepointRole::Ingress, ChokepointRole::Persist, ChokepointRole::TxEgress] {
            for s in cspaces.pd_table(role).slots() {
                if s.live && matches!(s.obj, KernelObject::PrivateFrame { pfn } if pfn == priv_pfn) {
                    return Err(ChokepointViolation::CspacePrivilegeViolation { role });
                }
            }
        }
    }
    Ok(())
}

/// Hardware TRNG entropy provider interface (`CAP-29`).
pub trait HwTrngSource {
    /// Fill `out` from hardware TRNG FIFO/channel. Returns `false` if hardware is unavailable/not-ready.
    fn read_entropy(&mut self, out: &mut [u8]) -> bool;
}

/// Fail-closed in-PD Linux syscall & hardware-TRNG confinement gate (`CAP-29` closed):
/// - `GETRANDOM` (`278`) and `OPENAT("/dev/urandom" | "/dev/random")` return `-ENOSYS` (`-38`)
///   unless `caller_pd`'s disjoint CSpace holds a live `KernelObject::HwTrng` read capability
///   AND the attached hardware TRNG passes continuous non-zero / non-stuck health checks.
/// - Never zero-fills `out_buf` on refusal!
pub struct PdSyscallGate;

impl PdSyscallGate {
    fn entropy_health_ok(bytes: &[u8]) -> bool {
        if bytes.len() < 8 {
            return bytes.iter().any(|&b| b != 0);
        }
        let first = bytes[0];
        let all_same = bytes.iter().all(|&b| b == first);
        let all_zero = bytes.iter().all(|&b| b == 0);
        !all_same && !all_zero
    }

    pub fn handle_getrandom<const SLOTS: usize>(
        cspaces: &FourPdCspace<SLOTS>,
        caller_pd: ChokepointRole,
        trng: Option<&mut dyn HwTrngSource>,
        out_buf: &mut [u8],
    ) -> i64 {
        if !cspaces.pd_table(caller_pd).has_live_hw_trng() {
            return -ERRNO_ENOSYS;
        }
        let Some(hw_trng) = trng else {
            return -ERRNO_ENOSYS;
        };
        if out_buf.is_empty() {
            return 0;
        }
        // Stage into bounded scratch chunk by chunk so a failing/stuck TRNG never clobbers `out_buf` with zeros!
        let mut scratch = [0u8; 64];
        let mut offset = 0usize;
        while offset < out_buf.len() {
            let take = (out_buf.len() - offset).min(scratch.len());
            scratch[..take].fill(0);
            let sample_len = take.max(8).min(scratch.len());
            if !hw_trng.read_entropy(&mut scratch[..sample_len]) {
                return -ERRNO_EIO;
            }
            if !Self::entropy_health_ok(&scratch[..sample_len]) {
                return -ERRNO_EIO;
            }
            out_buf[offset..offset + take].copy_from_slice(&scratch[..take]);
            offset += take;
        }
        i64::try_from(out_buf.len()).unwrap_or(-ERRNO_EINVAL)
    }

    pub fn handle_openat<const SLOTS: usize>(
        cspaces: &FourPdCspace<SLOTS>,
        caller_pd: ChokepointRole,
        path: &[u8],
    ) -> i64 {
        if path == b"/dev/urandom" || path == b"/dev/random" {
            let _ = (cspaces, caller_pd);
            // Force callers onto capability-checked `GETRANDOM`; never hand out a zero-filled sentinel fd!
            return -ERRNO_ENOSYS;
        }
        -ERRNO_ENOENT
    }

    pub fn handle_read_fd(fd: i64, _out_buf: &mut [u8]) -> i64 {
        let _ = fd;
        // Refuses sentinel `URANDOM_FD = 1000` and all unbacked fds with `-EBADF` without touching `_out_buf`.
        -ERRNO_EBADF
    }

    pub fn dispatch_syscall<const SLOTS: usize>(
        cspaces: &FourPdCspace<SLOTS>,
        caller_pd: ChokepointRole,
        sysnum: u64,
        path_arg: Option<&[u8]>,
        fd_arg: i64,
        buf_arg: Option<&mut [u8]>,
        trng: Option<&mut dyn HwTrngSource>,
    ) -> i64 {
        match sysnum {
            linux_aarch64_nr::GETRANDOM => {
                let Some(buf) = buf_arg else {
                    return -ERRNO_EINVAL;
                };
                Self::handle_getrandom(cspaces, caller_pd, trng, buf)
            }
            linux_aarch64_nr::OPENAT => {
                let Some(path) = path_arg else {
                    return -ERRNO_EINVAL;
                };
                Self::handle_openat(cspaces, caller_pd, path)
            }
            linux_aarch64_nr::READ => {
                let mut empty = [];
                let buf = buf_arg.unwrap_or(&mut empty);
                Self::handle_read_fd(fd_arg, buf)
            }
            linux_aarch64_nr::FSTAT => -ERRNO_EBADF,
            linux_aarch64_nr::CLOSE | linux_aarch64_nr::FUTEX | linux_aarch64_nr::CLOCK_GETTIME => 0,
            _ => -ERRNO_ENOSYS,
        }
    }
}

/// Domain customization tags for `persist-pd` fsync digest acks (`T4` count-only ack bug closed).
pub const PERSIST_LEAF_ACK_DOMAIN: &[u8] = b"OBEND-PERSIST-LEAF-ACK-V1";
pub const PERSIST_WAL_CHAIN_DOMAIN: &[u8] = b"OBEND-PERSIST-WAL-CHAIN-V1";

pub fn compute_persist_leaf_digest(alg: OutboxHashAlg, log_seq: u64, leaf_bytes: &[u8]) -> Digest {
    match alg {
        OutboxHashAlg::Cshake256 => {
            let mut s = customized(PERSIST_LEAF_ACK_DOMAIN);
            s.absorb(&log_seq.to_be_bytes());
            s.absorb(&(leaf_bytes.len() as u64).to_be_bytes());
            s.absorb(leaf_bytes);
            s.digest()
        }
        OutboxHashAlg::Sha256 => {
            let mut h = Sha256::new();
            h.update(&(PERSIST_LEAF_ACK_DOMAIN.len() as u64).to_be_bytes());
            h.update(PERSIST_LEAF_ACK_DOMAIN);
            h.update(&log_seq.to_be_bytes());
            h.update(&(leaf_bytes.len() as u64).to_be_bytes());
            h.update(leaf_bytes);
            h.finalize()
        }
    }
}

pub fn advance_persist_wal_root(
    alg: OutboxHashAlg,
    prev_wal_root: &Digest,
    log_seq: u64,
    leaf_digest: &Digest,
) -> Digest {
    match alg {
        OutboxHashAlg::Cshake256 => {
            let mut s = customized(PERSIST_WAL_CHAIN_DOMAIN);
            s.absorb(prev_wal_root);
            s.absorb(&log_seq.to_be_bytes());
            s.absorb(leaf_digest);
            s.digest()
        }
        OutboxHashAlg::Sha256 => {
            let mut h = Sha256::new();
            h.update(&(PERSIST_WAL_CHAIN_DOMAIN.len() as u64).to_be_bytes());
            h.update(PERSIST_WAL_CHAIN_DOMAIN);
            h.update(prev_wal_root);
            h.update(&log_seq.to_be_bytes());
            h.update(leaf_digest);
            h.finalize()
        }
    }
}

/// Cryptographic fsync acknowledgment returned by `persist-pd` over Protected Procedure Call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PersistDigestAck {
    pub status_ok: bool,
    pub fsynced: bool,
    pub log_seq: u64,
    pub leaf_digest: Digest,
    pub wal_root: Digest,
}

/// `persist-pd` state: sole writable holder of `durable_log`, mapping `leaf_buf` read-only.
#[derive(Clone, Copy, Debug)]
pub struct PersistPdState<const LOG_CAP: usize> {
    pub hash_alg: OutboxHashAlg,
    durable_log: [u8; LOG_CAP],
    used: usize,
    entries: u64,
    wal_root: Digest,
}
impl<const LOG_CAP: usize> PersistPdState<LOG_CAP> {
    pub const fn new(hash_alg: OutboxHashAlg, genesis_wal_root: Digest) -> Self {
        Self {
            hash_alg,
            durable_log: [0u8; LOG_CAP],
            used: 0,
            entries: 0,
            wal_root: genesis_wal_root,
        }
    }
    pub const fn entries(&self) -> u64 {
        self.entries
    }
    pub const fn wal_root(&self) -> Digest {
        self.wal_root
    }

    /// Protected procedure call handler: reads staged `[le8(len) || leaf_bytes]` from read-only
    /// `leaf_buf`, appends to `durable_log`, and returns the 256-bit fsync digest ack.
    pub fn handle_ppc_append(&mut self, mr0_len: usize, leaf_buf_ro: &[u8]) -> PersistDigestAck {
        let refuse = PersistDigestAck {
            status_ok: false,
            fsynced: false,
            log_seq: self.entries,
            leaf_digest: [0u8; 32],
            wal_root: self.wal_root,
        };
        let Some(hdr) = leaf_buf_ro.get(..8) else {
            return refuse;
        };
        let staged_len = usize::try_from(u64::from_le_bytes(hdr.try_into().unwrap())).unwrap_or(usize::MAX);
        if mr0_len == 0
            || mr0_len != staged_len
            || mr0_len > MAX_IPC_FRAME_BYTES - 8
            || leaf_buf_ro.len() < 8 + mr0_len
        {
            return refuse;
        }
        let Some(record_len) = mr0_len.checked_add(8) else {
            return refuse;
        };
        let Some(next_used) = self.used.checked_add(record_len) else {
            return refuse;
        };
        if next_used > LOG_CAP {
            return refuse;
        }
        let Some(next_seq) = self.entries.checked_add(1) else {
            return refuse;
        };
        let leaf_slice = &leaf_buf_ro[8..8 + mr0_len];
        self.durable_log[self.used..self.used + 8].copy_from_slice(&(mr0_len as u64).to_le_bytes());
        self.durable_log[self.used + 8..next_used].copy_from_slice(leaf_slice);
        self.used = next_used;
        self.entries = next_seq;
        let leaf_digest = compute_persist_leaf_digest(self.hash_alg, next_seq, leaf_slice);
        self.wal_root = advance_persist_wal_root(self.hash_alg, &self.wal_root, next_seq, &leaf_digest);
        PersistDigestAck {
            status_ok: true,
            fsynced: true,
            log_seq: next_seq,
            leaf_digest,
            wal_root: self.wal_root,
        }
    }
}

/// Authenticated release message sent on `commit-pd -> tx-egress-pd` strictly after `persist-pd` ack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EgressReleaseFrame<const MAX_PAYLOAD: usize> {
    pub payload_len: usize,
    pub payload: [u8; MAX_PAYLOAD],
    pub eff_commit: Digest,
    pub persist_ack: PersistDigestAck,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TxReleaseRefusal {
    UnacknowledgedOrUnfsyncedPersist,
    SequenceGap { expected: u64, got: u64 },
    EmptyOrOversizedFrame,
    PersistLeafDigestMismatch,
    WalChainRootMismatch,
}

/// Encode the canonical 40-byte + payload WAL leaf staged in `leaf_buf`:
/// `be8(nullifier_id) || eff_commit(32) || payload`.
pub fn format_staged_wal_leaf<const BUF: usize>(
    nullifier_id: u64,
    eff_commit: &Digest,
    payload: &[u8],
    leaf_buf: &mut [u8; BUF],
) -> Option<usize> {
    let body_len = 8usize.checked_add(32)?.checked_add(payload.len())?;
    let total = 8usize.checked_add(body_len)?;
    if total > BUF || total > MAX_IPC_FRAME_BYTES {
        return None;
    }
    leaf_buf[..8].copy_from_slice(&(body_len as u64).to_le_bytes());
    leaf_buf[8..16].copy_from_slice(&nullifier_id.to_be_bytes());
    leaf_buf[16..48].copy_from_slice(eff_commit);
    leaf_buf[48..total].copy_from_slice(payload);
    Some(body_len)
}

/// `tx-egress-pd` state: sole holder of outbound TX NIC MMIO; releases a frame ONLY when
/// `PersistDigestAck` fsync flag, sequence number, leaf digest over `(nullifier_id, eff_commit, payload)`,
/// and chained `wal_root` all verify!
#[derive(Clone, Copy, Debug)]
pub struct TxEgressPdState {
    pub hash_alg: OutboxHashAlg,
    released_seq: u64,
    last_wal_root: Digest,
    tx_packets_emitted: u64,
    last_tx_digest: Digest,
}
impl TxEgressPdState {
    pub const fn new(hash_alg: OutboxHashAlg, genesis_wal_root: Digest) -> Self {
        Self {
            hash_alg,
            released_seq: 0,
            last_wal_root: genesis_wal_root,
            tx_packets_emitted: 0,
            last_tx_digest: [0u8; 32],
        }
    }
    pub const fn released_seq(&self) -> u64 {
        self.released_seq
    }
    pub const fn tx_packets_emitted(&self) -> u64 {
        self.tx_packets_emitted
    }
    pub const fn last_tx_digest(&self) -> Digest {
        self.last_tx_digest
    }

    pub fn try_release<const MAX_PAYLOAD: usize>(
        &mut self,
        nullifier_id: u64,
        frame: &EgressReleaseFrame<MAX_PAYLOAD>,
    ) -> Result<Digest, TxReleaseRefusal> {
        if !frame.persist_ack.status_ok || !frame.persist_ack.fsynced {
            return Err(TxReleaseRefusal::UnacknowledgedOrUnfsyncedPersist);
        }
        let expected_seq = self
            .released_seq
            .checked_add(1)
            .ok_or(TxReleaseRefusal::UnacknowledgedOrUnfsyncedPersist)?;
        if frame.persist_ack.log_seq != expected_seq {
            return Err(TxReleaseRefusal::SequenceGap {
                expected: expected_seq,
                got: frame.persist_ack.log_seq,
            });
        }
        if frame.payload_len == 0 || frame.payload_len > MAX_PAYLOAD {
            return Err(TxReleaseRefusal::EmptyOrOversizedFrame);
        }
        let payload_slice = &frame.payload[..frame.payload_len];
        let mut staged = [0u8; MAX_IPC_FRAME_BYTES];
        let Some(body_len) =
            format_staged_wal_leaf(nullifier_id, &frame.eff_commit, payload_slice, &mut staged)
        else {
            return Err(TxReleaseRefusal::EmptyOrOversizedFrame);
        };
        let expected_leaf_digest =
            compute_persist_leaf_digest(self.hash_alg, expected_seq, &staged[8..8 + body_len]);
        if !ct_eq_digest(&frame.persist_ack.leaf_digest, &expected_leaf_digest) {
            return Err(TxReleaseRefusal::PersistLeafDigestMismatch);
        }
        let expected_wal = advance_persist_wal_root(
            self.hash_alg,
            &self.last_wal_root,
            expected_seq,
            &expected_leaf_digest,
        );
        if !ct_eq_digest(&frame.persist_ack.wal_root, &expected_wal) {
            return Err(TxReleaseRefusal::WalChainRootMismatch);
        }
        self.released_seq = expected_seq;
        self.last_wal_root = expected_wal;
        self.tx_packets_emitted = self.tx_packets_emitted.saturating_add(1);
        self.last_tx_digest = expected_leaf_digest;
        Ok(expected_leaf_digest)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HaltReason {
    CapacityExhausted,
    PersistAckFailed,
    PersistDigestMismatch,
    CspaceCapabilityFault,
    EgressReleaseRejected,
    ExplicitFaultLatch,
}

/// Fail-closed `commit-pd` monitor state machine (`CAP-28` closed):
/// - `halted` is a private irreversible monotone latch (`false -> true`, zero reset method).
/// - Every entry point checks `if self.halted { return false; }` **first**, BEFORE copying ring
///   frames, invoking `OutboxFinalityVerifier`, staging `leaf_buf`, calling `persist-pd` PPC,
///   or mutating `hw`, `ctr`, `log_len`, `forwarded`, or `refused`!
#[derive(Clone, Copy, Debug)]
pub struct CommitPdMonitor<const MAX_N: usize, const MAX_VIEWS: usize = 4> {
    pub verifier: OutboxFinalityVerifier<MAX_N, MAX_VIEWS>,
    committed_state_root: Digest,
    height: u64,
    hw: u64,
    ctr: u64,
    log_len: u64,
    cap: u64,
    wal_root: Digest,
    halted: bool,
    halt_reason: Option<HaltReason>,
    forwarded: u64,
    refused: u64,
    step_invocations: u64,
    ppc_persist_calls: u64,
    egress_releases: u64,
}
impl<const MAX_N: usize, const MAX_VIEWS: usize> CommitPdMonitor<MAX_N, MAX_VIEWS> {
    pub const fn new(
        verifier: OutboxFinalityVerifier<MAX_N, MAX_VIEWS>,
        genesis_state_root: Digest,
        genesis_wal_root: Digest,
        cap: u64,
    ) -> Self {
        Self {
            verifier,
            committed_state_root: genesis_state_root,
            height: 0,
            hw: 0,
            ctr: 0,
            log_len: 0,
            cap,
            wal_root: genesis_wal_root,
            halted: false,
            halt_reason: None,
            forwarded: 0,
            refused: 0,
            step_invocations: 0,
            ppc_persist_calls: 0,
            egress_releases: 0,
        }
    }

    pub const fn is_halted(&self) -> bool {
        self.halted
    }
    pub const fn halt_reason(&self) -> Option<HaltReason> {
        self.halt_reason
    }
    pub const fn committed_state_root(&self) -> Digest {
        self.committed_state_root
    }
    pub const fn height(&self) -> u64 {
        self.height
    }
    pub const fn hw(&self) -> u64 {
        self.hw
    }
    pub const fn ctr(&self) -> u64 {
        self.ctr
    }
    pub const fn log_len(&self) -> u64 {
        self.log_len
    }
    pub const fn wal_root(&self) -> Digest {
        self.wal_root
    }
    pub const fn forwarded(&self) -> u64 {
        self.forwarded
    }
    pub const fn refused(&self) -> u64 {
        self.refused
    }
    pub const fn step_invocations(&self) -> u64 {
        self.step_invocations
    }
    pub const fn ppc_persist_calls(&self) -> u64 {
        self.ppc_persist_calls
    }
    pub const fn egress_releases(&self) -> u64 {
        self.egress_releases
    }

    /// Irreversibly latch `halted = true` and return `false`.
    pub fn halt(&mut self, reason: HaltReason) -> bool {
        self.halted = true;
        if self.halt_reason.is_none() {
            self.halt_reason = Some(reason);
        }
        false
    }

    /// Process one staged ingress bundle through `commit-pd -> persist-pd [PPC digest ack] -> tx-egress-pd`:
    /// 1. **`CAP-28` Gate:** If `self.halted`, immediately `return false;` with zero side effects!
    /// 2. Copy shared ingress bundle into `private_slot` BEFORE verification (`copy_before_verify`),
    ///    using `after_copy_hook` so adversarial tests can mutate `shared_ingress_slot` mid-flight!
    /// 3. Verify capability access in `cspaces`, `height + 1`, `pre_state_root`, `FinCert` (`n - f`),
    ///    and `0x00/0x01` `IrreversibleOutbox` `effectsRoot`.
    /// 4. Stage leaf into `leaf_buf`, invoke synchronous PPC `persist_ppc`, and verify the returned
    ///    256-bit `PersistDigestAck` (`log_seq`, `leaf_digest`, `wal_root`, `fsynced`)! Any mismatch
    ///    halts `commit-pd` fail-closed before `tx-egress-pd` is ever notified!
    #[allow(clippy::too_many_arguments)]
    pub fn offer_bundle_with_persist<
        const SLOTS: usize,
        const MAX_CHAIN: usize,
        const MAX_SIGNERS: usize,
        const DEPTH: usize,
        const MAX_PAYLOAD: usize,
    >(
        &mut self,
        cspaces: &mut FourPdCspace<SLOTS>,
        ingress_ring_cap: CapHandle,
        leaf_buf_cap: CapHandle,
        persist_ppc_cap: CapHandle,
        egress_ring_cap: CapHandle,
        egress_ntfn_cap: CapHandle,
        shared_ingress_slot: &mut SovereignTurnBundle<
            OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>,
        >,
        after_copy_hook: impl FnOnce(
            &mut SovereignTurnBundle<OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>>,
        ),
        persist_ppc: impl FnOnce(usize, &[u8]) -> PersistDigestAck,
        tx_egress: &mut TxEgressPdState,
    ) -> bool {
        // CAP-28 FIX: Irreversible early return BEFORE any copy, verifier step, or IPC dispatch!
        if self.halted {
            return false;
        }

        // Verify Commit PD's read-only CSpace capability on `IngressRing` before copying.
        if cspaces
            .dispatch(
                ChokepointRole::Commit,
                CapRequest::MapSharedRegion {
                    region: ingress_ring_cap,
                    writable: false,
                    frame_bytes: MAX_PAYLOAD.min(MAX_IPC_FRAME_BYTES),
                },
            )
            .is_err()
        {
            return self.halt(HaltReason::CspaceCapabilityFault);
        }

        // Copy-Before-Verify: snapshot into Commit PD's private stack/frame before any check!
        let private_copy = *shared_ingress_slot;
        after_copy_hook(shared_ingress_slot);

        self.step_invocations = self.step_invocations.saturating_add(1);

        if self.log_len >= self.cap {
            self.refused = self.refused.saturating_add(1);
            return false;
        }

        let Some(next_height) = self.height.checked_add(1) else {
            return self.halt(HaltReason::CapacityExhausted);
        };
        if private_copy.public_inputs.height != next_height
            || !ct_eq_digest(&private_copy.public_inputs.pre_state_root, &self.committed_state_root)
            || private_copy.public_inputs.revoked_root == [0u8; 32]
            || !private_copy.last_row_gate_ok
            || !ct_eq_digest(
                &private_copy.effect_vk_digest,
                &private_copy.public_inputs.actor_vk_digest,
            )
        {
            self.hw = self.hw.saturating_add(1);
            self.refused = self.refused.saturating_add(1);
            return false;
        }

        let Ok(eff_commit) = self.verifier.check(
            &private_copy.public_inputs,
            &private_copy.challenge0,
            &private_copy.receipt,
        ) else {
            self.hw = self.hw.saturating_add(1);
            self.refused = self.refused.saturating_add(1);
            return false;
        };

        let payload_slice = &private_copy.receipt.payload[..private_copy.receipt.payload_len];
        let mut leaf_buf = [0u8; MAX_IPC_FRAME_BYTES];
        let Some(body_len) = format_staged_wal_leaf(
            private_copy.receipt.nullifier_id,
            &eff_commit,
            payload_slice,
            &mut leaf_buf,
        ) else {
            return self.halt(HaltReason::CapacityExhausted);
        };

        if cspaces
            .dispatch(
                ChokepointRole::Commit,
                CapRequest::MapSharedRegion {
                    region: leaf_buf_cap,
                    writable: true,
                    frame_bytes: 8 + body_len,
                },
            )
            .is_err()
            || cspaces
                .dispatch(
                    ChokepointRole::Commit,
                    CapRequest::InvokePersistPpc {
                        endpoint: persist_ppc_cap,
                        frame_bytes: body_len,
                    },
                )
                .is_err()
        {
            return self.halt(HaltReason::CspaceCapabilityFault);
        }

        // Synchronous PPC to `persist-pd`: must return matching 256-bit fsync digest ack BEFORE forward!
        self.ppc_persist_calls = self.ppc_persist_calls.saturating_add(1);
        let ack = persist_ppc(body_len, &leaf_buf[..8 + body_len]);
        let Some(expected_seq) = self.log_len.checked_add(1) else {
            return self.halt(HaltReason::CapacityExhausted);
        };
        if !ack.status_ok || !ack.fsynced || ack.log_seq != expected_seq {
            return self.halt(HaltReason::PersistAckFailed);
        }
        let alg = self.verifier.committee.hash_alg;
        let expected_leaf_digest =
            compute_persist_leaf_digest(alg, expected_seq, &leaf_buf[8..8 + body_len]);
        let expected_wal_root =
            advance_persist_wal_root(alg, &self.wal_root, expected_seq, &expected_leaf_digest);
        if !ct_eq_digest(&ack.leaf_digest, &expected_leaf_digest)
            || !ct_eq_digest(&ack.wal_root, &expected_wal_root)
        {
            return self.halt(HaltReason::PersistDigestMismatch);
        }

        if cspaces
            .dispatch(
                ChokepointRole::Commit,
                CapRequest::MapSharedRegion {
                    region: egress_ring_cap,
                    writable: true,
                    frame_bytes: private_copy.receipt.payload_len,
                },
            )
            .is_err()
            || cspaces
                .dispatch(
                    ChokepointRole::Commit,
                    CapRequest::Signal {
                        notif: egress_ntfn_cap,
                        claimed_badge: None,
                    },
                )
                .is_err()
        {
            return self.halt(HaltReason::CspaceCapabilityFault);
        }

        if !self
            .verifier
            .commit_turn(&private_copy.public_inputs, &private_copy.receipt)
        {
            return self.halt(HaltReason::CapacityExhausted);
        }

        let release_frame = EgressReleaseFrame {
            payload_len: private_copy.receipt.payload_len,
            payload: private_copy.receipt.payload,
            eff_commit,
            persist_ack: ack,
        };
        if tx_egress
            .try_release(private_copy.receipt.nullifier_id, &release_frame)
            .is_err()
        {
            return self.halt(HaltReason::EgressReleaseRejected);
        }

        self.hw = self.hw.saturating_add(1);
        self.ctr = self.hw;
        self.log_len = expected_seq;
        self.height = next_height;
        self.committed_state_root = private_copy.public_inputs.post_state_root;
        self.wal_root = expected_wal_root;
        self.forwarded = self.forwarded.saturating_add(1);
        self.egress_releases = self.egress_releases.saturating_add(1);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct CounterTrng {
        seed: u64,
        ready: bool,
        stuck_zero: bool,
    }
    impl HwTrngSource for CounterTrng {
        fn read_entropy(&mut self, out: &mut [u8]) -> bool {
            if !self.ready {
                return false;
            }
            if self.stuck_zero {
                out.fill(0);
                return true;
            }
            for b in out.iter_mut() {
                self.seed = self
                    .seed
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .wrapping_add(0xbf58_476d_1ce4_e5b9);
                *b = (self.seed >> 32) as u8 ^ (self.seed as u8);
            }
            true
        }
    }

    struct CanonicalHandles {
        ingress_ntfn: CapHandle,
        commit_ingress_ro: CapHandle,
        commit_leaf_rw: CapHandle,
        commit_ppc: CapHandle,
        commit_egress_rw: CapHandle,
        commit_egress_ntfn: CapHandle,
        persist_leaf_ro: CapHandle,
        persist_log_rw: CapHandle,
    }

    fn canonical_cspaces_and_handles(include_commit_trng: bool) -> (FourPdCspace<8>, CanonicalHandles) {
        let mut cs = FourPdCspace::<8>::new();
        // Ingress PD (disjoint global_cap_id 100..109)
        let _ = cs
            .pd_table_mut(ChokepointRole::Ingress)
            .install_root(
                0,
                100,
                KernelObject::SharedRegion {
                    region: SharedRegionId::IngressRing,
                    byte_len: 4096,
                },
                CapRights::RW,
                0,
            )
            .unwrap();
        let ingress_ntfn = cs
            .pd_table_mut(ChokepointRole::Ingress)
            .install_root(
                1,
                101,
                KernelObject::Notification { ntfn_id: 0 },
                CapRights::WO,
                0x10,
            )
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::Ingress)
            .install_root(
                2,
                102,
                KernelObject::Mmio {
                    kind: ApertureKind::RxNicMmio,
                    base_paddr: 0x0a00_3000,
                    byte_size: 0x1000,
                },
                CapRights::RW,
                0,
            )
            .unwrap();

        // Commit PD (disjoint global_cap_id 200..209)
        let commit_ingress_ro = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(
                0,
                200,
                KernelObject::SharedRegion {
                    region: SharedRegionId::IngressRing,
                    byte_len: 4096,
                },
                CapRights::RO,
                0,
            )
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(1, 201, KernelObject::PrivateFrame { pfn: 40 }, CapRights::RW, 0)
            .unwrap();
        let commit_leaf_rw = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(
                2,
                202,
                KernelObject::SharedRegion {
                    region: SharedRegionId::CommitLeafBuf,
                    byte_len: 4096,
                },
                CapRights::RW,
                0,
            )
            .unwrap();
        let commit_ppc = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(3, 203, KernelObject::PpcEndpoint { ep_id: 1 }, CapRights::WO, 0)
            .unwrap();
        let commit_egress_rw = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(
                4,
                204,
                KernelObject::SharedRegion {
                    region: SharedRegionId::EgressReleaseRing,
                    byte_len: 4096,
                },
                CapRights::RW,
                0,
            )
            .unwrap();
        let commit_egress_ntfn = cs
            .pd_table_mut(ChokepointRole::Commit)
            .install_root(
                5,
                205,
                KernelObject::Notification { ntfn_id: 1 },
                CapRights::WO,
                0x20,
            )
            .unwrap();
        if include_commit_trng {
            let _ = cs
                .pd_table_mut(ChokepointRole::Commit)
                .install_root(6, 206, KernelObject::HwTrng { trng_id: 0 }, CapRights::RO, 0)
                .unwrap();
        }

        // Persist PD (disjoint global_cap_id 300..309)
        let persist_leaf_ro = cs
            .pd_table_mut(ChokepointRole::Persist)
            .install_root(
                0,
                300,
                KernelObject::SharedRegion {
                    region: SharedRegionId::CommitLeafBuf,
                    byte_len: 4096,
                },
                CapRights::RO,
                0,
            )
            .unwrap();
        let persist_log_rw = cs
            .pd_table_mut(ChokepointRole::Persist)
            .install_root(
                1,
                301,
                KernelObject::SharedRegion {
                    region: SharedRegionId::PersistDurableLog,
                    byte_len: 0x10000,
                },
                CapRights::RW,
                0,
            )
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::Persist)
            .install_root(2, 302, KernelObject::PpcEndpoint { ep_id: 1 }, CapRights::RO, 0)
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::Persist)
            .install_root(
                3,
                303,
                KernelObject::Mmio {
                    kind: ApertureKind::DurableLogStorage,
                    base_paddr: 0x0b00_0000,
                    byte_size: 0x10000,
                },
                CapRights::RW,
                0,
            )
            .unwrap();

        // TxEgress PD (disjoint global_cap_id 400..409)
        let _ = cs
            .pd_table_mut(ChokepointRole::TxEgress)
            .install_root(
                0,
                400,
                KernelObject::SharedRegion {
                    region: SharedRegionId::EgressReleaseRing,
                    byte_len: 4096,
                },
                CapRights::RO,
                0,
            )
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::TxEgress)
            .install_root(
                1,
                401,
                KernelObject::Notification { ntfn_id: 1 },
                CapRights::RO,
                0,
            )
            .unwrap();
        let _ = cs
            .pd_table_mut(ChokepointRole::TxEgress)
            .install_root(
                2,
                402,
                KernelObject::Mmio {
                    kind: ApertureKind::TxNicMmio,
                    base_paddr: 0x0a00_4000,
                    byte_size: 0x1000,
                },
                CapRights::RW,
                0,
            )
            .unwrap();

        (
            cs,
            CanonicalHandles {
                ingress_ntfn,
                commit_ingress_ro,
                commit_leaf_rw,
                commit_ppc,
                commit_egress_rw,
                commit_egress_ntfn,
                persist_leaf_ro,
                persist_log_rw,
            },
        )
    }

    const RX_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
        kind: ApertureKind::RxNicMmio,
        base_paddr: 0x0a00_3000,
        byte_size: 0x1000,
        writable: true,
    }];
    const PERSIST_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
        kind: ApertureKind::DurableLogStorage,
        base_paddr: 0x0b00_0000,
        byte_size: 0x10000,
        writable: true,
    }];
    const TX_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
        kind: ApertureKind::TxNicMmio,
        base_paddr: 0x0a00_4000,
        byte_size: 0x1000,
        writable: true,
    }];
    const VALID_CHANNELS: [DirectedIpcChannel; 3] = [
        DirectedIpcChannel {
            channel_id: 0,
            src: ChokepointRole::Ingress,
            dst: ChokepointRole::Commit,
            kind: ChokepointChannelKind::OneWaySpsc,
            max_payload_bytes: 4096,
            callee_consumes_caller_irq: false,
        },
        DirectedIpcChannel {
            channel_id: 1,
            src: ChokepointRole::Commit,
            dst: ChokepointRole::Persist,
            kind: ChokepointChannelKind::ProtectedPersistPpc,
            max_payload_bytes: 4096,
            callee_consumes_caller_irq: false,
        },
        DirectedIpcChannel {
            channel_id: 2,
            src: ChokepointRole::Commit,
            dst: ChokepointRole::TxEgress,
            kind: ChokepointChannelKind::OneWaySpsc,
            max_payload_bytes: 4096,
            callee_consumes_caller_irq: false,
        },
    ];

    fn canonical_system_desc<'a>(channels: &'a [DirectedIpcChannel]) -> ChokepointSystemDesc<'a> {
        // Boot-evidence rootserver span `0x60246000..0x60a05000` (8,122,368 B < 10 MiB)
        ChokepointSystemDesc {
            rootserver_phys_start: 0x6024_6000,
            rootserver_phys_end: 0x60a0_5000,
            domains: [
                ChokepointPdDesc {
                    pd_id: 1,
                    role: ChokepointRole::Ingress,
                    name: b"ingress-pd",
                    priority: 90,
                    elf_footprint_bytes: 256 * 1024,
                    stack_and_heap_bytes: 128 * 1024,
                    apertures: &RX_APERTURES,
                },
                ChokepointPdDesc {
                    pd_id: 2,
                    role: ChokepointRole::Commit,
                    name: b"commit-pd",
                    priority: 100,
                    elf_footprint_bytes: 4 * 1024 * 1024,
                    stack_and_heap_bytes: 512 * 1024,
                    apertures: &[],
                },
                ChokepointPdDesc {
                    pd_id: 3,
                    role: ChokepointRole::Persist,
                    name: b"persist-pd",
                    priority: 200,
                    elf_footprint_bytes: 192 * 1024,
                    stack_and_heap_bytes: 128 * 1024,
                    apertures: &PERSIST_APERTURES,
                },
                ChokepointPdDesc {
                    pd_id: 4,
                    role: ChokepointRole::TxEgress,
                    name: b"tx-egress-pd",
                    priority: 150,
                    elf_footprint_bytes: 256 * 1024,
                    stack_and_heap_bytes: 128 * 1024,
                    apertures: &TX_APERTURES,
                },
            ],
            channels,
        }
    }

    #[test]
    fn four_pd_descriptor_enforces_topology_span_budget_and_blocks_ingress_egress_bypass() {
        let (cspaces, _) = canonical_cspaces_and_handles(false);
        let good = canonical_system_desc(&VALID_CHANNELS);
        assert_eq!(
            good.rootserver_phys_end - good.rootserver_phys_start,
            8_122_368
        );
        assert_eq!(verify_chokepoint_system(&good, &cspaces), Ok(()));

        // 1. Direct `ingress-pd -> tx-egress-pd` bypass channel is strictly rejected!
        let bypass_channels = [
            VALID_CHANNELS[0],
            VALID_CHANNELS[1],
            VALID_CHANNELS[2],
            DirectedIpcChannel {
                channel_id: 9,
                src: ChokepointRole::Ingress,
                dst: ChokepointRole::TxEgress,
                kind: ChokepointChannelKind::OneWaySpsc,
                max_payload_bytes: 512,
                callee_consumes_caller_irq: false,
            },
        ];
        assert_eq!(
            verify_chokepoint_system(&canonical_system_desc(&bypass_channels), &cspaces),
            Err(ChokepointViolation::DirectIngressToEgressBypass)
        );

        // 2. Direct `ingress-pd -> persist-pd` or `tx-egress-pd -> commit-pd` callback is rejected!
        let bad_edge = [
            VALID_CHANNELS[0],
            VALID_CHANNELS[1],
            VALID_CHANNELS[2],
            DirectedIpcChannel {
                channel_id: 10,
                src: ChokepointRole::Ingress,
                dst: ChokepointRole::Persist,
                kind: ChokepointChannelKind::OneWaySpsc,
                max_payload_bytes: 512,
                callee_consumes_caller_irq: false,
            },
        ];
        assert_eq!(
            verify_chokepoint_system(&canonical_system_desc(&bad_edge), &cspaces),
            Err(ChokepointViolation::ForbiddenChannelTopology {
                src: ChokepointRole::Ingress,
                dst: ChokepointRole::Persist,
            })
        );

        // 3. Root-server physical span `>= 10 MiB` (e.g. 10 MiB exact or 285 MiB mathlib ELF) rejected!
        let mut exact_10mib = good;
        exact_10mib.rootserver_phys_end =
            exact_10mib.rootserver_phys_start + MAX_ROOTSERVER_SPAN_BYTES;
        assert_eq!(
            verify_chokepoint_system(&exact_10mib, &cspaces),
            Err(ChokepointViolation::RootServerSpanBudgetExceeded {
                span_bytes: MAX_ROOTSERVER_SPAN_BYTES,
                limit_bytes: MAX_ROOTSERVER_SPAN_BYTES,
            })
        );
        let mut bloated_285mib = good;
        bloated_285mib.rootserver_phys_end = 0x7860_d000;
        assert!(matches!(
            verify_chokepoint_system(&bloated_285mib, &cspaces),
            Err(ChokepointViolation::RootServerSpanBudgetExceeded { .. })
        ));

        // 4. Microkit PPC priority inversion (`persist_prio <= commit_prio`) & `persist_can_wait_on_nic_irq` rejected!
        let mut bad_prio = good;
        bad_prio.domains[ChokepointRole::Persist.index()].priority = 100;
        assert_eq!(
            verify_chokepoint_system(&bad_prio, &cspaces),
            Err(ChokepointViolation::InvalidPpcPriority {
                commit_prio: 100,
                persist_prio: 100,
            })
        );
        let mut irq_leak_ch = VALID_CHANNELS;
        irq_leak_ch[1].callee_consumes_caller_irq = true;
        assert_eq!(
            verify_chokepoint_system(&canonical_system_desc(&irq_leak_ch), &cspaces),
            Err(ChokepointViolation::CalleeConsumesCallerIrq { channel_id: 1 })
        );
    }

    #[test]
    fn cap03_per_pd_disjoint_cspaces_defeat_global_slot_zero_confused_deputy() {
        let (mut cs, handles) = canonical_cspaces_and_handles(false);

        // 1. Guessing global `(slot, 0)` (the exact `ProcessKernel` CAP-03 exploit) fails in every PD!
        for slot in 0..8 {
            assert_eq!(
                cs.dispatch(
                    ChokepointRole::Ingress,
                    CapRequest::MapSharedRegion {
                        region: CapHandle { slot, epoch: 0 },
                        writable: false,
                        frame_bytes: 64,
                    },
                ),
                Err(CapFault::StaleOrZeroEpoch)
            );
        }

        // 2. Ingress presenting Persist's `durable_log` handle (`slot = 1, epoch = 2`) hits Ingress's own
        //    CSpace (which holds a Notification at slot 1, NOT `PersistDurableLog`), refusing `MapSharedRegion`!
        assert_eq!(
            cs.dispatch(
                ChokepointRole::Ingress,
                CapRequest::MapSharedRegion {
                    region: handles.persist_log_rw,
                    writable: true,
                    frame_bytes: 64,
                },
            ),
            Err(CapFault::WrongObjectKind)
        );

        // 3. Ingress attempting to spoof badge `0xDEAD` on its notification cap (`bound_badge = 0x10`) fails!
        assert_eq!(
            cs.dispatch(
                ChokepointRole::Ingress,
                CapRequest::Signal {
                    notif: handles.ingress_ntfn,
                    claimed_badge: Some(0xDEAD),
                },
            ),
            Err(CapFault::BadgeSpoofAttempt {
                attempted: 0xDEAD,
                kernel_bound: 0x10,
            })
        );
        assert_eq!(
            cs.dispatch(
                ChokepointRole::Ingress,
                CapRequest::Signal {
                    notif: handles.ingress_ntfn,
                    claimed_badge: None,
                },
            ),
            Ok(CapReply::Signalled {
                delivered_badge: 0x10
            })
        );

        // 4. Persist attempting writable mapping of `leaf_buf` (granted `RO`) fails!
        assert_eq!(
            cs.dispatch(
                ChokepointRole::Persist,
                CapRequest::MapSharedRegion {
                    region: handles.persist_leaf_ro,
                    writable: true,
                    frame_bytes: 64,
                },
            ),
            Err(CapFault::InsufficientRights)
        );

        // 5. Oversized `u32` IPC frame (> 4096 B) fails before allocation!
        assert_eq!(
            cs.dispatch(
                ChokepointRole::Persist,
                CapRequest::MapSharedRegion {
                    region: handles.persist_log_rw,
                    writable: true,
                    frame_bytes: MAX_IPC_FRAME_BYTES + 1,
                },
            ),
            Err(CapFault::FrameExceedsMaxBytes {
                requested: MAX_IPC_FRAME_BYTES + 1,
                max: MAX_IPC_FRAME_BYTES,
            })
        );

        // 6. Transitive CSpace revocation severs children + grandchildren and invalidates old epochs!
        let child = cs
            .pd_table_mut(ChokepointRole::Persist)
            .mint_attenuated(handles.persist_log_rw, 5, 305, CapRights::RW, 0)
            .unwrap();
        let grandchild = cs
            .pd_table_mut(ChokepointRole::Persist)
            .mint_attenuated(child, 6, 306, CapRights::RO, 0)
            .unwrap();
        assert_eq!(
            cs.pd_table_mut(ChokepointRole::Persist)
                .revoke_slot_and_descendants(handles.persist_log_rw.slot),
            Ok(3)
        );
        for dead in [handles.persist_log_rw, child, grandchild] {
            assert_eq!(
                cs.pd_table(ChokepointRole::Persist).resolve(dead),
                Err(CapFault::StaleOrZeroEpoch)
            );
        }

        // 7. Descriptor check rejects CSpace tables that share a `global_cap_id` across two PDs!
        let (mut colliding_cs, _) = canonical_cspaces_and_handles(false);
        let _ = colliding_cs
            .pd_table_mut(ChokepointRole::TxEgress)
            .install_root(
                7,
                201, // collides with Commit's global_cap_id 201!
                KernelObject::Notification { ntfn_id: 2 },
                CapRights::RO,
                0,
            )
            .unwrap();
        assert_eq!(
            verify_chokepoint_system(&canonical_system_desc(&VALID_CHANNELS), &colliding_cs),
            Err(ChokepointViolation::DuplicateGlobalCapId { global_cap_id: 201 })
        );
    }

    #[test]
    fn cap29_getrandom_and_urandom_fail_closed_with_enosys_unless_hw_trng_cap_present() {
        let (cs_no_trng, _) = canonical_cspaces_and_handles(false);
        let mut trng = CounterTrng {
            seed: 0x1234_5678_9abc_def0,
            ready: true,
            stuck_zero: false,
        };
        let mut sentinel = [0xAAu8; 32];

        // 1. Without `HwTrng` cap in Commit's CSpace, `GETRANDOM` returns `-ENOSYS` and NEVER zero-fills `sentinel`!
        assert_eq!(
            PdSyscallGate::dispatch_syscall(
                &cs_no_trng,
                ChokepointRole::Commit,
                linux_aarch64_nr::GETRANDOM,
                None,
                -1,
                Some(&mut sentinel),
                Some(&mut trng),
            ),
            -ERRNO_ENOSYS
        );
        assert_eq!(sentinel, [0xAAu8; 32]);

        // 2. `/dev/urandom` & `/dev/random` `OPENAT` return `-ENOSYS`, and `READ` on sentinel fd `1000` returns `-EBADF`!
        for path in [&b"/dev/urandom"[..], &b"/dev/random"[..]] {
            assert_eq!(
                PdSyscallGate::dispatch_syscall(
                    &cs_no_trng,
                    ChokepointRole::Commit,
                    linux_aarch64_nr::OPENAT,
                    Some(path),
                    -1,
                    None,
                    Some(&mut trng),
                ),
                -ERRNO_ENOSYS
            );
        }
        assert_eq!(
            PdSyscallGate::dispatch_syscall(
                &cs_no_trng,
                ChokepointRole::Commit,
                linux_aarch64_nr::READ,
                None,
                1000,
                Some(&mut sentinel),
                Some(&mut trng),
            ),
            -ERRNO_EBADF
        );
        assert_eq!(sentinel, [0xAAu8; 32]);

        // 3. With explicit `HwTrng` cap in Commit's CSpace: healthy TRNG succeeds; stuck-zero TRNG fails with `-EIO`!
        let (mut cs_with_trng, _) = canonical_cspaces_and_handles(true);
        let mut stuck = CounterTrng {
            seed: 1,
            ready: true,
            stuck_zero: true,
        };
        assert_eq!(
            PdSyscallGate::dispatch_syscall(
                &cs_with_trng,
                ChokepointRole::Commit,
                linux_aarch64_nr::GETRANDOM,
                None,
                -1,
                Some(&mut sentinel),
                Some(&mut stuck),
            ),
            -ERRNO_EIO
        );
        assert_eq!(sentinel, [0xAAu8; 32]);

        assert_eq!(
            PdSyscallGate::dispatch_syscall(
                &cs_with_trng,
                ChokepointRole::Commit,
                linux_aarch64_nr::GETRANDOM,
                None,
                -1,
                Some(&mut sentinel),
                Some(&mut trng),
            ),
            32
        );
        assert_ne!(sentinel, [0xAAu8; 32]);
        assert_ne!(sentinel, [0x00u8; 32]);

        // Revoking slot 6 (`HwTrng`) immediately restores `-ENOSYS`!
        assert_eq!(
            cs_with_trng
                .pd_table_mut(ChokepointRole::Commit)
                .revoke_slot_and_descendants(6),
            Ok(1)
        );
        let prev = sentinel;
        assert_eq!(
            PdSyscallGate::dispatch_syscall(
                &cs_with_trng,
                ChokepointRole::Commit,
                linux_aarch64_nr::GETRANDOM,
                None,
                -1,
                Some(&mut sentinel),
                Some(&mut trng),
            ),
            -ERRNO_ENOSYS
        );
        assert_eq!(sentinel, prev);
    }

    type ChokepointReceipt = OutboxTurnReceipt<2, 5, 1, 64>;

    struct PreparedTurnSpec<'a> {
        pre_state_root: Digest,
        post_state_root: Digest,
        nullifier_id: u64,
        high_water: u64,
        height: u64,
        view: u64,
        payload_bytes: &'a [u8],
    }

    fn build_two_turn_chokepoint_suite(
        alg: OutboxHashAlg,
        t1: PreparedTurnSpec<'_>,
        t2: PreparedTurnSpec<'_>,
    ) -> (
        OutboxFinalityVerifier<5, 2>,
        SovereignTurnBundle<ChokepointReceipt>,
        SovereignTurnBundle<ChokepointReceipt>,
    ) {
        fn prep_tree_and_chain(
            alg: OutboxHashAlg,
            spec: &PreparedTurnSpec<'_>,
        ) -> (
            [u8; 64],
            Digest,
            Digest,
            [Digest; 1],
            [SimplexChainEntry; 2],
        ) {
            let mut payload = [0u8; 64];
            payload[..spec.payload_bytes.len()].copy_from_slice(spec.payload_bytes);
            let eff_commit = effect_commit_digest(
                alg,
                spec.nullifier_id,
                OutboxEffectClass::IrreversibleActuation,
                spec.payload_bytes,
            );
            let sibling_commit =
                effect_commit_digest(alg, 999, OutboxEffectClass::IdempotentRead, b"telemetry");
            let tree = EffectsMerkleTree::from_commits([eff_commit, sibling_commit]).unwrap();
            let effects_root = tree.root(alg);
            let merkle_siblings: [Digest; 1] = tree.open(alg, 0).unwrap();
            let tip_payload = block_effects_payload(alg, &spec.post_state_root, &effects_root);
            let chain = [
                SimplexChainEntry::EmptyView { view: 1 },
                SimplexChainEntry::Block {
                    view: spec.view,
                    payload: tip_payload,
                },
            ];
            (payload, eff_commit, effects_root, merkle_siblings, chain)
        }

        let (pay1, eff1, root1, sib1, chain1) = prep_tree_and_chain(alg, &t1);
        let (pay2, eff2, root2, sib2, chain2) = prep_tree_and_chain(alg, &t2);
        assert_eq!(t2.view, t1.view + 1);

        let mut slot_pubkeys = [[[0u8; 32]; 5]; 2];
        let mut votes1 = [ValidatorFinalizeVote::ZERO; 5];
        let mut votes2 = [ValidatorFinalizeVote::ZERO; 5];
        for i in 0..5 {
            let mut salt1 = [0x33u8; 32];
            salt1[0] = (i as u8) + 1;
            let mut salt2 = [0x77u8; 32];
            salt2[0] = (i as u8) + 1;
            slot_pubkeys[0][i] =
                derive_finalize_slot_pubkey(alg, i as u64, t1.view, &chain1, &salt1).unwrap();
            slot_pubkeys[1][i] =
                derive_finalize_slot_pubkey(alg, i as u64, t2.view, &chain2, &salt2).unwrap();
            if i < 4 {
                votes1[i] = ValidatorFinalizeVote {
                    signer_id: i as u64,
                    sig_salt: salt1,
                };
                votes2[i] = ValidatorFinalizeVote {
                    signer_id: i as u64,
                    sig_salt: salt2,
                };
            }
        }
        let committee = SimplexCommittee {
            n: 5,
            f: 1,
            base_view: t1.view,
            active_views: 2,
            hash_alg: alg,
            slot_pubkeys,
        };
        let verifier = OutboxFinalityVerifier {
            circuit_digest: [0x51; 32],
            authorized_cap_root: [0x61; 32],
            gatekeeper_pd: 2,
            high_water_nullifier: t1.high_water,
            committee,
        };
        let mk_bundle = |spec: &PreparedTurnSpec<'_>,
                         payload: [u8; 64],
                         eff_commit: Digest,
                         effects_root: Digest,
                         merkle_siblings: [Digest; 1],
                         chain: [SimplexChainEntry; 2],
                         votes: [ValidatorFinalizeVote; 5]| {
            let pi = FullPinnedPublicInputs {
                circuit_desc_digest: verifier.circuit_digest,
                actor_vk_digest: committee.directory_digest(),
                pre_state_root: spec.pre_state_root,
                post_state_root: spec.post_state_root,
                cap_root: verifier.authorized_cap_root,
                revoked_root: outbox_window_digest(alg, verifier.gatekeeper_pd, spec.high_water),
                height: spec.height,
                turn_hash: outbox_turn_digest(alg, &eff_commit, &effects_root, 0),
            };
            let challenge0 = pi.transcript().squeeze();
            let receipt = OutboxTurnReceipt {
                nullifier_id: spec.nullifier_id,
                leaf_index: 0,
                effects_root,
                merkle_siblings,
                payload_len: spec.payload_bytes.len(),
                payload,
                fin_cert: SimplexFinCert {
                    view: spec.view,
                    chain_len: 2,
                    chain,
                    vote_count: 4,
                    votes,
                },
            };
            SovereignTurnBundle {
                public_inputs: pi,
                challenge0,
                effect_vk_digest: pi.actor_vk_digest,
                last_row_gate_ok: true,
                receipt,
            }
        };
        let b1 = mk_bundle(&t1, pay1, eff1, root1, sib1, chain1, votes1);
        let b2 = mk_bundle(&t2, pay2, eff2, root2, sib2, chain2, votes2);
        (verifier, b1, b2)
    }

    #[test]
    fn cap28_commit_pd_halted_latch_is_irreversible_and_gates_tx_egress_on_persist_digest_ack() {
        let alg = OutboxHashAlg::Cshake256;
        let genesis_state = [0x10; 32];
        let post_state_1 = [0x20; 32];
        let post_state_2 = [0x30; 32];
        let genesis_wal = [0x70; 32];

        let (mut cs, handles) = canonical_cspaces_and_handles(false);
        assert_eq!(
            verify_chokepoint_system(&canonical_system_desc(&VALID_CHANNELS), &cs),
            Ok(())
        );

        let (v1, mut b1, b2_honest) = build_two_turn_chokepoint_suite(
            alg,
            PreparedTurnSpec {
                pre_state_root: genesis_state,
                post_state_root: post_state_1,
                nullifier_id: 1,
                high_water: 0,
                height: 1,
                view: 2,
                payload_bytes: b"wire-tx-001",
            },
            PreparedTurnSpec {
                pre_state_root: post_state_1,
                post_state_root: post_state_2,
                nullifier_id: 2,
                high_water: 1,
                height: 2,
                view: 3,
                payload_bytes: b"wire-tx-002",
            },
        );
        let mut commit = CommitPdMonitor::new(v1, genesis_state, genesis_wal, 4);
        let mut persist = PersistPdState::<4096>::new(alg, genesis_wal);
        let mut egress = TxEgressPdState::new(alg, genesis_wal);

        // 1. Honest turn 1 with concurrent TOCTOU shared-ring overwrite after copy-before-verify:
        //    private copy verifies, `persist-pd` returns fsync digest ack, `tx-egress-pd` emits 1 packet!
        let ok1 = commit.offer_bundle_with_persist(
            &mut cs,
            handles.commit_ingress_ro,
            handles.commit_leaf_rw,
            handles.commit_ppc,
            handles.commit_egress_rw,
            handles.commit_egress_ntfn,
            &mut b1,
            |racing_ring| {
                racing_ring.receipt.payload.fill(0xFF);
                racing_ring.public_inputs.post_state_root = [0xEE; 32];
            },
            |n, leaf_ro| persist.handle_ppc_append(n, leaf_ro),
            &mut egress,
        );
        assert!(ok1);
        assert!(!commit.is_halted());
        assert_eq!(commit.forwarded(), 1);
        assert_eq!(commit.log_len(), 1);
        assert_eq!(persist.entries(), 1);
        assert_eq!(egress.tx_packets_emitted(), 1);

        // 2. Direct `tx-egress-pd` bypass attempt with count-matching (`log_seq = 2`) but forged/swapped
        //    digest ack (`T4` count-only ack swap) is strictly refused by `TxEgressPdState`!
        let forged_release = EgressReleaseFrame {
            payload_len: b2_honest.receipt.payload_len,
            payload: b2_honest.receipt.payload,
            eff_commit: [0xAB; 32],
            persist_ack: PersistDigestAck {
                status_ok: true,
                fsynced: true,
                log_seq: 2,
                leaf_digest: [0xCD; 32], // wrong digest for payload!
                wal_root: [0xEF; 32],
            },
        };
        assert_eq!(
            egress.try_release(2, &forged_release),
            Err(TxReleaseRefusal::PersistLeafDigestMismatch)
        );
        assert_eq!(egress.tx_packets_emitted(), 1);

        // 3. Turn 2 where `persist-pd` returns count-matching `log_seq = 2` with a tampered leaf digest:
        //    `commit-pd` latches `halted = true` (`PersistDigestMismatch`) BEFORE signalling `tx-egress-pd`!
        let mut b2 = b2_honest;
        let ok2 = commit.offer_bundle_with_persist(
            &mut cs,
            handles.commit_ingress_ro,
            handles.commit_leaf_rw,
            handles.commit_ppc,
            handles.commit_egress_rw,
            handles.commit_egress_ntfn,
            &mut b2,
            |_| {},
            |n, leaf_ro| {
                let mut ack = persist.handle_ppc_append(n, leaf_ro);
                ack.leaf_digest[0] ^= 0x01; // T4 count-matching digest corruption!
                ack
            },
            &mut egress,
        );
        assert!(!ok2);
        assert!(commit.is_halted());
        assert_eq!(commit.halt_reason(), Some(HaltReason::PersistDigestMismatch));
        assert_eq!(egress.tx_packets_emitted(), 1);
        assert_eq!(commit.forwarded(), 1);

        // 4. CAP-28 PROOF: Once `halted == true`, offering a completely valid Turn 2 immediately
        //    returns `false` BEFORE step invocation, BEFORE PPC dispatch, and mutates ZERO counters!
        let snap_steps = commit.step_invocations();
        let snap_ppcs = commit.ppc_persist_calls();
        let snap_hw = commit.hw();
        let snap_ctr = commit.ctr();
        let snap_log = commit.log_len();
        let snap_fwd = commit.forwarded();
        let snap_ref = commit.refused();
        let snap_wal = commit.wal_root();
        let mut ppc_called_while_halted = false;
        let mut copy_hook_called_while_halted = false;

        let mut b2_retry = b2_honest;
        let ok_after_halt = commit.offer_bundle_with_persist(
            &mut cs,
            handles.commit_ingress_ro,
            handles.commit_leaf_rw,
            handles.commit_ppc,
            handles.commit_egress_rw,
            handles.commit_egress_ntfn,
            &mut b2_retry,
            |_| {
                copy_hook_called_while_halted = true;
            },
            |n, leaf_ro| {
                ppc_called_while_halted = true;
                persist.handle_ppc_append(n, leaf_ro)
            },
            &mut egress,
        );
        assert!(!ok_after_halt);
        assert!(commit.is_halted());
        assert!(!copy_hook_called_while_halted);
        assert!(!ppc_called_while_halted);
        assert_eq!(commit.step_invocations(), snap_steps);
        assert_eq!(commit.ppc_persist_calls(), snap_ppcs);
        assert_eq!(commit.hw(), snap_hw);
        assert_eq!(commit.ctr(), snap_ctr);
        assert_eq!(commit.log_len(), snap_log);
        assert_eq!(commit.forwarded(), snap_fwd);
        assert_eq!(commit.refused(), snap_ref);
        assert_eq!(commit.wal_root(), snap_wal);
        assert_eq!(egress.tx_packets_emitted(), 1);
    }
}
