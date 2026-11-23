//! Comprehensive positive, adversarial, fuzzing, XML/DTB emission, and golden-digest
//! integration tests for `obend_sel4_verifier::iommu` (SHE Gap #2).

use obend_sel4_verifier::*;

const RX_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
    kind: ApertureKind::RxNicMmio,
    base_paddr: 0x0a00_3000,
    byte_size: 0x1000,
    writable: true,
}];
const COMMIT_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
    kind: ApertureKind::HardwareTrngMmio,
    base_paddr: 0x0900_0000,
    byte_size: 0x1000,
    writable: false,
}];
const PERSIST_APERTURES: [PdMmioAperture; 1] = [PdMmioAperture {
    kind: ApertureKind::DurableLogStorage,
    base_paddr: 0x0b00_0000,
    byte_size: 0x1_0000,
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

// Commit PD's private copy-before-verify frame sits at pfn = 0x60100 (paddr = 0x6010_0000).
const COMMIT_PRIVATE_PFN: u64 = 0x6_0100;
const COMMIT_PRIVATE_PADDR: u64 = COMMIT_PRIVATE_PFN * PAGE_SIZE_4K;

const PROTECTED_RANGES: [ProtectedFrameRange; 4] = [
    ProtectedFrameRange {
        class: ProtectedFrameClass::CommitPrivate,
        base_paddr: COMMIT_PRIVATE_PADDR,
        size: 4 * PAGE_SIZE_4K,
    },
    ProtectedFrameRange {
        class: ProtectedFrameClass::PdCodeStackCspace,
        base_paddr: 0x6011_0000,
        size: 64 * PAGE_SIZE_4K,
    },
    ProtectedFrameRange {
        class: ProtectedFrameClass::TrngMmio,
        base_paddr: 0x0900_0000,
        size: PAGE_SIZE_4K,
    },
    ProtectedFrameRange {
        class: ProtectedFrameClass::KernelPageTable,
        base_paddr: 0x6015_0000,
        size: 32 * PAGE_SIZE_4K,
    },
];

// DMA pool sits cleanly after root-server span `0x6024_6000..0x60a0_5000` (8,122,368 B).
// Pool size = 512 KiB (`0x8_0000`), total = 8,646,656 B < 10 MiB (`10,485,760` B).
const DMA_POOL_BASE: u64 = 0x60a0_5000;
const DMA_POOL_SIZE: u64 = 512 * 1024;

const INGRESS_REGIONS: [DmaRegion; 1] = [DmaRegion {
    iova: 0x1000_0000,
    paddr: DMA_POOL_BASE,
    size: 16 * PAGE_SIZE_4K,
    granule: PageGranule::Page4KiB,
    perm: IoPerm::ReadWrite,
    kind: DmaRegionKind::IngressRing,
}];
const PERSIST_REGIONS: [DmaRegion; 1] = [DmaRegion {
    iova: 0x2000_0000,
    paddr: DMA_POOL_BASE + 0x1_0000,
    size: 32 * PAGE_SIZE_4K,
    granule: PageGranule::Page4KiB,
    perm: IoPerm::ReadWrite,
    kind: DmaRegionKind::PersistWalPool,
}];
const EGRESS_REGIONS: [DmaRegion; 1] = [DmaRegion {
    iova: 0x3000_0000,
    paddr: DMA_POOL_BASE + 0x3_0000,
    size: 16 * PAGE_SIZE_4K,
    granule: PageGranule::Page4KiB,
    perm: IoPerm::ReadOnly,
    kind: DmaRegionKind::EgressOutboxRing,
}];
const DISPLAY_REGIONS: [DmaRegion; 1] = [DmaRegion {
    iova: 0x4000_0000,
    paddr: DMA_POOL_BASE + 0x4_0000,
    size: 16 * PAGE_SIZE_4K,
    granule: PageGranule::Page4KiB,
    perm: IoPerm::ReadOnly,
    kind: DmaRegionKind::DisplayFramebuffer,
}];
const CAMERA_REGIONS: [DmaRegion; 1] = [DmaRegion {
    iova: 0x5000_0000,
    paddr: DMA_POOL_BASE + 0x5_0000,
    size: 16 * PAGE_SIZE_4K,
    granule: PageGranule::Page4KiB,
    perm: IoPerm::WriteOnly,
    kind: DmaRegionKind::CameraRing,
}];

const CANONICAL_STREAMS: [DeviceStreamBinding<'static>; 5] = [
    DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &INGRESS_REGIONS,
    },
    DeviceStreamBinding {
        stream_id: StreamId(0x20),
        role: DeviceRole::PersistNvme,
        owner_pd: ChokepointRole::Persist,
        regions: &PERSIST_REGIONS,
    },
    DeviceStreamBinding {
        stream_id: StreamId(0x30),
        role: DeviceRole::EgressNic,
        owner_pd: ChokepointRole::TxEgress,
        regions: &EGRESS_REGIONS,
    },
    DeviceStreamBinding {
        stream_id: StreamId(0x40),
        role: DeviceRole::DisplayScanout,
        owner_pd: ChokepointRole::TxEgress,
        regions: &DISPLAY_REGIONS,
    },
    DeviceStreamBinding {
        stream_id: StreamId(0x50),
        role: DeviceRole::CameraCsi2,
        owner_pd: ChokepointRole::Ingress,
        regions: &CAMERA_REGIONS,
    },
];

fn canonical_policy() -> ChokepointIommuPolicy<'static> {
    ChokepointIommuPolicy {
        arch: IommuArch::ArmSmmuV3,
        default_deny_unmapped: true,
        rootserver_phys_start: 0x6024_6000,
        rootserver_phys_end: 0x60a0_5000,
        dma_pool_base: DMA_POOL_BASE,
        dma_pool_size: DMA_POOL_SIZE,
        protected_ranges: &PROTECTED_RANGES,
        streams: &CANONICAL_STREAMS,
    }
}

fn canonical_system_desc() -> ChokepointSystemDesc<'static> {
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
                apertures: &COMMIT_APERTURES,
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
        channels: &VALID_CHANNELS,
    }
}

fn canonical_cspaces() -> FourPdCspace<8> {
    let mut cs = FourPdCspace::<8>::new();
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
    let _ = cs
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

    let _ = cs
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
        .install_root(
            1,
            201,
            KernelObject::PrivateFrame {
                pfn: COMMIT_PRIVATE_PFN,
            },
            CapRights::RW,
            0,
        )
        .unwrap();
    let _ = cs
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
    let _ = cs
        .pd_table_mut(ChokepointRole::Commit)
        .install_root(3, 203, KernelObject::PpcEndpoint { ep_id: 1 }, CapRights::WO, 0)
        .unwrap();
    let _ = cs
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
    let _ = cs
        .pd_table_mut(ChokepointRole::Commit)
        .install_root(
            5,
            205,
            KernelObject::Notification { ntfn_id: 1 },
            CapRights::WO,
            0x20,
        )
        .unwrap();
    let _ = cs
        .pd_table_mut(ChokepointRole::Commit)
        .install_root(6, 206, KernelObject::HwTrng { trng_id: 0 }, CapRights::RO, 0)
        .unwrap();

    let _ = cs
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
    let _ = cs
        .pd_table_mut(ChokepointRole::Persist)
        .install_root(
            1,
            301,
            KernelObject::SharedRegion {
                region: SharedRegionId::PersistDurableLog,
                byte_len: 0x1_0000,
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
                byte_size: 0x1_0000,
            },
            CapRights::RW,
            0,
        )
        .unwrap();

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
    cs
}

#[test]
fn canonical_four_pd_smmu_and_riscv_iommu_policies_verify_and_support_2mib_huge_pages() {
    let desc = canonical_system_desc();
    let cs = canonical_cspaces();
    let arm_policy = canonical_policy();

    let d_arm = verify_chokepoint_with_iommu(&desc, &cs, &arm_policy).expect("ARM SMMUv3 valid");
    assert_ne!(d_arm, [0u8; 32]);
    assert!(arm_policy.physical_range_is_dma_unreachable(COMMIT_PRIVATE_PADDR, 4 * PAGE_SIZE_4K));

    let mut rv_policy = arm_policy;
    rv_policy.arch = IommuArch::RiscvIommu;
    let d_rv = verify_chokepoint_with_iommu(&desc, &cs, &rv_policy).expect("RISC-V IOMMU valid");
    assert_ne!(d_arm, d_rv, "manifest digest must bind IOMMU architecture");

    // 2 MiB huge-page alignment positive test within `< 10 MiB` budget (6 MiB root + 2 MiB DMA = 8 MiB).
    let huge_regions = [DmaRegion {
        iova: 0x2000_0000,
        paddr: 0x6080_0000,
        size: PAGE_SIZE_2M,
        granule: PageGranule::Huge2MiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::PersistWalPool,
    }];
    let huge_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x21),
        role: DeviceRole::PersistNvme,
        owner_pd: ChokepointRole::Persist,
        regions: &huge_regions,
    }];
    let huge_policy = ChokepointIommuPolicy {
        arch: IommuArch::RiscvIommu,
        default_deny_unmapped: true,
        rootserver_phys_start: 0x6020_0000,
        rootserver_phys_end: 0x6080_0000,
        dma_pool_base: 0x6080_0000,
        dma_pool_size: PAGE_SIZE_2M,
        protected_ranges: &PROTECTED_RANGES,
        streams: &huge_streams,
    };
    assert!(verify_iommu_policy(&huge_policy).is_ok());
}

#[test]
fn refuses_protected_frame_trng_rootserver_and_cspace_private_frame_overlaps() {
    let desc = canonical_system_desc();
    let cs = canonical_cspaces();

    // 1. Overlapping `commit-pd` private copy-before-verify frame.
    let bad_priv_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: COMMIT_PRIVATE_PADDR,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let bad_priv_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &bad_priv_reg,
    }];
    let mut pol = canonical_policy();
    pol.streams = &bad_priv_streams;
    assert_eq!(
        verify_iommu_policy(&pol),
        Err(IommuRefusal::OverlappingProtectedFrame {
            stream_id: 0x10,
            class: ProtectedFrameClass::CommitPrivate,
            paddr: COMMIT_PRIVATE_PADDR,
        })
    );

    // 2. Overlapping PD code/stack/CSpace frame.
    let bad_code_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: 0x6011_2000,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let bad_code_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &bad_code_reg,
    }];
    pol.streams = &bad_code_streams;
    assert_eq!(
        verify_iommu_policy(&pol),
        Err(IommuRefusal::OverlappingProtectedFrame {
            stream_id: 0x10,
            class: ProtectedFrameClass::PdCodeStackCspace,
            paddr: 0x6011_2000,
        })
    );

    // 3. Overlapping hardware TRNG MMIO registers.
    let bad_trng_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: 0x0900_0000,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let bad_trng_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &bad_trng_reg,
    }];
    pol.streams = &bad_trng_streams;
    assert_eq!(
        verify_iommu_policy(&pol),
        Err(IommuRefusal::OverlappingProtectedFrame {
            stream_id: 0x10,
            class: ProtectedFrameClass::TrngMmio,
            paddr: 0x0900_0000,
        })
    );

    // 4. Overlapping root-server boot physical span.
    let bad_root_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: 0x6040_0000,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let bad_root_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &bad_root_reg,
    }];
    pol.streams = &bad_root_streams;
    assert_eq!(
        verify_iommu_policy(&pol),
        Err(IommuRefusal::OverlappingRootServerSpan {
            stream_id: 0x10,
            paddr: 0x6040_0000,
        })
    );

    // 5. Coupled `verify_chokepoint_with_iommu` catches an unlisted CSpace `PrivateFrame` sitting inside DMA pool!
    let mut cs_sneaky = cs;
    let sneaky_pfn = DMA_POOL_BASE / PAGE_SIZE_4K;
    let _ = cs_sneaky
        .pd_table_mut(ChokepointRole::Commit)
        .install_root(
            7,
            299,
            KernelObject::PrivateFrame { pfn: sneaky_pfn },
            CapRights::RW,
            0,
        )
        .unwrap();
    assert_eq!(
        verify_chokepoint_with_iommu(&desc, &cs_sneaky, &canonical_policy()),
        Err(IommuRefusal::OverlappingProtectedFrame {
            stream_id: 0x10,
            class: ProtectedFrameClass::CommitPrivate,
            paddr: DMA_POOL_BASE,
        })
    );
}

#[test]
fn refuses_stream_id_alignment_wrap_role_escalation_cross_alias_and_budget_violations() {
    let base = canonical_policy();

    // 1. Default-deny disabled.
    let mut no_deny = base;
    no_deny.default_deny_unmapped = false;
    assert_eq!(
        verify_iommu_policy(&no_deny),
        Err(IommuRefusal::DefaultDenyDisabled)
    );

    // 2. Unassigned (`0`) and Wildcard (`u32::MAX`) StreamIds.
    for bad_sid in [StreamId::UNASSIGNED, StreamId::WILDCARD] {
        let streams = [DeviceStreamBinding {
            stream_id: bad_sid,
            role: DeviceRole::IngressNic,
            owner_pd: ChokepointRole::Ingress,
            regions: &INGRESS_REGIONS,
        }];
        let mut pol = base;
        pol.streams = &streams;
        assert_eq!(
            verify_iommu_policy(&pol),
            Err(IommuRefusal::UnassignedOrWildcardStreamId {
                stream_id: bad_sid.0
            })
        );
    }

    // 3. Duplicate StreamId.
    let dup_streams = [
        DeviceStreamBinding {
            stream_id: StreamId(0x10),
            role: DeviceRole::IngressNic,
            owner_pd: ChokepointRole::Ingress,
            regions: &INGRESS_REGIONS,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x10),
            role: DeviceRole::PersistNvme,
            owner_pd: ChokepointRole::Persist,
            regions: &PERSIST_REGIONS,
        },
    ];
    let mut dup_pol = base;
    dup_pol.streams = &dup_streams;
    assert_eq!(
        verify_iommu_policy(&dup_pol),
        Err(IommuRefusal::DuplicateStreamId { stream_id: 0x10 })
    );

    // 4. Unaligned 4KiB and 2MiB pages.
    let unaligned_4k = [DmaRegion {
        iova: 0x1000_0000,
        paddr: DMA_POOL_BASE + 0x100,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let streams_4k = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &unaligned_4k,
    }];
    let mut pol_4k = base;
    pol_4k.streams = &streams_4k;
    assert_eq!(
        verify_iommu_policy(&pol_4k),
        Err(IommuRefusal::UnalignedDmaRegion {
            stream_id: 0x10,
            addr: DMA_POOL_BASE + 0x100,
            size: PAGE_SIZE_4K,
            required_align: PAGE_SIZE_4K,
        })
    );

    let unaligned_2m = [DmaRegion {
        iova: 0x2000_0000,
        paddr: DMA_POOL_BASE, // 4KiB aligned, NOT 2MiB aligned!
        size: PAGE_SIZE_2M,
        granule: PageGranule::Huge2MiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::PersistWalPool,
    }];
    let streams_2m = [DeviceStreamBinding {
        stream_id: StreamId(0x20),
        role: DeviceRole::PersistNvme,
        owner_pd: ChokepointRole::Persist,
        regions: &unaligned_2m,
    }];
    let mut pol_2m = base;
    pol_2m.streams = &streams_2m;
    assert_eq!(
        verify_iommu_policy(&pol_2m),
        Err(IommuRefusal::UnalignedDmaRegion {
            stream_id: 0x20,
            addr: DMA_POOL_BASE,
            size: PAGE_SIZE_2M,
            required_align: PAGE_SIZE_2M,
        })
    );

    // 5. Wrapping `[paddr, paddr + size)` range.
    let wrap_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: u64::MAX - PAGE_SIZE_4K + 1,
        size: 2 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let wrap_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &wrap_reg,
    }];
    let mut wrap_pol = base;
    wrap_pol.streams = &wrap_streams;
    assert_eq!(
        verify_iommu_policy(&wrap_pol),
        Err(IommuRefusal::WrappingAddressRange {
            stream_id: 0x10,
            addr: u64::MAX - PAGE_SIZE_4K + 1,
            size: 2 * PAGE_SIZE_4K,
        })
    );

    // 6. `IngressNic` granted write access to `tx-egress-pd` ring!
    let ingress_to_egress = [DmaRegion {
        iova: 0x1000_0000,
        paddr: DMA_POOL_BASE + 0x3_0000,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::WriteOnly,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let bad_ingress_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &ingress_to_egress,
    }];
    let mut pol_esc1 = base;
    pol_esc1.streams = &bad_ingress_streams;
    assert_eq!(
        verify_iommu_policy(&pol_esc1),
        Err(IommuRefusal::ForbiddenDmaRegionKind {
            stream_id: 0x10,
            role: DeviceRole::IngressNic,
            kind: DmaRegionKind::EgressOutboxRing,
            perm: IoPerm::WriteOnly,
        })
    );

    // 7. `EgressNic` granted write access to finalized outbox payloads!
    let egress_writable = [DmaRegion {
        iova: 0x3000_0000,
        paddr: DMA_POOL_BASE + 0x3_0000,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let bad_egress_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x30),
        role: DeviceRole::EgressNic,
        owner_pd: ChokepointRole::TxEgress,
        regions: &egress_writable,
    }];
    let mut pol_esc2 = base;
    pol_esc2.streams = &bad_egress_streams;
    assert_eq!(
        verify_iommu_policy(&pol_esc2),
        Err(IommuRefusal::ForbiddenDmaRegionKind {
            stream_id: 0x30,
            role: DeviceRole::EgressNic,
            kind: DmaRegionKind::EgressOutboxRing,
            perm: IoPerm::ReadWrite,
        })
    );

    // 8. Cross-stream writable physical aliasing (IngressNic & EgressNic sharing same paddr -> bypass!).
    let alias_egress = [DmaRegion {
        iova: 0x3000_0000,
        paddr: DMA_POOL_BASE, // overlaps INGRESS_REGIONS writable paddr!
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadOnly,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let alias_streams = [
        CANONICAL_STREAMS[0],
        DeviceStreamBinding {
            stream_id: StreamId(0x30),
            role: DeviceRole::EgressNic,
            owner_pd: ChokepointRole::TxEgress,
            regions: &alias_egress,
        },
    ];
    let mut alias_pol = base;
    alias_pol.streams = &alias_streams;
    assert_eq!(
        verify_iommu_policy(&alias_pol),
        Err(IommuRefusal::CrossStreamWritableAlias {
            stream_a: 0x10,
            stream_b: 0x30,
            paddr: DMA_POOL_BASE,
        })
    );

    // 9. `Commit` PD attempting to own ANY peripheral DMA stream is rejected!
    let commit_stream = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Commit,
        regions: &INGRESS_REGIONS,
    }];
    let mut commit_pol = base;
    commit_pol.streams = &commit_stream;
    assert_eq!(
        verify_iommu_policy(&commit_pol),
        Err(IommuRefusal::StreamOwnerRoleMismatch {
            stream_id: 0x10,
            device_role: DeviceRole::IngressNic,
            owner_pd: ChokepointRole::Commit,
        })
    );

    // 10. Root-server + DMA pool hitting or exceeding `10 MiB` (`10 * 1024 * 1024`) rejected!
    let mut over_budget = base;
    over_budget.dma_pool_size = MAX_ROOTSERVER_SPAN_BYTES - (base.rootserver_phys_end - base.rootserver_phys_start);
    // Round up to 4KiB boundary so total >= 10 MiB.
    over_budget.dma_pool_size = (over_budget.dma_pool_size + PAGE_SIZE_4K - 1) & !(PAGE_SIZE_4K - 1);
    assert!(matches!(
        verify_iommu_policy(&over_budget),
        Err(IommuRefusal::PhysicalBudgetExceeded { .. })
    ));
}

#[test]
fn deterministic_dma_fuzzing_proves_commit_private_frame_unreachable_and_egress_readonly() {
    let policy = canonical_policy();
    let private_frame = [0xA5u8; 4096];
    let mut pool_backing = [0x11u8; 64 * 1024];

    // Targeted direct checks on `translate_dma`:
    // - Unknown stream faults (`FaultOnUnmappedStream`).
    assert_eq!(
        policy.translate_dma(StreamId(0x99), 0x1000_0000, 64, DmaAccess::Read),
        Err(DmaFault::UnmappedStream { stream_id: 0x99 })
    );
    // - EgressNic read on finalized outbox succeeds; write is denied!
    assert_eq!(
        policy.translate_dma(StreamId(0x30), 0x3000_0000, 64, DmaAccess::Read),
        Ok(DmaTranslation {
            paddr: DMA_POOL_BASE + 0x3_0000,
            len: 64,
            kind: DmaRegionKind::EgressOutboxRing,
            perm: IoPerm::ReadOnly,
        })
    );
    assert_eq!(
        policy.translate_dma(StreamId(0x30), 0x3000_0000, 64, DmaAccess::Write),
        Err(DmaFault::PermissionDenied {
            stream_id: 0x30,
            iova: 0x3000_0000,
            perm: IoPerm::ReadOnly,
            access: DmaAccess::Write,
        })
    );
    // - CameraCsi2 write succeeds; read is denied (`WriteOnly`).
    assert_eq!(
        policy.translate_dma(StreamId(0x50), 0x5000_0000, 64, DmaAccess::Read),
        Err(DmaFault::PermissionDenied {
            stream_id: 0x50,
            iova: 0x5000_0000,
            perm: IoPerm::WriteOnly,
            access: DmaAccess::Read,
        })
    );
    // - Partial cross-region boundary escape fails atomically.
    assert_eq!(
        policy.translate_dma(
            StreamId(0x10),
            0x1000_0000 + 16 * PAGE_SIZE_4K - 16,
            32,
            DmaAccess::Write
        ),
        Err(DmaFault::CrossRegionSpanDenied {
            stream_id: 0x10,
            iova: 0x1000_0000 + 16 * PAGE_SIZE_4K - 16,
            len: 32,
        })
    );

    // Deterministic pseudo-random fuzzing: 2,000 adversarial peripheral DMA bursts across
    // valid + rogue StreamIds, random IOVAs, targeted CommitPrivate / TRNG / rootserver addresses!
    let mut ops = [DmaBurstOp {
        stream_id: StreamId(0),
        iova: 0,
        len: 1,
        access: DmaAccess::Read,
        payload_byte: 0,
    }; 2000];
    let mut rng = 0x9e37_79b9_7f4a_7c15u64;
    let candidate_sids = [0u32, 0x10, 0x20, 0x30, 0x40, 0x50, 0x77, u32::MAX];
    let candidate_bases = [
        0x1000_0000u64,
        0x2000_0000,
        0x3000_0000,
        0x4000_0000,
        0x5000_0000,
        COMMIT_PRIVATE_PADDR,
        0x6024_6000,
        0x0900_0000,
    ];
    for op in &mut ops {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        let sid = candidate_sids[(rng as usize) % candidate_sids.len()];
        let base = candidate_bases[((rng >> 8) as usize) % candidate_bases.len()];
        let off = (rng >> 16) & 0x1_ffff;
        let len = ((rng >> 33) & 0xff) + 1;
        let access = if (rng >> 41) & 1 == 0 {
            DmaAccess::Read
        } else {
            DmaAccess::Write
        };
        *op = DmaBurstOp {
            stream_id: StreamId(sid),
            iova: base.wrapping_add(off),
            len,
            access,
            payload_byte: (rng >> 48) as u8,
        };
    }

    let report = simulate_dma_burst(
        &policy,
        COMMIT_PRIVATE_PADDR,
        &private_frame,
        DMA_POOL_BASE,
        &mut pool_backing,
        &ops,
    )
    .expect("verified policy simulation succeeds");

    assert_eq!(report.total_ops, 2000);
    assert!(report.faulted_ops > 1000);
    assert!(report.allowed_reads > 0);
    assert!(report.allowed_writes > 0);
    assert_eq!(
        report.private_frame_touches, 0,
        "commit-pd private frame must be 100% unreachable by peripheral DMA"
    );
    assert_eq!(
        report.egress_outbox_writes, 0,
        "finalized tx-egress outbox must never be writable by peripheral DMA"
    );
    // Verify normal IngressNic DMA writes actually landed in `pool_backing`.
    assert_ne!(pool_backing, [0x11u8; 64 * 1024]);
}

#[test]
fn emits_canonical_no_std_microkit_system_xml_and_dtb_iommus_bindings() {
    let policy = canonical_policy();
    let desc = canonical_system_desc();

    // Fixed stack buffers (zero heap allocation).
    let mut xml_buf = [0u8; 4096];
    let xml_len = emit_microkit_system_xml(&policy, &desc, &mut xml_buf).expect("XML emit");
    let xml = core::str::from_utf8(&xml_buf[..xml_len]).expect("valid UTF-8 XML");
    assert!(xml.contains("OBEND.SHE.SMMU_MANIFEST/v1"));
    assert!(xml.contains("arch=arm,smmu-v3"));
    assert!(xml.contains("<protection_domain name=\"ingress-pd\""));
    assert!(xml.contains("<protection_domain name=\"commit-pd\""));
    assert!(xml.contains("<protection_domain name=\"persist-pd\""));
    assert!(xml.contains("<protection_domain name=\"tx-egress-pd\""));
    assert!(xml.contains("<memory_region name=\"dma_s16_r0\""));
    assert!(xml.contains("perms=\"r\""));
    // Commit PD section must NEVER map any peripheral `dma_s*` region!
    let commit_start = xml.find("<protection_domain name=\"commit-pd\"").unwrap();
    let commit_end = commit_start + xml[commit_start..].find("</protection_domain>").unwrap();
    assert!(
        !xml[commit_start..commit_end].contains("dma_s"),
        "commit-pd must never map any peripheral DMA region"
    );

    let mut dts_buf = [0u8; 4096];
    let dts_len = emit_dtb_iommus_binding(&policy, &mut dts_buf).expect("DTS emit");
    let dts = core::str::from_utf8(&dts_buf[..dts_len]).expect("valid UTF-8 DTS");
    assert!(dts.contains("compatible = \"arm,smmu-v3\";"));
    assert!(dts.contains("#iommu-cells = <1>;"));
    assert!(dts.contains("iommus = <&iommu0 0x10>;"));
    assert!(dts.contains("iommus = <&iommu0 0x30>;"));
    assert!(dts.contains("commit-private-0"));
    assert!(dts.contains("no-map;"));

    // Small buffer fails cleanly with `EmitError::BufferTooSmall`.
    let mut tiny = [0u8; 32];
    assert_eq!(
        emit_microkit_system_xml(&policy, &desc, &mut tiny),
        Err(EmitError::BufferTooSmall)
    );
    assert_eq!(
        emit_dtb_iommus_binding(&policy, &mut tiny),
        Err(EmitError::BufferTooSmall)
    );

    // Invalid policy fails closed before emitting a single byte!
    let mut bad_pol = policy;
    bad_pol.default_deny_unmapped = false;
    assert_eq!(
        emit_microkit_system_xml(&bad_pol, &desc, &mut xml_buf),
        Err(EmitError::InvalidPolicy(IommuRefusal::DefaultDenyDisabled))
    );
    assert_eq!(
        emit_dtb_iommus_binding(&bad_pol, &mut dts_buf),
        Err(EmitError::InvalidPolicy(IommuRefusal::DefaultDenyDisabled))
    );
}

#[test]
fn smmu_manifest_digest_binds_every_field_and_matches_golden_vector() {
    let base = canonical_policy();
    let d0 = smmu_manifest_digest(&base);

    // Mutate every single top-level & nested field and verify digest sensitivity!
    let mut m_arch = base;
    m_arch.arch = IommuArch::RiscvIommu;
    assert_ne!(d0, smmu_manifest_digest(&m_arch));

    let mut m_deny = base;
    m_deny.default_deny_unmapped = false;
    assert_ne!(d0, smmu_manifest_digest(&m_deny));

    let mut m_rstart = base;
    m_rstart.rootserver_phys_start += PAGE_SIZE_4K;
    assert_ne!(d0, smmu_manifest_digest(&m_rstart));

    let mut m_rend = base;
    m_rend.rootserver_phys_end -= PAGE_SIZE_4K;
    assert_ne!(d0, smmu_manifest_digest(&m_rend));

    let mut m_pbase = base;
    m_pbase.dma_pool_base += PAGE_SIZE_4K;
    assert_ne!(d0, smmu_manifest_digest(&m_pbase));

    let mut m_psize = base;
    m_psize.dma_pool_size -= PAGE_SIZE_4K;
    assert_ne!(d0, smmu_manifest_digest(&m_psize));

    let mut alt_prot = PROTECTED_RANGES;
    alt_prot[0].size += PAGE_SIZE_4K;
    let mut m_prot = base;
    m_prot.protected_ranges = &alt_prot;
    assert_ne!(d0, smmu_manifest_digest(&m_prot));

    let mut alt_reg = EGRESS_REGIONS;
    alt_reg[0].perm = IoPerm::ReadWrite;
    let mut alt_streams = CANONICAL_STREAMS;
    alt_streams[2].regions = &alt_reg;
    let mut m_stream = base;
    m_stream.streams = &alt_streams;
    assert_ne!(d0, smmu_manifest_digest(&m_stream));

    // Locked Golden Test Vector #1 shared verbatim with `Obend.OS.SmmuDmaConfinement` (`@she-smmu-lean` #204):
    let lean_golden_prot = [
        ProtectedFrameRange {
            class: ProtectedFrameClass::CommitPrivate,
            base_paddr: 0x6030_0000,
            size: 0x1000,
        },
        ProtectedFrameRange {
            class: ProtectedFrameClass::PdCodeStackCspace,
            base_paddr: 0x6024_6000,
            size: 0x000b_a000,
        },
    ];
    let lean_golden_ingress = [DmaRegion {
        iova: 0x8000_0000,
        paddr: 0x6084_6000,
        size: 0x1000,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::WriteOnly,
        kind: DmaRegionKind::IngressRing,
    }];
    let lean_golden_persist = [DmaRegion {
        iova: 0x8001_0000,
        paddr: 0x6084_7000,
        size: 0x2000,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::PersistWalPool,
    }];
    let lean_golden_egress = [DmaRegion {
        iova: 0x8002_0000,
        paddr: 0x6084_9000,
        size: 0x1000,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadOnly,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let lean_golden_streams = [
        DeviceStreamBinding {
            stream_id: StreamId(0x0000_0010),
            role: DeviceRole::IngressNic,
            owner_pd: ChokepointRole::Ingress,
            regions: &lean_golden_ingress,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x0000_0020),
            role: DeviceRole::PersistNvme,
            owner_pd: ChokepointRole::Persist,
            regions: &lean_golden_persist,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x0000_0030),
            role: DeviceRole::EgressNic,
            owner_pd: ChokepointRole::TxEgress,
            regions: &lean_golden_egress,
        },
    ];
    let lean_golden_policy = ChokepointIommuPolicy {
        arch: IommuArch::ArmSmmuV3,
        default_deny_unmapped: true,
        rootserver_phys_start: 0x6024_6000,
        rootserver_phys_end: 0x6084_6000,
        dma_pool_base: 0x6084_6000,
        dma_pool_size: 0x0010_0000,
        protected_ranges: &lean_golden_prot,
        streams: &lean_golden_streams,
    };
    let lean_golden_expected: Digest = [
        0xbc, 0x53, 0x8f, 0x6d, 0x7a, 0x5e, 0xf1, 0x80, 0x33, 0x2e, 0xf0, 0xcd, 0x6c, 0xc8, 0xa1,
        0x73, 0x95, 0x55, 0x10, 0x9d, 0x68, 0x9d, 0x37, 0xa7, 0xc8, 0x88, 0x6b, 0x10, 0x80, 0xd7,
        0x23, 0x0e,
    ];
    assert_eq!(
        verify_iommu_policy(&lean_golden_policy),
        Ok(lean_golden_expected),
        "Rust OBEND.SHE.SMMU_MANIFEST/v1 digest must match Lean Golden Vector #1 byte-for-byte"
    );

    // Golden Vector #2 (5-stream canonical policy with CameraCsi2 + DisplayScanout + TrngMmio):
    let canonical_digest = verify_iommu_policy(&base).expect("canonical 5-stream policy verifies");
    assert_ne!(canonical_digest, lean_golden_expected);
}

#[test]
fn refuses_loader_collision_outside_pool_overlap_iova_missing_protection_and_gpu_escalation() {
    let base = canonical_policy();

    // 1. DMA pool colliding with stock Microkit 2.2.0 loader base `0x7000_0000`.
    let mut loader_hit = base;
    loader_hit.dma_pool_base = STOCK_MICROKIT_LOADER_BASE - PAGE_SIZE_4K;
    loader_hit.dma_pool_size = 2 * PAGE_SIZE_4K;
    assert_eq!(
        verify_iommu_policy(&loader_hit),
        Err(IommuRefusal::LoaderCollision {
            phys_end: STOCK_MICROKIT_LOADER_BASE + PAGE_SIZE_4K,
            loader_base: STOCK_MICROKIT_LOADER_BASE,
        })
    );

    // 2. DMA region outside budgeted DMA pool.
    let outside_reg = [DmaRegion {
        iova: 0x1000_0000,
        paddr: DMA_POOL_BASE + DMA_POOL_SIZE,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let outside_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &outside_reg,
    }];
    let mut pol_out = base;
    pol_out.streams = &outside_streams;
    assert_eq!(
        verify_iommu_policy(&pol_out),
        Err(IommuRefusal::DmaRegionOutsidePool {
            stream_id: 0x10,
            paddr: DMA_POOL_BASE + DMA_POOL_SIZE,
            size: PAGE_SIZE_4K,
        })
    );

    // 3. Intra-stream overlapping IOVA mapping.
    let dup_iova_regs = [
        DmaRegion {
            iova: 0x1000_0000,
            paddr: DMA_POOL_BASE,
            size: 2 * PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
        DmaRegion {
            iova: 0x1000_1000,
            paddr: DMA_POOL_BASE + 2 * PAGE_SIZE_4K,
            size: PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
    ];
    let dup_iova_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &dup_iova_regs,
    }];
    let mut pol_iova = base;
    pol_iova.streams = &dup_iova_streams;
    assert_eq!(
        verify_iommu_policy(&pol_iova),
        Err(IommuRefusal::OverlappingStreamIova {
            stream_id: 0x10,
            iova_a: 0x1000_0000,
            iova_b: 0x1000_1000,
        })
    );

    // 4. Missing required protected ranges (`CommitPrivate` or `PdCodeStackCspace`) & empty stream table.
    let only_code = [PROTECTED_RANGES[1]];
    let mut no_priv_prot = base;
    no_priv_prot.protected_ranges = &only_code;
    assert_eq!(
        verify_iommu_policy(&no_priv_prot),
        Err(IommuRefusal::MissingRequiredProtection {
            class: ProtectedFrameClass::CommitPrivate,
        })
    );

    let mut empty_streams = base;
    empty_streams.streams = &[];
    assert_eq!(
        verify_iommu_policy(&empty_streams),
        Err(IommuRefusal::EmptyStreamTable)
    );

    // 5. GPU allowed on `GpuScratchPool` (`ReadWrite`), refused on `EgressOutboxRing` (`ReadWrite`).
    let gpu_ok_reg = [DmaRegion {
        iova: 0x6000_0000,
        paddr: DMA_POOL_BASE + 0x6_0000,
        size: 4 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::GpuScratchPool,
    }];
    let gpu_ok_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x60),
        role: DeviceRole::Gpu,
        owner_pd: ChokepointRole::TxEgress,
        regions: &gpu_ok_reg,
    }];
    let mut pol_gpu_ok = base;
    pol_gpu_ok.streams = &gpu_ok_streams;
    assert!(verify_iommu_policy(&pol_gpu_ok).is_ok());

    let gpu_bad_reg = [DmaRegion {
        iova: 0x6000_0000,
        paddr: DMA_POOL_BASE + 0x6_0000,
        size: 4 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let gpu_bad_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x60),
        role: DeviceRole::Gpu,
        owner_pd: ChokepointRole::TxEgress,
        regions: &gpu_bad_reg,
    }];
    let mut pol_gpu_bad = base;
    pol_gpu_bad.streams = &gpu_bad_streams;
    assert_eq!(
        verify_iommu_policy(&pol_gpu_bad),
        Err(IommuRefusal::ForbiddenDmaRegionKind {
            stream_id: 0x60,
            role: DeviceRole::Gpu,
            kind: DmaRegionKind::EgressOutboxRing,
            perm: IoPerm::ReadWrite,
        })
    );

    // 6. RISC-V IOMMU DTS & XML emission check.
    let mut rv_pol = base;
    rv_pol.arch = IommuArch::RiscvIommu;
    let desc = canonical_system_desc();
    let mut buf = [0u8; 4096];
    let n_dts = emit_dtb_iommus_binding(&rv_pol, &mut buf).expect("RISC-V DTS emit");
    let dts = core::str::from_utf8(&buf[..n_dts]).unwrap();
    assert!(dts.contains("compatible = \"riscv,iommu\";"));
    let n_xml = emit_microkit_system_xml(&rv_pol, &desc, &mut buf).expect("RISC-V XML emit");
    let xml = core::str::from_utf8(&buf[..n_xml]).unwrap();
    assert!(xml.contains("arch=riscv,iommu"));

    // 7. Root-server span mismatch in coupled check & XML emitter.
    let mut mismatched_desc = desc;
    mismatched_desc.rootserver_phys_end -= PAGE_SIZE_4K;
    let cs = canonical_cspaces();
    assert_eq!(
        verify_chokepoint_with_iommu(&mismatched_desc, &cs, &base),
        Err(IommuRefusal::RootServerSpanMismatch)
    );
    assert_eq!(
        emit_microkit_system_xml(&base, &mismatched_desc, &mut buf),
        Err(EmitError::InvalidPolicy(IommuRefusal::RootServerSpanMismatch))
    );

    // 8. `translate_dma` zero-length and wrapping transfer checks.
    assert_eq!(
        base.translate_dma(StreamId(0x10), 0x1000_0000, 0, DmaAccess::Read),
        Err(DmaFault::ZeroLengthTransfer)
    );
    assert_eq!(
        base.translate_dma(StreamId(0x10), u64::MAX - 8, 16, DmaAccess::Read),
        Err(DmaFault::AddressWrap)
    );
    assert_eq!(
        base.translate_dma(StreamId(0x10), 0x9999_0000, 64, DmaAccess::Read),
        Err(DmaFault::UnmappedIova {
            stream_id: 0x10,
            iova: 0x9999_0000,
        })
    );

    // 9. Cross-audit regressions (#210):
    //    (a) `translate_dma` fails closed with `DefaultDenyDisabled` when `default_deny_unmapped == false`.
    let mut no_deny = base;
    no_deny.default_deny_unmapped = false;
    assert_eq!(
        no_deny.translate_dma(StreamId(0x10), 0x1000_0000, 64, DmaAccess::Read),
        Err(DmaFault::DefaultDenyDisabled)
    );

    //    (b) `dma_pool` overlapping `rootserver` or `protected_ranges` is refused even if mapped regions sit in the non-overlapping tail!
    let mut pool_hits_root = base;
    pool_hits_root.dma_pool_base = base.rootserver_phys_end - PAGE_SIZE_4K;
    pool_hits_root.dma_pool_size = DMA_POOL_SIZE + PAGE_SIZE_4K;
    assert_eq!(
        verify_iommu_policy(&pool_hits_root),
        Err(IommuRefusal::DmaPoolOverlapsRootServer)
    );

    let prot_in_pool_tail = [
        ProtectedFrameRange {
            class: ProtectedFrameClass::CommitPrivate,
            base_paddr: DMA_POOL_BASE + DMA_POOL_SIZE - PAGE_SIZE_4K,
            size: PAGE_SIZE_4K,
        },
        PROTECTED_RANGES[1],
    ];
    let mut pool_hits_prot = base;
    pool_hits_prot.protected_ranges = &prot_in_pool_tail;
    assert_eq!(
        verify_iommu_policy(&pool_hits_prot),
        Err(IommuRefusal::DmaPoolOverlapsProtectedFrame {
            class: ProtectedFrameClass::CommitPrivate,
        })
    );

    //    (c) `emit_microkit_system_xml` refuses DMA IOVAs colliding with fixed IPC VAddrs `0x4000000..0x4003000`.
    let colliding_iova_reg = [DmaRegion {
        iova: MICROKIT_RESERVED_IPC_VADDR_BASE,
        paddr: DMA_POOL_BASE,
        size: PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let colliding_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &colliding_iova_reg,
    }];
    let mut colliding_pol = base;
    colliding_pol.streams = &colliding_streams;
    assert!(verify_iommu_policy(&colliding_pol).is_ok());
    assert_eq!(
        emit_microkit_system_xml(&colliding_pol, &desc, &mut buf),
        Err(EmitError::ReservedIpcVaddrCollision {
            stream_id: 0x10,
            iova: MICROKIT_RESERVED_IPC_VADDR_BASE,
        })
    );
}

#[test]
fn coupled_copy_before_verify_and_adversarial_dma_burst_preserves_settled_actuation() {
    let alg = OutboxHashAlg::Cshake256;
    let desc = canonical_system_desc();
    let mut cs = canonical_cspaces();
    let policy = canonical_policy();
    assert!(verify_chokepoint_with_iommu(&desc, &cs, &policy).is_ok());

    let commit_ingress_ro = CapHandle { slot: 0, epoch: 1 };
    let commit_leaf_rw = CapHandle { slot: 2, epoch: 3 };
    let commit_ppc = CapHandle { slot: 3, epoch: 4 };
    let commit_egress_rw = CapHandle { slot: 4, epoch: 5 };
    let commit_egress_ntfn = CapHandle { slot: 5, epoch: 6 };

    let genesis_state = [0x10u8; 32];
    let post_state = [0x20u8; 32];
    let genesis_wal = [0x70u8; 32];
    let payload_bytes = b"smmu-confined-actuation-001";
    let mut payload = [0u8; 64];
    payload[..payload_bytes.len()].copy_from_slice(payload_bytes);

    let eff_commit = effect_commit_digest(
        alg,
        1,
        OutboxEffectClass::IrreversibleActuation,
        payload_bytes,
    );
    let sib = effect_commit_digest(alg, 999, OutboxEffectClass::IdempotentRead, b"sib");
    let tree = EffectsMerkleTree::from_commits([eff_commit, sib]).unwrap();
    let effects_root = tree.root(alg);
    let siblings: [Digest; 1] = tree.open(alg, 0).unwrap();
    let tip_payload = block_effects_payload(alg, &post_state, &effects_root);
    let chain = [
        SimplexChainEntry::EmptyView { view: 1 },
        SimplexChainEntry::Block {
            view: 2,
            payload: tip_payload,
        },
    ];

    let mut slot_pubkeys = [[[0u8; 32]; 4]; 1];
    let mut votes = [ValidatorFinalizeVote::ZERO; 4];
    for i in 0..4 {
        let mut salt = [0x55u8; 32];
        salt[0] = (i as u8) + 1;
        slot_pubkeys[0][i] = derive_finalize_slot_pubkey(alg, i as u64, 2, &chain, &salt).unwrap();
        if i < 3 {
            votes[i] = ValidatorFinalizeVote {
                signer_id: i as u64,
                sig_salt: salt,
            };
        }
    }
    let committee = SimplexCommittee {
        n: 4,
        f: 1,
        base_view: 2,
        active_views: 1,
        hash_alg: alg,
        slot_pubkeys,
    };
    let verifier = OutboxFinalityVerifier {
        circuit_digest: [0x51; 32],
        authorized_cap_root: [0x61; 32],
        gatekeeper_pd: 2,
        high_water_nullifier: 0,
        committee,
    };
    let pi = FullPinnedPublicInputs {
        circuit_desc_digest: verifier.circuit_digest,
        actor_vk_digest: committee.directory_digest(),
        pre_state_root: genesis_state,
        post_state_root: post_state,
        cap_root: verifier.authorized_cap_root,
        revoked_root: outbox_window_digest(alg, verifier.gatekeeper_pd, 0),
        height: 1,
        turn_hash: outbox_turn_digest(alg, &eff_commit, &effects_root, 0),
    };
    let mut shared_bundle = SovereignTurnBundle {
        public_inputs: pi,
        challenge0: pi.transcript().squeeze(),
        effect_vk_digest: pi.actor_vk_digest,
        last_row_gate_ok: true,
        receipt: OutboxTurnReceipt::<2, 4, 1, 64> {
            nullifier_id: 1,
            leaf_index: 0,
            effects_root,
            merkle_siblings: siblings,
            payload_len: payload_bytes.len(),
            payload,
            fin_cert: SimplexFinCert {
                view: 2,
                chain_len: 2,
                chain,
                vote_count: 3,
                votes,
            },
        },
    };

    let mut commit = CommitPdMonitor::new(verifier, genesis_state, genesis_wal, 4);
    let mut persist = PersistPdState::<4096>::new(alg, genesis_wal);
    let mut egress = TxEgressPdState::new(alg, genesis_wal);
    let private_frame = [0xC3u8; 4096];
    let mut dma_ram = [0u8; 4096];

    let ok = commit.offer_bundle_with_persist(
        &mut cs,
        commit_ingress_ro,
        commit_leaf_rw,
        commit_ppc,
        commit_egress_rw,
        commit_egress_ntfn,
        &mut shared_bundle,
        |racing_slot| {
            // Concurrent peripheral DMA attack attempting to clobber shared ingress ring,
            // commit-pd private frame, and tx-egress outbox ring mid-verification!
            let attack_ops = [
                DmaBurstOp {
                    stream_id: StreamId(0x10),
                    iova: 0x1000_0000,
                    len: 64,
                    access: DmaAccess::Write,
                    payload_byte: 0xFF,
                },
                DmaBurstOp {
                    stream_id: StreamId(0x10),
                    iova: COMMIT_PRIVATE_PADDR,
                    len: 64,
                    access: DmaAccess::Write,
                    payload_byte: 0xEE,
                },
                DmaBurstOp {
                    stream_id: StreamId(0x30),
                    iova: 0x3000_0000,
                    len: 64,
                    access: DmaAccess::Write,
                    payload_byte: 0xDD,
                },
                DmaBurstOp {
                    stream_id: StreamId(0xFF),
                    iova: COMMIT_PRIVATE_PADDR,
                    len: 64,
                    access: DmaAccess::Read,
                    payload_byte: 0,
                },
            ];
            let rep = simulate_dma_burst(
                &policy,
                COMMIT_PRIVATE_PADDR,
                &private_frame,
                DMA_POOL_BASE,
                &mut dma_ram,
                &attack_ops,
            )
            .expect("verified SMMU filters adversarial burst");
            assert_eq!(rep.private_frame_touches, 0);
            assert_eq!(rep.egress_outbox_writes, 0);
            assert_eq!(rep.faulted_ops, 3);
            assert_eq!(rep.allowed_writes, 1);
            // Clobber the shared ring slot (simulating allowed IngressNic RX DMA write after copy).
            racing_slot.receipt.payload.fill(0xFF);
        },
        |n, leaf_ro| persist.handle_ppc_append(n, leaf_ro),
        &mut egress,
    );
    assert!(ok, "copy-before-verify + SMMU confinement must settle authentic payload");
    assert_eq!(commit.height(), 1);
    assert_eq!(commit.forwarded(), 1);
    assert_eq!(persist.entries(), 1);
    assert_eq!(egress.tx_packets_emitted(), 1);
    assert_eq!(egress.released_seq(), 1);
}

#[test]
fn smmuv3_ste_riscv_ddt_stage2_descriptors_and_cmdq_match_locked_bit_layouts() {
    // 1. Golden 512-bit Armv8 SMMUv3 STE (`vmid = 1`, `s2ttb = 0x6015_2000`):
    //    w0 = 0x0d (`V[0]=1, Config[3:1]=0b110`), w1 = 0 (`EATS[93:92]=0b00`),
    //    w2 = 0x040d_0090_0000_0001 (`S2VMID=1, S2T0SZ=16, S2SL0=2, S2TG=0, S2PS=5, S2AA64=1, S2S=0, S2R=1`),
    //    w3 = 0x6015_2000 (`S2TTB[243:196]`).
    let ste = SmmuV3Ste::pack_stage2(1, 0x6015_2000).expect("valid STE");
    assert_eq!(
        ste.words,
        [
            0x0000_0000_0000_000d,
            0x0000_0000_0000_0000,
            0x040d_0090_0000_0001,
            0x0000_0000_6015_2000,
            0,
            0,
            0,
            0,
        ]
    );
    assert_eq!(
        ste.decode(),
        Ok(DecodedSmmuV3Ste::Stage2Translate {
            vmid: 1,
            s2ttb_paddr: 0x6015_2000,
        })
    );
    assert_eq!(SmmuV3Ste::ABORT.decode(), Ok(DecodedSmmuV3Ste::Abort));
    let ste_bytes = ste.to_le_bytes();
    assert_eq!(SmmuV3Ste::from_le_bytes(&ste_bytes), ste);

    // 16-bit VMID using bits [11:10] (`0x0c01`, global bits [139:138]) round-trips cleanly without colliding with EATS[93:92]!
    let ste_hi_vmid = SmmuV3Ste::pack_stage2(0x0c01, 0x6015_3000).expect("16-bit VMID valid");
    assert_eq!(
        ste_hi_vmid.decode(),
        Ok(DecodedSmmuV3Ste::Stage2Translate {
            vmid: 0x0c01,
            s2ttb_paddr: 0x6015_3000,
        })
    );

    // Mutating EATS[93:92] (`w1` bit 28) is unconditionally refused (`PcieAtsBypassEnabled`).
    let mut bad_eats = ste;
    bad_eats.words[1] |= 1u64 << 28;
    assert_eq!(
        bad_eats.decode(),
        Err(SteDecodeError::PcieAtsBypassEnabled(1))
    );

    // Mutating `Config[3:1]` to `0b100` (Stage-1 & Stage-2 bypass!) is refused.
    let mut bad_bypass = ste;
    bad_bypass.words[0] = 1 | (0b100 << 1);
    assert_eq!(
        bad_bypass.decode(),
        Err(SteDecodeError::ForbiddenConfigMode(0b100))
    );

    // Mutating `S2S[185]` (`w2` bit 57) without stall handler is refused.
    let mut bad_stall = ste;
    bad_stall.words[2] |= 1u64 << 57;
    assert_eq!(bad_stall.decode(), Err(SteDecodeError::StallWithoutHandler));

    // 2. Golden 256-bit RISC-V IOMMU Base-Format DDT Entry (`gscid = 1`, `16 KiB`-aligned `root_paddr = 0x6015_4000`):
    let ddte = RiscvDdtEntry::pack_sv48x4(1, 0x6015_4000).expect("valid 16KiB-aligned RISC-V DDTE");
    assert_eq!(
        ddte.words,
        [0x0000_0000_0000_0001, 0x9000_1000_0006_0154, 0, 0]
    );
    assert_eq!(
        ddte.decode(),
        Ok(DecodedRiscvDdte::Sv48x4Translate {
            gscid: 1,
            root_paddr: 0x6015_4000,
        })
    );
    // 4 KiB-only aligned root (`0x6015_2000`, `PPN[1:0] = 0b10 != 0`) is rejected by `Sv48x4`!
    assert_eq!(
        RiscvDdtEntry::pack_sv48x4(1, 0x6015_2000),
        Err(DdteDecodeError::UnalignedOrOutOfRangeRoot(0x6015_2000))
    );
    assert_eq!(RiscvDdtEntry::ABORT.decode(), Ok(DecodedRiscvDdte::Abort));
    let mut bad_rv_ats = ddte;
    bad_rv_ats.words[0] |= 1 << 1; // EN_ATS=1
    assert_eq!(bad_rv_ats.decode(), Err(DdteDecodeError::PcieAtsOrPriEnabled));
    let mut bad_rv_bare = ddte;
    bad_rv_bare.words[1] &= !(0xfu64 << 60); // MODE=0 Bare bypass!
    assert_eq!(
        bad_rv_bare.decode(),
        Err(DdteDecodeError::BareBypassOrInvalidMode(0))
    );

    // 3. Golden 64-bit Armv8 Stage-2 Descriptors (Table, L2 2MiB Block, L3 4KiB Page):
    let tbl_desc = encode_stage2_table_desc(0x6015_3000).unwrap();
    assert_eq!(tbl_desc, 0x0000_0000_6015_3003);
    assert_eq!(decode_stage2_table_desc(tbl_desc), Some(0x6015_3000));
    assert_eq!(decode_stage2_table_desc(0x0000_0000_6020_0441), None); // Block invalid at L0/L1!

    let page_desc = encode_stage2_page4k_desc(0x6084_6000, IoPerm::WriteOnly).unwrap();
    assert_eq!(page_desc, 0x0040_0000_6084_6483);
    assert_eq!(
        decode_stage2_l3_desc(page_desc),
        Some(DecodedL3Desc::Page4KiB {
            oa_paddr: 0x6084_6000,
            perm: IoPerm::WriteOnly,
        })
    );
    // Clearing AF[10] or flipping S2XN[54:53] from `0b10` (XN-all) to `0b11` (EL1 executable under FEAT_XNX) faults!
    assert_eq!(decode_stage2_l3_desc(page_desc & !(1u64 << 10)), None);
    assert_eq!(decode_stage2_l3_desc(page_desc | (1u64 << 53)), None);
    assert_eq!(decode_stage2_l3_desc(0x0040_0000_6084_6481), None); // 0b01 invalid at L3!

    let blk_desc = encode_stage2_block2m_desc(0x6020_0000, IoPerm::ReadOnly).unwrap();
    assert_eq!(blk_desc, 0x0040_0000_6020_0441);
    assert_eq!(
        decode_stage2_l2_desc(blk_desc),
        Some(DecodedL2Desc::Block2MiB {
            oa_paddr: 0x6020_0000,
            perm: IoPerm::ReadOnly,
        })
    );
    // Non-zero low OA bits [20:12] in a 2 MiB block descriptor must be rejected!
    assert_eq!(decode_stage2_l2_desc(blk_desc | 0x1000), None);

    // 4. Golden 128-bit SMMUv3 Command Queue encodings:
    let cfgi = SmmuCmd::CfgiSte {
        stream_id: StreamId(0x10),
        leaf: false,
    };
    assert_eq!(cfgi.pack(), Some([0x0000_0010_0000_0003, 0]));
    assert_eq!(SmmuCmd::decode([0x0000_0010_0000_0003, 0]), Some(cfgi));

    let tlbi = SmmuCmd::TlbiS2Ipa {
        vmid: 1,
        ipa: 0x8000_0000,
        leaf: false,
    };
    assert_eq!(
        tlbi.pack(),
        Some([0x0000_0001_0000_002a, 0x0000_0000_8000_0000])
    );
    assert_eq!(
        SmmuCmd::decode([0x0000_0001_0000_002a, 0x0000_0000_8000_0000]),
        Some(tlbi)
    );
    // Non-zero RES0 bits [63:48] must be rejected on Stage-2 TLBI commands!
    assert_eq!(
        SmmuCmd::decode([0x0001_0001_0000_002a, 0x0000_0000_8000_0000]),
        None
    );
    let vmall = SmmuCmd::TlbiS12Vmall { vmid: 1 };
    assert_eq!(vmall.pack(), Some([0x0000_0001_0000_0028, 0]));
    assert_eq!(SmmuCmd::decode([0x0000_0001_0000_0028, 0]), Some(vmall));

    assert_eq!(SmmuCmd::Sync.pack(), Some([0x46, 0]));
    assert_eq!(SmmuCmd::decode([0x46, 0]), Some(SmmuCmd::Sync));
}

#[test]
fn differential_fuzzer_2000_ops_proves_walk_smmuv3_stage2_equals_translate_dma_and_protects_tables() {
    // 0. Coalescable IOVA-adjacent + PA-contiguous + same-permission regions cannot be distinguished
    //    by pure hardware Stage-2 PTEs (`RegionsNonCoalescable`), so `RadixTableArena::compile` refuses them!
    let coalescable_adj = [
        DmaRegion {
            iova: 0x1000_0000,
            paddr: 0x6080_0000,
            size: 16 * PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
        DmaRegion {
            iova: 0x1001_0000,
            paddr: 0x6081_0000,
            size: 2 * PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
    ];
    let coalescable_streams = [DeviceStreamBinding {
        stream_id: StreamId(0x10),
        role: DeviceRole::IngressNic,
        owner_pd: ChokepointRole::Ingress,
        regions: &coalescable_adj,
    }];
    let coalescable_policy = ChokepointIommuPolicy {
        arch: IommuArch::ArmSmmuV3,
        default_deny_unmapped: true,
        rootserver_phys_start: 0x6020_0000,
        rootserver_phys_end: 0x6060_0000,
        dma_pool_base: 0x6080_0000,
        dma_pool_size: 4 * PAGE_SIZE_2M / 2,
        protected_ranges: &PROTECTED_RANGES,
        streams: &coalescable_streams,
    };
    assert_eq!(
        RadixTableArena::<20>::compile(&coalescable_policy, 0x6015_0000),
        Err(RadixBuildError::CoalescableAdjacentRegions {
            stream_id: 0x10,
            first_iova: 0x1000_0000,
            second_iova: 0x1001_0000,
        })
    );

    // Include IOVA-adjacent non-contiguous-PA regions (`0x1001_0000 -> 0x6081_4000` right after `0x1000_0000..0x1001_0000`),
    // a 2 MiB L2 huge-page block (`0x2000_0000..0x2020_0000`), RO outbox, and WO camera!
    let ingress_two_adj = [
        DmaRegion {
            iova: 0x1000_0000,
            paddr: 0x6080_0000,
            size: 16 * PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
        DmaRegion {
            iova: 0x1001_0000,
            paddr: 0x6081_4000,
            size: 2 * PAGE_SIZE_4K,
            granule: PageGranule::Page4KiB,
            perm: IoPerm::ReadWrite,
            kind: DmaRegionKind::IngressRing,
        },
    ];
    let persist_huge = [DmaRegion {
        iova: 0x2000_0000,
        paddr: 0x60a0_0000,
        size: PAGE_SIZE_2M,
        granule: PageGranule::Huge2MiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::PersistWalPool,
    }];
    let egress_ro = [DmaRegion {
        iova: 0x3000_0000,
        paddr: 0x6082_0000,
        size: 4 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadOnly,
        kind: DmaRegionKind::EgressOutboxRing,
    }];
    let camera_wo = [DmaRegion {
        iova: 0x5000_0000,
        paddr: 0x6083_0000,
        size: 4 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::WriteOnly,
        kind: DmaRegionKind::CameraRing,
    }];
    let streams = [
        DeviceStreamBinding {
            stream_id: StreamId(0x10),
            role: DeviceRole::IngressNic,
            owner_pd: ChokepointRole::Ingress,
            regions: &ingress_two_adj,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x20),
            role: DeviceRole::PersistNvme,
            owner_pd: ChokepointRole::Persist,
            regions: &persist_huge,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x30),
            role: DeviceRole::EgressNic,
            owner_pd: ChokepointRole::TxEgress,
            regions: &egress_ro,
        },
        DeviceStreamBinding {
            stream_id: StreamId(0x50),
            role: DeviceRole::CameraCsi2,
            owner_pd: ChokepointRole::Ingress,
            regions: &camera_wo,
        },
    ];
    let policy = ChokepointIommuPolicy {
        arch: IommuArch::ArmSmmuV3,
        default_deny_unmapped: true,
        rootserver_phys_start: 0x6020_0000,
        rootserver_phys_end: 0x6060_0000,
        dma_pool_base: 0x6080_0000,
        dma_pool_size: 4 * PAGE_SIZE_2M / 2, // 4 MiB (`0x6080_0000..0x60c0_0000`), total 8 MiB < 10 MiB!
        protected_ranges: &PROTECTED_RANGES,
        streams: &streams,
    };

    // Attempting to place the radix arena outside `KernelPageTable` protected frames is refused,
    // AND leaves `arena` completely disarmed (`active_stream_limit == 0`, unwalkable)!
    let mut arena = RadixTableArena::<20>::empty();
    arena
        .compile_into(&policy, 0x6015_0000)
        .expect("initial compile succeeds");
    assert_eq!(
        arena.compile_into(&policy, 0x6010_0000),
        Err(RadixBuildError::ArenaNotInKernelPageTableRange {
            arena_base: 0x6010_0000,
            arena_bytes: 18 * PAGE_SIZE_4K,
        })
    );
    assert_eq!(arena.active_stream_limit(), 0);
    assert_eq!(
        walk_smmuv3_stage2(&arena, StreamId(0x10), 0x1000_0000, 64, DmaAccess::Write),
        Err(DmaFault::UnmappedStream { stream_id: 0x10 })
    );

    arena
        .compile_into(&policy, 0x6015_0000)
        .expect("compiles into KernelPageTable arena");
    assert!(
        arena.smmu_tables_dma_unreachable(&policy),
        "Stream Table + CmdQ + L0..L3 radix tables must sit in KernelPageTable and be 100% DMA-unreachable"
    );
    let mut rv_mismatch = policy;
    rv_mismatch.arch = IommuArch::RiscvIommu;
    assert_eq!(
        RadixTableArena::<20>::compile(&rv_mismatch, 0x6015_0000),
        Err(RadixBuildError::UnsupportedArchForSmmuV3Radix(
            IommuArch::RiscvIommu
        ))
    );
    // Misaligned `SMMU_STRTAB_BASE` (`0x6015_1000` is 4 KiB-aligned, NOT 8 KiB-aligned for 128 STEs!) is refused!
    assert_eq!(
        RadixTableArena::<20>::compile(&policy, 0x6015_1000),
        Err(RadixBuildError::UnalignedOrOutOfRangeArenaBase(0x6015_1000))
    );

    // Explicit edge-case corpus before 2,000-op PRNG sweep:
    let edge_cases: &[(u32, u64, u64, DmaAccess)] = &[
        // Multi-page contiguous transfer inside region 0 (`0x1000_0ff0..0x1000_2010`): succeeds!
        (0x10, 0x1000_0ff0, 0x1020, DmaAccess::Write),
        // Multi-page boundary escape off the end of mapped region (`0x1001_1fc0..0x1001_2040` into unmapped L3 PTE): faults!
        (0x10, 0x1001_1fc0, 128, DmaAccess::Write),
        // Two-byte transfer straddling two adjacent `ReadWrite` regions (`0x1000_ffff..0x1001_0001`): CrossRegionSpanDenied!
        (0x10, 0x1000_ffff, 2, DmaAccess::Write),
        // Interior offset inside 2 MiB L2 block (`0x201a_bcde`):
        (0x20, 0x201a_bcde, 512, DmaAccess::Read),
        // High IOVA >= 2^48 with mapped low bits (`(1 << 48) | 0x1000_0000`): UnmappedIova!
        (0x10, (1u64 << 48) | 0x1000_0000, 64, DmaAccess::Write),
        // Zero length and u64 wraparound:
        (0x10, 0x1000_0000, 0, DmaAccess::Read),
        (0x10, u64::MAX - 7, 16, DmaAccess::Write),
        // Unmapped / sentinel StreamIds:
        (0, 0x1000_0000, 64, DmaAccess::Read),
        (u32::MAX, 0x1000_0000, 64, DmaAccess::Write),
        (0x77, 0x1000_0000, 64, DmaAccess::Read),
        // Permission denials on RO and WO leaves:
        (0x30, 0x3000_0100, 64, DmaAccess::Write),
        (0x50, 0x5000_0200, 64, DmaAccess::Read),
    ];
    for &(sid, iova, len, access) in edge_cases {
        assert_eq!(
            walk_smmuv3_stage2(&arena, StreamId(sid), iova, len, access),
            translate_dma(&policy, StreamId(sid), iova, len, access),
            "edge case mismatch for sid={sid:#x} iova={iova:#x} len={len:#x}"
        );
    }

    // 2,000-op deterministic differential fuzzer checking exact `Result<DmaTranslation, DmaFault>` equality!
    let mut rng = 0xd1b5_4a32_d192_ed03u64;
    let sids = [0u32, 0x10, 0x20, 0x30, 0x50, 0x66, 0x80, u32::MAX];
    let bases = [
        0x1000_0000u64,
        0x1000_ff00,
        0x1001_0000,
        0x2000_0000,
        0x201f_f800,
        0x3000_0000,
        0x5000_0000,
        0x6015_0000, // KernelPageTable SMMU radix arena base!
        COMMIT_PRIVATE_PADDR,
        1u64 << 48,
        u64::MAX - 64,
    ];
    let mut ok_count = 0usize;
    let mut err_count = 0usize;
    for step in 0..2000usize {
        rng ^= rng >> 12;
        rng ^= rng << 25;
        rng ^= rng >> 27;
        let sid = sids[(rng as usize) % sids.len()];
        let base = if step % 2 == 0 {
            match sid {
                0x10 => 0x1000_0000,
                0x20 => 0x2000_0000,
                0x30 => 0x3000_0000,
                0x50 => 0x5000_0000,
                _ => bases[((rng >> 8) as usize) % bases.len()],
            }
        } else {
            bases[((rng >> 8) as usize) % bases.len()]
        };
        let off = (rng >> 16) & 0x3fff;
        let len = (rng >> 32) & 0x2fff; // includes 0, sub-page, and multi-page lengths up to ~12 KiB!
        let access = if (rng >> 48) & 1 == 0 {
            DmaAccess::Read
        } else {
            DmaAccess::Write
        };
        let iova = base.wrapping_add(off);
        let hw_res = walk_smmuv3_stage2(&arena, StreamId(sid), iova, len, access);
        let spec_res = translate_dma(&policy, StreamId(sid), iova, len, access);
        assert_eq!(
            hw_res, spec_res,
            "2000-op differential fuzz mismatch at step={step} sid={sid:#x} iova={iova:#x} len={len:#x}"
        );
        match hw_res {
            Ok(tr) => {
                ok_count += 1;
                // Verify NO translated DMA ever touches the SMMU radix arena (`0x6015_0000..0x6017_0000`)!
                assert!(
                    tr.paddr + tr.len <= arena.arena_base_paddr()
                        || tr.paddr >= arena.arena_base_paddr() + arena.total_allocated_bytes()
                );
            }
            Err(_) => err_count += 1,
        }
    }
    assert!(ok_count > 200);
    assert!(err_count > 1000);
}

#[test]
fn stateful_iotlb_refuses_unsynced_reconfig_and_enforces_tlbi_sync_epoch_safety() {
    let base_policy = canonical_policy();
    let mut arena0 = RadixTableArena::<20>::empty();
    arena0
        .compile_into(&base_policy, 0x6015_0000)
        .expect("epoch 0 arena");
    let mut arena1 = RadixTableArena::<20>::empty();
    let mut engine = SmmuIotlbEngine::<16, 32>::new();

    // Warm the IOTLB with a writable IngressNic (`0x10`) DMA translation at `0x1000_0000 -> DMA_POOL_BASE`.
    let hit0 = engine
        .translate_with_iotlb(&arena0, StreamId(0x10), 0x1000_0040, 64, DmaAccess::Write)
        .expect("epoch 0 DMA write cached");
    assert_eq!(hit0.paddr, DMA_POOL_BASE + 0x40);
    assert_eq!(engine.live_entry_count(), 1);

    let vmid_ingress = arena0.stream_vmid(StreamId(0x10)).unwrap();
    assert_eq!(vmid_ingress, 0x10);
    let old_reg = INGRESS_REGIONS[0];

    // Epoch 1 policy: unmap `DMA_POOL_BASE..DMA_POOL_BASE+0x1_0000` from `IngressNic` (`0x10`),
    // moving `IngressNic` to `DMA_POOL_BASE + 0x6_0000` so the old frames can be repurposed safely!
    let reassigned_ingress = [DmaRegion {
        iova: 0x1000_0000,
        paddr: DMA_POOL_BASE + 0x6_0000,
        size: 4 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let mut epoch1_streams = CANONICAL_STREAMS;
    epoch1_streams[0].regions = &reassigned_ingress;
    let epoch1_policy = ChokepointIommuPolicy {
        streams: &epoch1_streams,
        ..base_policy
    };
    arena1
        .compile_into(&epoch1_policy, 0x6015_0000)
        .expect("unflushed arena1");

    // 1. Active-arena enforcement: BEFORE `unmap_or_reassign_dma_region` commits `arena1`,
    //    passing the unactivated `arena1` is refused (`StaleOrForeignArenaEpoch`) on BOTH cached-hit
    //    (`0x1000_0040`) and miss (`0x1000_1000`) paths, while `arena0` still hits `DMA_POOL_BASE`!
    let live_hit = engine
        .translate_with_iotlb(&arena0, StreamId(0x10), 0x1000_0040, 64, DmaAccess::Write)
        .expect("epoch-0 IOTLB entry still live on arena0 before TLBI+SYNC");
    assert_eq!(live_hit.paddr, DMA_POOL_BASE + 0x40);
    assert_eq!(
        engine.translate_with_iotlb(&arena1, StreamId(0x10), 0x1000_0040, 64, DmaAccess::Write),
        Err(DmaFault::StaleOrForeignArenaEpoch)
    );
    assert_eq!(
        engine.translate_with_iotlb(&arena1, StreamId(0x10), 0x1000_1000, 64, DmaAccess::Write),
        Err(DmaFault::StaleOrForeignArenaEpoch)
    );

    // 1b. Spoofing `old_vmid` (e.g., passing `0x99` instead of `vmid_ingress = 0x10`) is refused!
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                0x99,
                &old_reg,
                &epoch1_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::InvalidOldStreamVmidOrRegion {
            stream_id: 0x10,
            claimed_vmid: 0x99,
        }
    );

    // 2. Attempting `unmap_or_reassign_dma_region` with NO invalidation commands is refused (`MissingCfgiSte`)!
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &epoch1_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::MissingCfgiSte { stream_id: 0x10 }
    );

    // 3. Arm IHI 0070 §4.3.1: `CMD_CFGI_STE + CMD_SYNC` alone flushes STE config cache ONLY,
    //    leaving the VMID-tagged IOTLB entry LIVE (`live_entry_count() == 1`) and refusing reconfig!
    engine
        .submit_raw_cmd([0x0000_0010_0000_0003, 0])
        .expect("raw CMD_CFGI_STE");
    engine
        .submit_raw_cmd([0x46, 0])
        .expect("raw CMD_SYNC");
    assert_eq!(
        engine.live_entry_count(),
        1,
        "CMD_CFGI_STE + CMD_SYNC alone must NOT evict VMID-tagged IOTLB entries"
    );
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &epoch1_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::MissingCoveringTlbiS2Ipa {
            vmid: vmid_ingress,
            iova: old_reg.iova,
        }
    );
    // Malformed RES0 bits [63:48] in raw command words are rejected!
    assert_eq!(
        engine.submit_raw_cmd([0x0001_0010_0000_002a, old_reg.iova]),
        Err(TlbiReconfigError::MalformedCommandWords([
            0x0001_0010_0000_002a,
            old_reg.iova,
        ]))
    );

    // 4. Submitting covering `CMD_TLBI_S2_IPA` WITHOUT `CMD_SYNC` is refused (`UnsyncedCommandsPending`),
    //    AND the stale IOTLB entry is STILL live in hardware!
    for page_idx in 0..16u64 {
        let words = SmmuCmd::TlbiS2Ipa {
            vmid: vmid_ingress,
            ipa: old_reg.iova + page_idx * PAGE_SIZE_4K,
            leaf: false,
        }
        .pack()
        .unwrap();
        engine.submit_raw_cmd(words).unwrap();
    }
    assert_eq!(engine.live_entry_count(), 1, "pending TLBI must not evict before CMD_SYNC");
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &epoch1_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::UnsyncedCommandsPending
    );

    // 5. Issuing `CMD_SYNC` drains the queue and evicts the IOTLB entry, BUT if a DMA miss refills
    //    from `arena0` AFTER `CMD_SYNC` and BEFORE `unmap_or_reassign_dma_region`, `synced_len` is
    //    invalidated so the stale `CMD_SYNC` CANNOT be replayed!
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(engine.live_entry_count(), 0);
    let _refilled = engine
        .translate_with_iotlb(&arena0, StreamId(0x10), 0x1000_0040, 64, DmaAccess::Write)
        .expect("refill from arena0 after early sync");
    assert_eq!(engine.live_entry_count(), 1);
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &epoch1_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::MissingCfgiSte { stream_id: 0x10 }
    );

    // 6. Batching `CMD_CFGI_STE` + `CMD_TLBI_S2_IPA` + `CMD_SYNC` WITHOUT an intervening `CMD_SYNC`
    //    between `CFGI_STE` and `TLBI_S2_IPA` is refused per Arm IHI 0070 §3.21.1.1; adding `CMD_SYNC`
    //    after `CMD_CFGI_STE` and then issuing `CMD_TLBI_S2_IPA` + `CMD_SYNC` unlocks `epoch1_policy`!
    engine
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for page_idx in 0..16u64 {
        engine
            .submit_cmd(SmmuCmd::TlbiS2Ipa {
                vmid: vmid_ingress,
                ipa: old_reg.iova + page_idx * PAGE_SIZE_4K,
                leaf: false,
            })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(engine.live_entry_count(), 0);

    let truncated_streams = [epoch1_streams[0]];
    let sneaky_policy = ChokepointIommuPolicy {
        streams: &truncated_streams,
        ..epoch1_policy
    };
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &sneaky_policy,
                0x6015_0000,
                &mut arena1,
            )
            .unwrap_err(),
        TlbiReconfigError::UnannouncedMappingChange {
            stream_id: CANONICAL_STREAMS[1].stream_id.0,
            iova_base: 0,
        }
    );

    engine
        .unmap_or_reassign_dma_region(
            &arena0,
            StreamId(0x10),
            vmid_ingress,
            &old_reg,
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        )
        .expect("CFGI_STE + covering TLBI_S2_IPA + CMD_SYNC unlocks safe epoch transition");
    assert_eq!(engine.epoch(), 1);

    // Subsequent DMA on `0x10` now resolves to the new physical frame `DMA_POOL_BASE + 0x6_0040`, never old `DMA_POOL_BASE`!
    let hit1 = engine
        .translate_with_iotlb(&arena1, StreamId(0x10), 0x1000_0040, 64, DmaAccess::Write)
        .expect("epoch 1 DMA write");
    assert_eq!(hit1.paddr, DMA_POOL_BASE + 0x6_0040);
    assert_eq!(engine.live_entry_count(), 1);

    // 7. Verify `CMD_TLBI_S12_VMALL(vmid_ingress) + CMD_SYNC` evicts all live entries for `vmid_ingress`,
    //    AND passing retired `arena0` as `old_arena` at epoch 1 or keeping `reassigned_ingress[0]` unchanged is refused!
    let mut scratch_arena = RadixTableArena::<20>::empty();
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena0,
                StreamId(0x10),
                vmid_ingress,
                &old_reg,
                &base_policy,
                0x6015_0000,
                &mut scratch_arena,
            )
            .unwrap_err(),
        TlbiReconfigError::StaleOrMismatchedOldArena
    );
    assert_eq!(
        engine
            .unmap_or_reassign_dma_region(
                &arena1,
                StreamId(0x10),
                vmid_ingress,
                &reassigned_ingress[0],
                &epoch1_policy,
                0x6015_0000,
                &mut scratch_arena,
            )
            .unwrap_err(),
        TlbiReconfigError::TargetRegionUnchanged
    );
    engine
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: vmid_ingress })
        .unwrap();
    assert_eq!(engine.live_entry_count(), 1, "pending TLBI_S12_VMALL must wait for CMD_SYNC");
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(engine.live_entry_count(), 0, "synced TLBI_S12_VMALL evicts vmid_ingress IOTLB entries");
}

#[test]
fn stateful_iotlb_enforces_arena_base_binding_cfgi_ordering_subtree_coherence_queue_bounds_and_multi_epoch() {
    // 1. CommandQueueFull on both pending queue and synced window (`MAX_CMDS = 2`):
    let mut tiny_q = SmmuIotlbEngine::<4, 2>::new();
    tiny_q
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    tiny_q
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 })
        .unwrap();
    assert_eq!(
        tiny_q.submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 }),
        Err(TlbiReconfigError::CommandQueueFull)
    );
    tiny_q.submit_cmd(SmmuCmd::Sync).unwrap();
    tiny_q
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    assert_eq!(
        tiny_q.submit_cmd(SmmuCmd::Sync),
        Err(TlbiReconfigError::CommandQueueFull)
    );

    // 2. Same-policy, different-`arena_base` (`0x6015_0000` vs `0x6015_8000` inside `KernelPageTable`) is refused!
    let base_policy = canonical_policy();
    let arena_a = RadixTableArena::<24>::compile(&base_policy, 0x6015_0000).unwrap();
    let arena_b = RadixTableArena::<24>::compile(&base_policy, 0x6015_8000).unwrap();
    assert_eq!(arena_a.policy_digest(), arena_b.policy_digest());
    let mut engine = SmmuIotlbEngine::<16, 64>::new();
    engine
        .translate_with_iotlb(&arena_a, StreamId(0x10), 0x1000_0000, 64, DmaAccess::Write)
        .expect("bind engine to arena_a at 0x6015_0000");
    assert_eq!(engine.active_arena_base(), Some(0x6015_0000));
    // Foreign arena `arena_b` is refused on BOTH cached IOTLB hit (`0x1000_0000`) AND miss (`0x1000_1000`)!
    assert_eq!(
        engine.translate_with_iotlb(&arena_b, StreamId(0x10), 0x1000_0000, 64, DmaAccess::Write),
        Err(DmaFault::StaleOrForeignArenaEpoch)
    );
    assert_eq!(
        engine.translate_with_iotlb(&arena_b, StreamId(0x10), 0x1000_1000, 64, DmaAccess::Write),
        Err(DmaFault::StaleOrForeignArenaEpoch)
    );

    // Epoch 1 policy that spans two 2 MiB windows on stream `0x10` (`0x101f_f000..0x1020_1000`),
    // allocating +1 L3 table and shifting the physical L0..L3 frames of streams `0x20..0x50`!
    let split_2m_ingress = [DmaRegion {
        iova: 0x101f_f000,
        paddr: DMA_POOL_BASE + 0x6_0000,
        size: 2 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let mut epoch1_streams = CANONICAL_STREAMS;
    epoch1_streams[0].regions = &split_2m_ingress;
    let epoch1_policy = ChokepointIommuPolicy {
        streams: &epoch1_streams,
        ..base_policy
    };
    let mut arena1 = RadixTableArena::<24>::empty();

    // Passing `arena_b` (same policy digest & epoch 0, wrong physical base `0x6015_8000`) as `old_arena` is refused!
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena_b,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        ),
        Err(TlbiReconfigError::StaleOrMismatchedOldArena)
    );

    // 3. Reversed ordering (`CMD_TLBI_S12_VMALL` BEFORE `CMD_CFGI_STE`) is refused!
    engine
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 })
        .unwrap();
    engine
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena_a,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        ),
        Err(TlbiReconfigError::MissingCoveringTlbiS2Ipa {
            vmid: 0x10,
            iova: INGRESS_REGIONS[0].iova,
        })
    );

    // 4. Proper `CFGI_STE(0x10) -> TLBI_S12_VMALL(0x10) -> SYNC`, but streams `0x20..0x50` shifted physical
    //    table addresses (+1 L3 table on `0x10`), so omitting `CFGI_STE(0x20)` / `TLBI_S12_VMALL(0x20)` is refused!
    engine
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena_a,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        ),
        Err(TlbiReconfigError::MissingCfgiSte { stream_id: 0x20 })
    );
    for &sid in &[0x20u32, 0x30, 0x40, 0x50] {
        engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena_a,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        ),
        Err(TlbiReconfigError::MissingWalkCacheTlbiVmall { vmid: 0x20 })
    );
    for &vmid in &[0x20u16, 0x30, 0x40, 0x50] {
        engine.submit_cmd(SmmuCmd::TlbiS12Vmall { vmid }).unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    engine
        .unmap_or_reassign_dma_region(
            &arena_a,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch1_policy,
            0x6015_0000,
            &mut arena1,
        )
        .expect("Epoch 0 -> Epoch 1 succeeds once shifted streams flush CFGI_STE + TLBI_S12_VMALL");
    assert_eq!(engine.epoch(), 1);
    let hit_e1 = engine
        .translate_with_iotlb(&arena1, StreamId(0x10), 0x101f_f080, 64, DmaAccess::Write)
        .expect("epoch 1 split-2M translation");
    assert_eq!(hit_e1.paddr, DMA_POOL_BASE + 0x6_0080);

    // 5. Multi-epoch transition `Epoch 1 -> Epoch 2` into new physical arena base `0x6015_8000`
    //    (verifying single-batch CFGI+TLBI without intervening CMD_SYNC is refused, AND weakening
    //    CommitPrivate protected ranges across epochs is refused)!
    let epoch2_ingress = [DmaRegion {
        iova: 0x101f_f000,
        paddr: DMA_POOL_BASE + 0x7_0000,
        size: 2 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let mut epoch2_streams = epoch1_streams;
    epoch2_streams[0].regions = &epoch2_ingress;
    let epoch2_policy = ChokepointIommuPolicy {
        streams: &epoch2_streams,
        ..epoch1_policy
    };
    let mut arena2 = RadixTableArena::<24>::empty();
    // Single-batch `CFGI_STE + TLBI_S12_VMALL + SYNC` without intervening `CMD_SYNC` is refused!
    engine
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    engine
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena1,
            StreamId(0x10),
            0x10,
            &split_2m_ingress[0],
            &epoch2_policy,
            0x6015_8000,
            &mut arena2,
        ),
        Err(TlbiReconfigError::MissingCoveringTlbiS2Ipa {
            vmid: 0x10,
            iova: split_2m_ingress[0].iova,
        })
    );
    // Now complete proper two-barrier `CFGI_STE(0x10..0x50) -> SYNC -> TLBI_S12_VMALL(0x10..0x50) -> SYNC`:
    for &sid in &[0x20u32, 0x30, 0x40, 0x50] {
        engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        engine
            .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: sid as u16 })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();

    // Shrinking `CommitPrivate` protected range across epochs is refused (`ProtectedRangeWeakened`)!
    let mut shrunk_prot = PROTECTED_RANGES;
    shrunk_prot[0].size = PAGE_SIZE_4K;
    let weakened_policy = ChokepointIommuPolicy {
        protected_ranges: &shrunk_prot,
        ..epoch2_policy
    };
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena1,
            StreamId(0x10),
            0x10,
            &split_2m_ingress[0],
            &weakened_policy,
            0x6015_8000,
            &mut arena2,
        ),
        Err(TlbiReconfigError::ProtectedRangeWeakened {
            class: ProtectedFrameClass::CommitPrivate,
            base_paddr: PROTECTED_RANGES[0].base_paddr,
        })
    );

    engine
        .unmap_or_reassign_dma_region(
            &arena1,
            StreamId(0x10),
            0x10,
            &split_2m_ingress[0],
            &epoch2_policy,
            0x6015_8000,
            &mut arena2,
        )
        .expect("Epoch 1 -> Epoch 2 transition into 0x6015_8000");
    assert_eq!(engine.epoch(), 2);
    assert_eq!(engine.active_arena_base(), Some(0x6015_8000));
    let hit_e2 = engine
        .translate_with_iotlb(&arena2, StreamId(0x10), 0x101f_f080, 64, DmaAccess::Write)
        .expect("epoch 2 translation");
    assert_eq!(hit_e2.paddr, DMA_POOL_BASE + 0x7_0080);

    // 6. Multi-epoch cumulative outbox protection (`Epoch 2 -> Epoch 3 -> Epoch 4`):
    //    Retiring `EgressOutboxRing` (`0x30`) in `Epoch 2 -> 3` still forbids repurposing that
    //    retired outbox physical frame as writable DMA in `Epoch 3 -> 4`!
    let mut epoch3_streams = epoch2_streams;
    epoch3_streams[2].regions = &[];
    let epoch3_policy = ChokepointIommuPolicy {
        streams: &epoch3_streams,
        ..epoch2_policy
    };
    let mut arena3 = RadixTableArena::<24>::empty();
    for &sid in &[0x30u32, 0x40, 0x50] {
        engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for &sid in &[0x30u32, 0x40, 0x50] {
        engine
            .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: sid as u16 })
            .unwrap();
    }
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    engine
        .unmap_or_reassign_dma_region(
            &arena2,
            StreamId(0x30),
            0x30,
            &EGRESS_REGIONS[0],
            &epoch3_policy,
            0x6015_8000,
            &mut arena3,
        )
        .expect("Epoch 2 -> Epoch 3 retires EgressOutboxRing on stream 0x30");
    assert_eq!(engine.epoch(), 3);

    // Build an alternate `arena3_no_history` via a separate engine that NEVER mapped `EGRESS_REGIONS[0]`,
    // reaching the EXACT SAME `(built_epoch = 3, policy_digest = epoch3_policy, arena_base_paddr = 0x6015_8000)`!
    let mut alt_engine = SmmuIotlbEngine::<16, 64>::new();
    let mut alt_streams0 = CANONICAL_STREAMS;
    alt_streams0[2].regions = &[];
    let alt_pol0 = ChokepointIommuPolicy {
        streams: &alt_streams0,
        ..base_policy
    };
    let mut alt_streams1 = alt_streams0;
    alt_streams1[0].regions = &split_2m_ingress;
    let alt_pol1 = ChokepointIommuPolicy {
        streams: &alt_streams1,
        ..base_policy
    };
    let alt_arena0 = RadixTableArena::<24>::compile(&alt_pol0, 0x6015_8000).unwrap();
    let mut alt_arena1 = RadixTableArena::<24>::empty();
    let mut alt_arena2 = RadixTableArena::<24>::empty();
    let mut arena3_no_history = RadixTableArena::<24>::empty();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: sid as u16 })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    alt_engine
        .unmap_or_reassign_dma_region(
            &alt_arena0,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &alt_pol1,
            0x6015_8000,
            &mut alt_arena1,
        )
        .unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: sid as u16 })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    alt_engine
        .unmap_or_reassign_dma_region(
            &alt_arena1,
            StreamId(0x10),
            0x10,
            &split_2m_ingress[0],
            &alt_pol0,
            0x6015_8000,
            &mut alt_arena2,
        )
        .unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::CfgiSte {
                stream_id: StreamId(sid),
                leaf: false,
            })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    for &sid in &[0x10u32, 0x20, 0x30, 0x40, 0x50] {
        alt_engine
            .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: sid as u16 })
            .unwrap();
    }
    alt_engine.submit_cmd(SmmuCmd::Sync).unwrap();
    alt_engine
        .unmap_or_reassign_dma_region(
            &alt_arena2,
            StreamId(0x10),
            0x10,
            &INGRESS_REGIONS[0],
            &epoch3_policy,
            0x6015_8000,
            &mut arena3_no_history,
        )
        .unwrap();
    assert_eq!(arena3_no_history.built_epoch(), arena3.built_epoch());
    assert_eq!(arena3_no_history.policy_digest(), arena3.policy_digest());
    assert_eq!(
        arena3_no_history.arena_base_paddr(),
        arena3.arena_base_paddr()
    );

    // Now in `Epoch 3 -> Epoch 4`, attempting to map the retired outbox physical frame
    // (`EGRESS_REGIONS[0].paddr`) as writable on stream `0x10` is refused — AND swapping in
    // `arena3_no_history` (matching epoch/digest/base, missing retired outbox history) is ALSO refused!
    let hijack_retired_outbox = [DmaRegion {
        iova: 0x101f_f000,
        paddr: EGRESS_REGIONS[0].paddr,
        size: 2 * PAGE_SIZE_4K,
        granule: PageGranule::Page4KiB,
        perm: IoPerm::ReadWrite,
        kind: DmaRegionKind::IngressRing,
    }];
    let mut epoch4_streams = epoch3_streams;
    epoch4_streams[0].regions = &hijack_retired_outbox;
    let epoch4_policy = ChokepointIommuPolicy {
        streams: &epoch4_streams,
        ..epoch3_policy
    };
    let mut arena4 = RadixTableArena::<24>::empty();
    engine
        .submit_cmd(SmmuCmd::CfgiSte {
            stream_id: StreamId(0x10),
            leaf: false,
        })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    engine
        .submit_cmd(SmmuCmd::TlbiS12Vmall { vmid: 0x10 })
        .unwrap();
    engine.submit_cmd(SmmuCmd::Sync).unwrap();
    assert_eq!(
        engine.translate_with_iotlb(
            &arena3_no_history,
            StreamId(0x10),
            0x101f_f080,
            64,
            DmaAccess::Write
        ),
        Err(DmaFault::StaleOrForeignArenaEpoch)
    );
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena3_no_history,
            StreamId(0x10),
            0x10,
            &epoch2_ingress[0],
            &epoch4_policy,
            0x6015_8000,
            &mut arena4,
        ),
        Err(TlbiReconfigError::StaleOrMismatchedOldArena)
    );
    assert_eq!(
        engine.unmap_or_reassign_dma_region(
            &arena3,
            StreamId(0x10),
            0x10,
            &epoch2_ingress[0],
            &epoch4_policy,
            0x6015_8000,
            &mut arena4,
        ),
        Err(TlbiReconfigError::OutboxFrameWriteEscalation {
            paddr: EGRESS_REGIONS[0].paddr,
        })
    );
}

