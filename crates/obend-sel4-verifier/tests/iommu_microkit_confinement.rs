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
        size: 16 * PAGE_SIZE_4K,
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
