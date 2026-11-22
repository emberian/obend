//! Comprehensive conformance, anti-spoofing, non-occlusion, dual-tone hazard visibility,
//! zero-private-leakage, and Lean<->Rust golden vector parity tests for the Epiphany Lens
//! scanout compositor and `OBEND.SHE.SENSOR_SEAL/v1` sensor frame redactor/sealer.

use std::collections::{BTreeMap, BTreeSet};

use obend_surfaces::epiphany::{
    blend_alpha, blend_channel, compile_belief_view_node, composite_pixel, compute_sensor_seal,
    cshake256_32, encode_sensor_seal_preimage, luma_bt601, porter_duff_over, verify_sealed_frame,
    worst_case_dual_tone_contrast, BeliefOverlaySpec, ConsentModalRect, EpiphanyCompositor,
    EpiphanyRefusal, IntrusionPolicy, PhysicalHazardBox, PhysicalHazardReticlePlane,
    RawSensorFrame, Rect, Rgba, SensorFrameSealer, SensorTile, TrustedConsentBand,
    TrustedConsentChromePlane, UntrustedBeliefPlane, Viewport, DEFAULT_MIN_HAZARD_ALPHA,
    DEFAULT_MIN_HAZARD_CONTRAST, SENSOR_SEAL_DOMAIN,
};
use obend_surfaces::{BindFmt, Disposition, Frustum, HostStatus, ViewNode, WorldState};

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write;
        let _ = write!(&mut s, "{b:02x}");
    }
    s
}

fn sample_chrome(viewport: Viewport, with_modal: bool) -> TrustedConsentChromePlane {
    TrustedConsentChromePlane {
        viewport,
        consent_band: TrustedConsentBand::top_bar(viewport, 4),
        modal: if with_modal {
            Some(ConsentModalRect {
                rect: Rect::new(4, 6, 8, 6),
                prompt: "Approve quorum transfer?".into(),
                quorum_epoch: 7,
                bg: Rgba::new(20, 30, 50, 255),
                border_accent: Rgba::new(240, 190, 40, 255),
            })
        } else {
            None
        },
        sensor_led_active: true,
        band_bg: Rgba::CHROME_SLATE,
        led_color: Rgba::SENSOR_LED_GREEN,
    }
}

#[test]
fn porter_duff_over_algebraic_boundaries_and_bounds() {
    for src_c in (0u8..=255).step_by(17) {
        for dst_c in (0u8..=255).step_by(17) {
            assert_eq!(blend_channel(src_c, dst_c, 255), src_c);
            assert_eq!(blend_channel(src_c, dst_c, 0), dst_c);
            assert_eq!(blend_alpha(255, dst_c), 255);
            assert_eq!(blend_alpha(0, dst_c), dst_c);
            for a in (0u8..=255).step_by(15) {
                let out_a = blend_alpha(a, dst_c);
                assert!(out_a >= a);
            }
        }
    }

    let opaque = Rgba::new(12, 34, 56, 255);
    let adv = Rgba::new(255, 200, 100, 255);
    assert_eq!(porter_duff_over(opaque, adv), opaque);
    assert_eq!(porter_duff_over(Rgba::TRANSPARENT, adv), adv);
    assert_eq!(luma_bt601(Rgba::BLACK), 0);
    assert_eq!(luma_bt601(Rgba::WHITE), 255);
}

#[test]
fn chrome_non_occludable_under_arbitrary_untrusted_pixel_mutations() {
    let viewport = Viewport::new(16, 16);
    let chrome = sample_chrome(viewport, true);
    let mut hazards = PhysicalHazardReticlePlane::new(
        viewport,
        DEFAULT_MIN_HAZARD_ALPHA,
        DEFAULT_MIN_HAZARD_CONTRAST,
    );
    hazards.boxes.push(PhysicalHazardBox {
        hazard_id: "forklift-1".into(),
        rect: Rect::new(1, 5, 14, 10),
        stroke_width: 1,
        hi_color: Rgba::HAZARD_HI_YELLOW,
        lo_color: Rgba::HAZARD_LO_BLACK,
        severity: 10,
    });
    let compositor = EpiphanyCompositor::new(viewport);

    let adversarial_planes: Vec<UntrustedBeliefPlane> = (0u8..8)
        .map(|seed| {
            let mut px = Vec::with_capacity(256);
            for i in 0u32..256 {
                let r = ((i.wrapping_mul(73) ^ (seed as u32 * 41)) & 0xff) as u8;
                let g = ((i.wrapping_mul(151) ^ (seed as u32 * 97)) & 0xff) as u8;
                let b = ((i.wrapping_mul(211) ^ (seed as u32 * 131)) & 0xff) as u8;
                let a = if seed == 0 {
                    0
                } else if seed == 1 {
                    255
                } else {
                    ((i.wrapping_mul(29) + seed as u32 * 37) & 0xff) as u8
                };
                px.push(Rgba::new(r, g, b, a));
            }
            UntrustedBeliefPlane::from_pixels(viewport, px).expect("plane")
        })
        .collect();

    let baseline = compositor
        .composite_frame(&adversarial_planes[0], &hazards, &chrome)
        .expect("baseline composite");

    for plane in &adversarial_planes {
        let frame = compositor
            .composite_frame(plane, &hazards, &chrome)
            .expect("composite");
        for y in 0..viewport.height {
            for x in 0..viewport.width {
                if chrome.is_protected_pixel(x, y) {
                    let expected = chrome.pixel_at(x, y);
                    assert_eq!(
                        frame.pixel_at(x, y),
                        Some(expected),
                        "protected chrome pixel ({x},{y}) altered by untrusted plane"
                    );
                    assert_eq!(frame.pixel_at(x, y), baseline.pixel_at(x, y));
                }
            }
        }
    }

    // Non-vacuity: outside protected chrome & hazards, mutating untrusted pixels changes scanout.
    let mut changed = false;
    let f1 = compositor
        .composite_frame(&adversarial_planes[1], &hazards, &chrome)
        .expect("f1");
    for y in 0..viewport.height {
        for x in 0..viewport.width {
            if !chrome.is_protected_pixel(x, y)
                && !hazards.has_active_hazard_at(x, y)
                && f1.pixel_at(x, y) != baseline.pixel_at(x, y)
            {
                changed = true;
            }
        }
    }
    assert!(changed, "untrusted safe region must actually render");
}

#[test]
fn physical_hazard_reticle_visibility_floor_exhaustive_adversarial_backgrounds() {
    let pairs = [
        (Rgba::HAZARD_HI_YELLOW, Rgba::HAZARD_LO_BLACK),
        (Rgba::HAZARD_HI_WHITE, Rgba::HAZARD_LO_BLACK),
        (
            Rgba::new(255, 255, 255, DEFAULT_MIN_HAZARD_ALPHA),
            Rgba::new(0, 0, 0, DEFAULT_MIN_HAZARD_ALPHA),
        ),
    ];

    for &(hi, lo) in &pairs {
        assert!(hi.a >= DEFAULT_MIN_HAZARD_ALPHA);
        assert!(lo.a >= DEFAULT_MIN_HAZARD_ALPHA);
        let floor = worst_case_dual_tone_contrast(hi, lo);
        assert!(floor >= DEFAULT_MIN_HAZARD_CONTRAST);

        // Exhaustive grid over adversarial untrusted backgrounds (bg1 under hi, bg2 under lo).
        let grid: Vec<Rgba> = (0u8..=255)
            .step_by(85)
            .flat_map(|r| {
                (0u8..=255).step_by(85).flat_map(move |g| {
                    (0u8..=255)
                        .step_by(85)
                        .flat_map(move |b| [0u8, 128, 255].into_iter().map(move |a| Rgba::new(r, g, b, a)))
                })
            })
            .collect();

        for &bg1 in &grid {
            let out_hi = composite_pixel(bg1, hi, Rgba::TRANSPARENT, false);
            assert!(out_hi.a >= DEFAULT_MIN_HAZARD_ALPHA);
            let l_hi = luma_bt601(out_hi);
            for &bg2 in &[Rgba::BLACK, Rgba::WHITE, bg1, Rgba::new(255, 0, 0, 255)] {
                let out_lo = composite_pixel(bg2, lo, Rgba::TRANSPARENT, false);
                assert!(out_lo.a >= DEFAULT_MIN_HAZARD_ALPHA);
                let l_lo = luma_bt601(out_lo);
                assert!(
                    l_hi >= l_lo.saturating_add(DEFAULT_MIN_HAZARD_CONTRAST),
                    "dual-tone contrast floor violated: hi={hi:?} over bg1={bg1:?} (luma={l_hi}) vs lo={lo:?} over bg2={bg2:?} (luma={l_lo})"
                );
            }
        }
    }

    // Negative test: dim or low-contrast hazard reticle is refused fail-closed.
    let viewport = Viewport::new(16, 16);
    let chrome = sample_chrome(viewport, false);
    let untrusted = UntrustedBeliefPlane::blank(viewport).expect("blank");
    let mut weak_hazards = PhysicalHazardReticlePlane::new(
        viewport,
        DEFAULT_MIN_HAZARD_ALPHA,
        DEFAULT_MIN_HAZARD_CONTRAST,
    );
    weak_hazards.boxes.push(PhysicalHazardBox {
        hazard_id: "ghost-obstacle".into(),
        rect: Rect::new(2, 6, 8, 8),
        stroke_width: 1,
        hi_color: Rgba::new(140, 130, 125, 90),
        lo_color: Rgba::new(120, 120, 120, 90),
        severity: 5,
    });
    let err = EpiphanyCompositor::new(viewport)
        .composite_frame(&untrusted, &weak_hazards, &chrome)
        .expect_err("weak hazard must be refused");
    assert!(matches!(
        err,
        EpiphanyRefusal::HazardVisibilityViolation {
            ref hazard_id,
            actual_min_alpha: 90,
            min_alpha: DEFAULT_MIN_HAZARD_ALPHA,
            ..
        } if hazard_id == "ghost-obstacle"
    ));
}

#[test]
fn viewnode_intrusion_refusal_clipping_spoofing_and_frustum_noninterference() {
    let viewport = Viewport::new(32, 32);
    let band = TrustedConsentBand::top_bar(viewport, 6);

    let mut visible = BTreeSet::new();
    visible.insert(("circle-a".to_owned(), 0usize));
    let mut policies = BTreeMap::new();
    policies.insert(
        "secret-vault".to_owned(),
        Disposition::Sever {
            snapshot_digest: 0xCAFE,
        },
    );
    let frustum = Frustum {
        viewer: "wearer".into(),
        visible_slots: visible,
        policies,
    };

    let tree = ViewNode::VStack(vec![
        ViewNode::Bind {
            slot: 0,
            label: "distance_m".into(),
            fmt: BindFmt::Raw,
            resolved: None,
        },
        ViewNode::Host {
            cell: "secret-vault".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Bind {
                slot: 9,
                label: "private_key_id".into(),
                fmt: BindFmt::Hex,
                resolved: None,
            })),
        },
        ViewNode::Tile {
            handle: "map-overlay".into(),
            w: 100,
            h: 100,
        },
    ]);

    let intruding_spec = BeliefOverlaySpec {
        circle_id: "scout-circle".into(),
        cell: "circle-a".into(),
        requested_rect: Rect::new(0, 2, 24, 20),
        root: tree,
        fill_color: Rgba::new(40, 120, 200, 180),
    };

    let mut w1 = WorldState::default();
    w1.set("circle-a", 0, 12);
    w1.set("secret-vault", 9, 111_111);

    // 1. Refuse policy strictly rejects overlapping TrustedConsentBand.
    let refused = compile_belief_view_node(
        viewport,
        band,
        &frustum,
        &w1,
        &intruding_spec,
        IntrusionPolicy::Refuse,
    )
    .expect_err("intruding belief overlay must be refused");
    assert_eq!(
        refused,
        EpiphanyRefusal::ChromeBandIntrusion {
            circle_id: "scout-circle".into(),
            attempted: Rect::new(0, 2, 24, 20),
            reserved_band: band.rect,
        }
    );

    // 2. ClipToSafeRegion trims cleanly below TrustedConsentBand and clamps overflowing Tile.
    let compiled_1 = compile_belief_view_node(
        viewport,
        band,
        &frustum,
        &w1,
        &intruding_spec,
        IntrusionPolicy::ClipToSafeRegion,
    )
    .expect("clipped overlay");
    assert_eq!(compiled_1.safe_rect, Some(Rect::new(0, 6, 24, 16)));
    assert!(!compiled_1.boxes.is_empty());
    for b in &compiled_1.boxes {
        assert!(!b.rect.intersects(band.rect));
        assert!(b.rect.fits_within(viewport));
    }

    // 3. Frustum non-interference: mutating severed secret slot leaves compiled overlay and
    //    rasterized pixels identical; mutating visible slot changes them (non-vacuity).
    let mut w2 = w1.clone();
    w2.set("secret-vault", 9, 999_999);
    let compiled_2 = compile_belief_view_node(
        viewport,
        band,
        &frustum,
        &w2,
        &intruding_spec,
        IntrusionPolicy::ClipToSafeRegion,
    )
    .expect("clipped overlay w2");
    assert_eq!(compiled_1, compiled_2);
    let plane_1 =
        UntrustedBeliefPlane::rasterize_overlays(viewport, std::slice::from_ref(&compiled_1))
            .expect("raster 1");
    let plane_2 =
        UntrustedBeliefPlane::rasterize_overlays(viewport, &[compiled_2]).expect("raster 2");
    assert_eq!(plane_1, plane_2);

    let mut w3 = w1.clone();
    w3.set("circle-a", 0, 29);
    let compiled_3 = compile_belief_view_node(
        viewport,
        band,
        &frustum,
        &w3,
        &intruding_spec,
        IntrusionPolicy::ClipToSafeRegion,
    )
    .expect("clipped overlay w3");
    assert_ne!(compiled_1, compiled_3);

    // 4. Spoofing reserved hardware consent chrome markers is refused even outside the band.
    let spoof_spec = BeliefOverlaySpec {
        circle_id: "phishing-circle".into(),
        cell: "circle-a".into(),
        requested_rect: Rect::new(4, 10, 12, 12),
        root: ViewNode::Section {
            title: "OBEND.CHROME Verified Prompt".into(),
            tag: "normal".into(),
            children: vec![ViewNode::Button {
                label: "Approve".into(),
                turn: "she.consent.accept".into(),
                arg: 1,
            }],
        },
        fill_color: Rgba::new(20, 20, 20, 255),
    };
    let spoof_err = compile_belief_view_node(
        viewport,
        band,
        &frustum,
        &w1,
        &spoof_spec,
        IntrusionPolicy::ClipToSafeRegion,
    )
    .expect_err("chrome spoof must be refused");
    assert!(matches!(
        spoof_err,
        EpiphanyRefusal::ChromeSpoofAttempt { ref circle_id, .. } if circle_id == "phishing-circle"
    ));
}

#[test]
fn sensor_seal_v1_lean_golden_vector_byte_exact_parity() {
    // Locked cross-language golden vector shared with `Obend.Polis.EpiphanyCompositor` (#205).
    let raw = RawSensorFrame::from_full_frame(
        7,
        42,
        4,
        2,
        vec![
            Rgba::new(10, 20, 30, 255),
            Rgba::new(99, 99, 99, 255),
            Rgba::new(88, 77, 66, 255),
            Rgba::new(40, 50, 60, 255),
            Rgba::new(70, 80, 90, 255),
            Rgba::new(100, 110, 120, 255),
            Rgba::new(130, 140, 150, 255),
            Rgba::new(160, 170, 180, 255),
        ],
        vec![Rect::new(1, 0, 2, 1)],
    );

    let mut sealer = SensorFrameSealer::new();
    let sealed = sealer.seal_frame(&raw).expect("seal golden vector");

    let preimage = encode_sensor_seal_preimage(
        sealed.sensor_id,
        sealed.mono_seq,
        sealed.width,
        sealed.height,
        &sealed.redact_boxes,
        &sealed.redacted_tiles,
    );
    assert_eq!(preimage.len(), 95);
    assert_eq!(
        hex_encode(&preimage),
        "08000000000000000708000000000000002a0400000004040000000210000000010000000000000002000000013130000000000000000000000004000000020a141eff000000000000000028323cff46505aff646e78ff828c96ffa0aab4ff"
    );
    assert_eq!(
        hex_encode(&sealed.seal_digest),
        "07e36afa669af0611a69815d73f0fdb2362e7cfbfea48a937e343c38a80ab648"
    );
    assert_eq!(
        sealed.seal_digest,
        cshake256_32(SENSOR_SEAL_DOMAIN.as_bytes(), &preimage)
    );
    verify_sealed_frame(&sealed, Some(41)).expect("verify golden sealed frame");
}

#[test]
fn sensor_frame_sealer_monotonicity_zero_private_leakage_multi_tile_and_tamper_refusal() {
    let mut sealer = SensorFrameSealer::new();
    let redact_boxes = vec![Rect::new(1, 0, 2, 2)];

    // Split a 4x4 frame into two 4x2 CSI-2 horizontal strips to verify multi-tile redaction.
    let make_tiles = |secret_a: Rgba, secret_b: Rgba| {
        vec![
            SensorTile {
                tile_x: 0,
                tile_y: 0,
                tile_w: 4,
                tile_h: 2,
                pixels: vec![
                    Rgba::new(10, 20, 30, 255),
                    secret_a,
                    secret_b,
                    Rgba::new(10, 20, 30, 255),
                    Rgba::new(10, 20, 30, 255),
                    secret_b,
                    secret_a,
                    Rgba::new(10, 20, 30, 255),
                ],
            },
            SensorTile {
                tile_x: 0,
                tile_y: 2,
                tile_w: 4,
                tile_h: 2,
                pixels: vec![Rgba::new(15, 25, 35, 255); 8],
            },
        ]
    };

    let raw_a = RawSensorFrame {
        sensor_id: 42,
        mono_seq: 1,
        width: 4,
        height: 4,
        tiles: make_tiles(Rgba::new(250, 12, 34, 255), Rgba::new(199, 88, 77, 255)),
        redact_boxes: redact_boxes.clone(),
    };
    let raw_b = RawSensorFrame {
        sensor_id: 42,
        mono_seq: 1,
        width: 4,
        height: 4,
        tiles: make_tiles(Rgba::new(5, 240, 200, 128), Rgba::new(1, 2, 3, 4)),
        redact_boxes: redact_boxes.clone(),
    };

    let sealed_a = sealer.seal_frame(&raw_a).expect("seal a");
    let mut sealer_b = SensorFrameSealer::new();
    let sealed_b = sealer_b.seal_frame(&raw_b).expect("seal b");

    // Zero private leakage: arbitrary mutations inside `redact_boxes` yield identical redacted
    // tiles AND identical `OBEND.SHE.SENSOR_SEAL/v1` digests.
    assert_eq!(sealed_a.redacted_tiles, sealed_b.redacted_tiles);
    assert_eq!(sealed_a.seal_digest, sealed_b.seal_digest);
    for idx in [1usize, 2, 5, 6] {
        assert_eq!(sealed_a.redacted_tiles[0].pixels[idx], Rgba::TRANSPARENT);
    }
    assert_eq!(
        sealed_a.redacted_tiles[0].pixels[0],
        Rgba::new(10, 20, 30, 255)
    );
    verify_sealed_frame(&sealed_a, None).expect("verify sealed_a");

    // Replay (same seq) and rollback (lower seq) are strictly refused without mutating state.
    assert_eq!(
        sealer.seal_frame(&raw_a),
        Err(EpiphanyRefusal::SensorSeqRollback {
            sensor_id: 42,
            last_seq: 1,
            attempted_seq: 1,
        })
    );
    let mut rollback = raw_a.clone();
    rollback.mono_seq = 0;
    assert_eq!(
        sealer.seal_frame(&rollback),
        Err(EpiphanyRefusal::SensorSeqRollback {
            sensor_id: 42,
            last_seq: 1,
            attempted_seq: 0,
        })
    );

    // Strictly advancing sequence succeeds; independent sensor_id has independent counter.
    let mut frame_2 = raw_a.clone();
    frame_2.mono_seq = 2;
    let sealed_2 = sealer.seal_frame(&frame_2).expect("seal seq 2");
    assert_ne!(sealed_a.seal_digest, sealed_2.seal_digest);

    let mut other_sensor = raw_a.clone();
    other_sensor.sensor_id = 99;
    other_sensor.mono_seq = 1;
    let sealed_other = sealer.seal_frame(&other_sensor).expect("seal sensor 99");
    SensorFrameSealer::verify_sealed_trace(&[sealed_a.clone(), sealed_2.clone(), sealed_other])
        .expect("valid multi-sensor trace");

    // Replay inside a sealed trace is rejected.
    assert!(matches!(
        SensorFrameSealer::verify_sealed_trace(&[sealed_2.clone(), sealed_a.clone()]),
        Err(EpiphanyRefusal::SensorSeqRollback {
            sensor_id: 42,
            last_seq: 2,
            attempted_seq: 1,
        })
    ));

    // Tampering with a redacted pixel triggers UnredactedPrivateRoi.
    let mut leaky = sealed_a.clone();
    leaky.redacted_tiles[0].pixels[1] = Rgba::new(1, 0, 0, 255);
    assert_eq!(
        verify_sealed_frame(&leaky, None),
        Err(EpiphanyRefusal::UnredactedPrivateRoi {
            tile_index: 0,
            box_index: 0,
            x: 1,
            y: 0,
        })
    );

    // Tampering with an unredacted pixel without updating the digest triggers SealDigestMismatch.
    let mut tampered = sealed_a.clone();
    tampered.redacted_tiles[0].pixels[0] = Rgba::new(11, 20, 30, 255);
    assert!(matches!(
        verify_sealed_frame(&tampered, None),
        Err(EpiphanyRefusal::SealDigestMismatch { .. })
    ));

    // Domain separation check.
    let pre = encode_sensor_seal_preimage(
        sealed_a.sensor_id,
        sealed_a.mono_seq,
        sealed_a.width,
        sealed_a.height,
        &sealed_a.redact_boxes,
        &sealed_a.redacted_tiles,
    );
    let expected = compute_sensor_seal(
        sealed_a.sensor_id,
        sealed_a.mono_seq,
        sealed_a.width,
        sealed_a.height,
        &sealed_a.redact_boxes,
        &sealed_a.redacted_tiles,
    );
    assert_eq!(expected, cshake256_32(SENSOR_SEAL_DOMAIN.as_bytes(), &pre));
    assert_ne!(expected, cshake256_32(b"OBEND.SHE.SENSOR_SEAL/v2", &pre));
}

#[test]
fn adversarial_geometry_overflow_nonopaque_chrome_and_depth_budget_refusals() {
    let viewport = Viewport::new(32, 32);
    let band = TrustedConsentBand::top_bar(viewport, 4);

    // u32 overflow rect must not panic and must fail fits_within.
    let overflow_rect = Rect::new(u32::MAX - 2, 0, 10, 10);
    assert!(!overflow_rect.fits_within(viewport));
    assert!(!overflow_rect.contains(0, 0));

    // Non-opaque chrome band or consent modal must be refused fail-closed.
    let mut non_opaque_chrome = sample_chrome(viewport, true);
    non_opaque_chrome.band_bg.a = 254;
    let blank = UntrustedBeliefPlane::blank(viewport).expect("blank");
    let hazards = PhysicalHazardReticlePlane::new(
        viewport,
        DEFAULT_MIN_HAZARD_ALPHA,
        DEFAULT_MIN_HAZARD_CONTRAST,
    );
    assert!(matches!(
        EpiphanyCompositor::new(viewport).composite_frame(&blank, &hazards, &non_opaque_chrome),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));

    let mut non_opaque_modal = sample_chrome(viewport, true);
    non_opaque_modal.modal.as_mut().unwrap().bg.a = 200;
    assert!(matches!(
        EpiphanyCompositor::new(viewport).composite_frame(&blank, &hazards, &non_opaque_modal),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));

    // Undersized hazard box incapable of hosting dual-tone outer + inner rings must be refused.
    let mut bad_hazards = hazards;
    bad_hazards.boxes.push(PhysicalHazardBox {
        hazard_id: "tiny".into(),
        rect: Rect::new(2, 6, 3, 3),
        stroke_width: 1,
        hi_color: Rgba::HAZARD_HI_YELLOW,
        lo_color: Rgba::HAZARD_LO_BLACK,
        severity: 1,
    });
    assert!(matches!(
        bad_hazards.validate(),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));

    // ViewNode exceeding MAX_VIEW_DEPTH must be refused.
    let mut deep = ViewNode::Divider;
    for _ in 0..=obend_surfaces::MAX_VIEW_DEPTH + 1 {
        deep = ViewNode::Adept(Box::new(deep));
    }
    let frustum = Frustum {
        viewer: "wearer".into(),
        visible_slots: BTreeSet::new(),
        policies: BTreeMap::new(),
    };
    let world = WorldState::default();
    let deep_spec = BeliefOverlaySpec {
        circle_id: "deep-circle".into(),
        cell: "c".into(),
        requested_rect: Rect::new(0, 6, 16, 16),
        root: deep,
        fill_color: Rgba::new(10, 20, 30, 200),
    };
    assert!(matches!(
        compile_belief_view_node(
            viewport,
            band,
            &frustum,
            &world,
            &deep_spec,
            IntrusionPolicy::Refuse
        ),
        Err(EpiphanyRefusal::ViewBudgetExceeded { .. })
    ));

    // Interposed host attempting to spoof `hardware_led` must be refused.
    let spoof_host = BeliefOverlaySpec {
        circle_id: "mock-circle".into(),
        cell: "c".into(),
        requested_rect: Rect::new(0, 6, 16, 16),
        root: ViewNode::Host {
            cell: "sub".into(),
            status: HostStatus::Interposed {
                mock_label: "fake_hardware_led".into(),
            },
            view: None,
        },
        fill_color: Rgba::new(10, 20, 30, 200),
    };
    assert!(matches!(
        compile_belief_view_node(
            viewport,
            band,
            &frustum,
            &world,
            &spoof_host,
            IntrusionPolicy::ClipToSafeRegion
        ),
        Err(EpiphanyRefusal::ChromeSpoofAttempt { .. })
    ));

    // Out-of-bounds or truncated CSI-2 SensorTile must be refused fail-closed.
    let mut sealer = SensorFrameSealer::new();
    let oob_frame = RawSensorFrame {
        sensor_id: 1,
        mono_seq: 1,
        width: 4,
        height: 4,
        tiles: vec![SensorTile {
            tile_x: 2,
            tile_y: 0,
            tile_w: 4,
            tile_h: 2,
            pixels: vec![Rgba::BLACK; 8],
        }],
        redact_boxes: vec![],
    };
    assert!(matches!(
        sealer.seal_frame(&oob_frame),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));
    assert_eq!(sealer.last_seq(1), None);

    // Zero-dimension sensor frame must be refused and must NOT advance monotone sequence state.
    let zero_dim_frame = RawSensorFrame {
        sensor_id: 77,
        mono_seq: 1,
        width: 0,
        height: 0,
        tiles: vec![],
        redact_boxes: vec![],
    };
    assert!(matches!(
        sealer.seal_frame(&zero_dim_frame),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));
    assert_eq!(sealer.last_seq(77), None);

    // Zero-dimension CSI-2 SensorTile inside a non-empty frame must be refused.
    let zero_tile_frame = RawSensorFrame {
        sensor_id: 77,
        mono_seq: 1,
        width: 4,
        height: 4,
        tiles: vec![SensorTile {
            tile_x: 0,
            tile_y: 0,
            tile_w: 0,
            tile_h: 0,
            pixels: vec![],
        }],
        redact_boxes: vec![],
    };
    assert!(matches!(
        sealer.seal_frame(&zero_tile_frame),
        Err(EpiphanyRefusal::InvalidGeometry { .. })
    ));
    assert_eq!(sealer.last_seq(77), None);

    // Protected chrome flag hard-zeroes untrusted belief pixels even without chrome opaqueness.
    assert_eq!(
        composite_pixel(
            Rgba::new(255, 128, 64, 255),
            Rgba::TRANSPARENT,
            Rgba::TRANSPARENT,
            true,
        ),
        Rgba::TRANSPARENT
    );
}

#[test]
fn end_to_end_multi_frame_sealer_and_compositor_pipeline() {
    let viewport = Viewport::new(16, 16);
    let chrome = sample_chrome(viewport, true);
    let mut hazards = PhysicalHazardReticlePlane::new(
        viewport,
        DEFAULT_MIN_HAZARD_ALPHA,
        DEFAULT_MIN_HAZARD_CONTRAST,
    );
    hazards.boxes.push(PhysicalHazardBox {
        hazard_id: "low-sev".into(),
        rect: Rect::new(2, 6, 10, 8),
        stroke_width: 1,
        hi_color: Rgba::HAZARD_HI_YELLOW,
        lo_color: Rgba::HAZARD_LO_BLACK,
        severity: 3,
    });
    hazards.boxes.push(PhysicalHazardBox {
        hazard_id: "high-sev".into(),
        rect: Rect::new(2, 6, 10, 8),
        stroke_width: 1,
        hi_color: Rgba::HAZARD_HI_WHITE,
        lo_color: Rgba::HAZARD_LO_BLACK,
        severity: 9,
    });
    // Higher-severity hazard wins on overlapping outer ring pixel (2, 6).
    assert_eq!(hazards.pixel_at(2, 6), Rgba::HAZARD_HI_WHITE);
    // Inner ring pixel (3, 7) renders lo_color.
    assert_eq!(hazards.pixel_at(3, 7), Rgba::HAZARD_LO_BLACK);

    let mut sealer = SensorFrameSealer::new();
    let mut sealed_trace = Vec::new();
    let compositor = EpiphanyCompositor::new(viewport);

    let frustum = Frustum {
        viewer: "wearer".into(),
        visible_slots: BTreeSet::from([("nav".to_owned(), 0usize)]),
        policies: BTreeMap::new(),
    };
    let mut world = WorldState::default();

    for seq in 1u64..=3 {
        world.set("nav", 0, seq * 10);
        let raw = RawSensorFrame::from_full_frame(
            1,
            seq,
            4,
            4,
            vec![Rgba::new((seq * 30) as u8, 40, 50, 255); 16],
            vec![Rect::new(0, 0, 2, 2)],
        );
        let sealed = sealer.seal_frame(&raw).expect("seal frame");
        sealed_trace.push(sealed);

        let overlay = compile_belief_view_node(
            viewport,
            chrome.consent_band,
            &frustum,
            &world,
            &BeliefOverlaySpec {
                circle_id: "nav-circle".into(),
                cell: "nav".into(),
                requested_rect: Rect::new(0, 0, 16, 16),
                root: ViewNode::Bind {
                    slot: 0,
                    label: "heading".into(),
                    fmt: BindFmt::Raw,
                    resolved: None,
                },
                fill_color: Rgba::new(20, 80, 160, 180),
            },
            IntrusionPolicy::ClipToSafeRegion,
        )
        .expect("compile overlay");
        let untrusted =
            UntrustedBeliefPlane::rasterize_overlays(viewport, &[overlay]).expect("rasterize");
        let frame = compositor
            .composite_frame(&untrusted, &hazards, &chrome)
            .expect("composite");

        // Sensor LED inside TrustedConsentBand and ConsentModalRect are untouched every turn.
        let led = chrome.sensor_led_rect();
        assert_eq!(frame.pixel_at(led.x, led.y), Some(Rgba::SENSOR_LED_GREEN));
        assert_eq!(
            frame.pixel_at(5, 7),
            chrome.modal.as_ref().unwrap().pixel_at(5, 7)
        );
    }

    SensorFrameSealer::verify_sealed_trace(&sealed_trace).expect("trace valid");
}
