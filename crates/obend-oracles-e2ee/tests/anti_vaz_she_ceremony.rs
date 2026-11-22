#![forbid(unsafe_code)]
//! Multi-Turn Sovereign SHE ("Anti-Vaz") Ceremony & Cross-Language Conformance Suite.
//!
//! Verifies byte-exact parity against `lean/Obend/Polis/SecureHardwareEnv.lean` and
//! `lean/tests/metasystem/SecureHardwareEnvTest.lean`, integration with `obend-oracles-e2ee`'s
//! TLSNotary / TEE / E2EE verifiers, and fail-closed refusals against every Vaz-coercion,
//! `< t` custodian coalition, ToF relay, withdrawn-CBR zkML, nullifier-replay, budget-overrun,
//! and `seL4` TOCTOU attack vector.

use std::collections::BTreeMap;

use obend_oracles_e2ee::{
    apply_oracle_attested_actuation, apply_she_turn, chutes_report_data_binding,
    fixture_build_intel_tdx_quote, fixture_build_nvidia_rim_swid_xml, fixture_issue_cert_der,
    fixture_issue_ocsp_der, fixture_notarize, fixture_sign_spdm_report, hex_encode_lower,
    legacy_withdrawn_cbr_milli_bits, notary_key_fingerprint, proven_zkml_milli_bits, run_she_trace,
    she_floors_digest, she_payload_digest, she_turn_envelope_digest, verify_e2ee_channel,
    verify_intel_tdx, verify_nvidia_gpu, verify_tlsn_transcript, ActuationTurnProposal,
    BasicConstraints, CandidateComputation, CertRecord, E2eeChannelInput, E2eeChannelPolicy,
    FixtureCertSpec, FixtureSigner, FixtureTdxQuoteFields, GpuArch, IntelTdxAttestation,
    IntelTdxMeasurementPin, IntelTdxPolicy, KeyUsage, MandateAttenuation, NvidiaGpuAttestation,
    NvidiaGpuPolicy, NvidiaOcspResponse, NvidiaOcspStatus, PinnedNotaryEntry,
    PinnedNotaryRegistry, SealedOracleIngress, SheFloor, SheRefusal, SheState, SheTurn,
    SignatureAlgorithm, TlsnTranscriptEnvelope, UpgradeAuthorityClaim, UpgradeJudgeProposal,
    ZkmlSoundnessRegime, KEY_USAGE_DIGITAL_SIGNATURE, KEY_USAGE_KEY_CERT_SIGN,
    ML_KEM_768_PUBKEY_LEN, NO_SERVICE_TD, OPAQUE_CHIP_SKU, OPAQUE_FWID, OPAQUE_PROJECT,
    OPAQUE_PROJECT_SKU, SPDM_NONCE_LEN, SPDM_SIGNATURE_LEN,
};

fn canonical_genesis_floors() -> Vec<SheFloor> {
    vec![
        SheFloor::SensorRoiRedaction {
            min_redacted_rois: 2,
        },
        SheFloor::ConsentBandNonOcclusion {
            min_band_height_px: 32,
        },
        SheFloor::ZkmlProvenSoundnessMilliBits {
            min_milli_bits: 100_000,
        },
        SheFloor::PhysicalProximityMaxTicks { max_ticks: 50 },
        SheFloor::E2eeTeeChannelBound {
            min_attested_gpus: 1,
        },
        SheFloor::OperatorLocalRevert {
            max_revert_steps: 8,
        },
    ]
}

fn canonical_genesis_state() -> SheState {
    SheState {
        habitat_judge_digest: [0x10; 32],
        pinned_model_weights_root: [0x22; 32],
        mono_sensor_seq: 0,
        consumed_nullifiers: Vec::new(),
        remaining_mandate_budget: 100,
        active_safety_and_privacy_floors: canonical_genesis_floors(),
        settled_outbox_actions: Vec::new(),
        custodian_threshold_t: 3,
        custodian_total_n: 5,
        custodian_quorum_epoch: 1,
        revoked_custodians: Vec::new(),
        max_proximity_ticks: 50,
        revert_window_steps: 4,
    }
}

fn golden_turn_1() -> ActuationTurnProposal {
    let payload = b"ACT1".to_vec();
    let floors = canonical_genesis_floors();
    ActuationTurnProposal {
        sensor_seq: 1,
        sensor_seal_digest: [0x33; 32],
        candidate: CandidateComputation {
            statement_digest: [0x11; 32],
            model_weights_root: [0x22; 32],
            bound_floors_digest: she_floors_digest(&floors),
            sensor_seal_digest: [0x33; 32],
            action_payload_digest: she_payload_digest(&payload),
            regime: ZkmlSoundnessRegime::UniqueDecodingUdr,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            ext_field_bits: 100,
            proof_verified: true,
        },
        nullifier: [0x44; 32],
        mandate_cost: 25,
        redacted_roi_count: 3,
        consent_band_height_px: 40,
        attested_gpu_count: 2,
        shared_ring_at_copy: payload.clone(),
        private_frame_copy: payload.clone(),
        dispatched_payload: payload,
        simplex_committee_n: 4,
        simplex_faulty_f: 1,
        simplex_finalize_signers: vec![0, 1, 2],
        custodian_epoch: 1,
        custodian_signers: vec![0, 2, 3],
        tof_round_trip_ticks: 18,
    }
}

fn golden_turn_2() -> UpgradeJudgeProposal {
    let mut new_floors = canonical_genesis_floors();
    new_floors.push(SheFloor::SensorRoiRedaction {
        min_redacted_rois: 4,
    });
    UpgradeJudgeProposal {
        new_judge_digest: [0x55; 32],
        new_model_weights_root: [0x22; 32],
        new_floors,
        new_revert_window_steps: 6,
        new_custodian_epoch: 2,
        custodian_signers: vec![0, 1, 3],
        tof_round_trip_ticks: 15,
        authority_claim: UpgradeAuthorityClaim::LocalCustodianCeremony,
    }
}

fn golden_turn_3() -> MandateAttenuation {
    MandateAttenuation {
        new_budget_cap: 50,
        new_max_proximity_ticks: 30,
        newly_revoked_custodians: vec![4],
        reason_digest: [0x66; 32],
    }
}

fn golden_turn_4() -> ActuationTurnProposal {
    let payload = b"ACT2".to_vec();
    let mut upgraded_floors = canonical_genesis_floors();
    upgraded_floors.push(SheFloor::SensorRoiRedaction {
        min_redacted_rois: 4,
    });
    ActuationTurnProposal {
        sensor_seq: 2,
        sensor_seal_digest: [0x72; 32],
        candidate: CandidateComputation {
            statement_digest: [0x71; 32],
            model_weights_root: [0x22; 32],
            bound_floors_digest: she_floors_digest(&upgraded_floors),
            sensor_seal_digest: [0x72; 32],
            action_payload_digest: she_payload_digest(&payload),
            regime: ZkmlSoundnessRegime::JohnsonBoundJbr,
            log_blowup: 6,
            num_queries: 30,
            grind_bits: 16,
            ext_field_bits: 100,
            proof_verified: true,
        },
        nullifier: [0x73; 32],
        mandate_cost: 40,
        redacted_roi_count: 4,
        consent_band_height_px: 48,
        attested_gpu_count: 2,
        shared_ring_at_copy: payload.clone(),
        private_frame_copy: payload.clone(),
        dispatched_payload: payload,
        simplex_committee_n: 4,
        simplex_faulty_f: 1,
        simplex_finalize_signers: vec![1, 2, 3],
        custodian_epoch: 2,
        custodian_signers: vec![0, 1, 2],
        tof_round_trip_ticks: 22,
    }
}

#[test]
fn lean_rust_she_turn_wire_vectors_match_byte_for_byte() {
    assert_eq!(
        hex_encode_lower(&she_floors_digest(&canonical_genesis_floors())),
        "6f6491a661a8e2d178544e84cd4917fda6e6eb451ae9f49c4a211588096c6811"
    );
    assert_eq!(
        hex_encode_lower(&she_payload_digest(b"ACT1")),
        "1839254e8817686d0ea77ebcdf95f57f61b01582ed8ed01dc471c60f2a602d57"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(
            &SheTurn::ProposeAndSettleActuation(golden_turn_1())
        )),
        "38dbf7839d0460ff2415223e050389e78fd6542726b3365d3f62cd33ce7589c5"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(&SheTurn::UpgradeHabitatJudge(
            golden_turn_2()
        ))),
        "04d22d3d57805d267b0aa866b597223edae6b8c408a3d8e12f1125f75317e3e0"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(
            &SheTurn::RevokeOrAttenuateMandate(golden_turn_3())
        )),
        "4703fd475cbe80a9dee00cc86a023b0341874af30ba13a45aa61080a05f159ac"
    );
}

#[test]
fn multi_turn_sovereign_she_ceremony_conserves_budget_and_strengthens_floors() {
    let init = canonical_genesis_state();
    assert!(init.well_formed());
    let trace = vec![
        SheTurn::ProposeAndSettleActuation(golden_turn_1()),
        SheTurn::UpgradeHabitatJudge(golden_turn_2()),
        SheTurn::RevokeOrAttenuateMandate(golden_turn_3()),
        SheTurn::ProposeAndSettleActuation(golden_turn_4()),
    ];
    let end = run_she_trace(&init, &trace).expect("valid 4-turn ceremony should succeed");
    assert_eq!(end.mono_sensor_seq, 2);
    assert_eq!(end.settled_outbox_actions.len(), 2);
    assert_eq!(end.settled_total_cost(), 65);
    assert_eq!(end.remaining_mandate_budget, 10);
    assert!(end.settled_total_cost() + end.remaining_mandate_budget <= init.remaining_mandate_budget);
    assert_eq!(end.custodian_quorum_epoch, 2);
    assert_eq!(end.max_proximity_ticks, 30);
    for floor in &init.active_safety_and_privacy_floors {
        assert!(end.active_safety_and_privacy_floors.contains(floor));
    }
    assert_ne!(
        end.settled_outbox_actions[0].nullifier,
        end.settled_outbox_actions[1].nullifier
    );
    assert!(
        end.settled_outbox_actions[0].sensor_seq < end.settled_outbox_actions[1].sensor_seq
    );
}

#[test]
fn vaz_coercive_floor_downgrades_refused_under_vendor_and_agency_signatures() {
    let st = canonical_genesis_state();

    // 1. External intelligence agency order attempting to drop sensor ROI redaction floor.
    let mut dropped_roi = canonical_genesis_floors();
    dropped_roi.retain(|f| !matches!(f, SheFloor::SensorRoiRedaction { .. }));
    let agency_attack = SheTurn::UpgradeHabitatJudge(UpgradeJudgeProposal {
        new_judge_digest: [0x99; 32],
        new_model_weights_root: [0x22; 32],
        new_floors: dropped_roi,
        new_revert_window_steps: 4,
        new_custodian_epoch: 2,
        custodian_signers: vec![0, 1, 2, 3, 4],
        tof_round_trip_ticks: 10,
        authority_claim: UpgradeAuthorityClaim::AgencyEmergencyOrder {
            agency_id: b"EXTERNAL_CABAL_VAZ".to_vec(),
            agency_sig: vec![0xAB; 64],
        },
    });
    assert_eq!(
        apply_she_turn(&st, &agency_attack),
        Err(SheRefusal::CoerciveFloorDowngrade {
            dropped_floor: SheFloor::SensorRoiRedaction {
                min_redacted_rois: 2
            }
        })
    );

    // 2. Vendor root directive attempting to weaken 100-bit zkML floor down to 34 bits.
    let weakened_zkml = vec![
        SheFloor::SensorRoiRedaction {
            min_redacted_rois: 2,
        },
        SheFloor::ConsentBandNonOcclusion {
            min_band_height_px: 32,
        },
        SheFloor::ZkmlProvenSoundnessMilliBits {
            min_milli_bits: 34_000,
        },
        SheFloor::PhysicalProximityMaxTicks { max_ticks: 50 },
        SheFloor::E2eeTeeChannelBound {
            min_attested_gpus: 1,
        },
        SheFloor::OperatorLocalRevert {
            max_revert_steps: 8,
        },
    ];
    let vendor_attack = SheTurn::UpgradeHabitatJudge(UpgradeJudgeProposal {
        new_judge_digest: [0x98; 32],
        new_model_weights_root: [0x22; 32],
        new_floors: weakened_zkml,
        new_revert_window_steps: 4,
        new_custodian_epoch: 2,
        custodian_signers: vec![0, 1, 2, 3],
        tof_round_trip_ticks: 10,
        authority_claim: UpgradeAuthorityClaim::VendorRootDirective {
            vendor_sig: vec![0xCD; 64],
        },
    });
    assert_eq!(
        apply_she_turn(&st, &vendor_attack),
        Err(SheRefusal::CoerciveFloorDowngrade {
            dropped_floor: SheFloor::ZkmlProvenSoundnessMilliBits {
                min_milli_bits: 100_000
            }
        })
    );
}

#[test]
fn subthreshold_duplicate_and_revoked_custodian_coalitions_refused() {
    let st = canonical_genesis_state();

    // Coerced `< t` coalition (2 < 3).
    let mut subthreshold = golden_turn_1();
    subthreshold.custodian_signers = vec![0, 2];
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(subthreshold)),
        Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: 2,
            required_t: 3
        })
    );

    // Coerced `< t` coalition padding signer list with duplicate ID `[0, 0, 2]`.
    let mut dup_signers = golden_turn_1();
    dup_signers.custodian_signers = vec![0, 0, 2];
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(dup_signers)),
        Err(SheRefusal::DuplicateOrOutOfRangeSigner)
    );

    // Revoking custodian 4 in turn 3 blocks custodian 4 from participating in turn 4.
    let st_after_3 = run_she_trace(
        &st,
        &[
            SheTurn::ProposeAndSettleActuation(golden_turn_1()),
            SheTurn::UpgradeHabitatJudge(golden_turn_2()),
            SheTurn::RevokeOrAttenuateMandate(golden_turn_3()),
        ],
    )
    .unwrap();
    let mut with_revoked = golden_turn_4();
    with_revoked.custodian_signers = vec![0, 1, 4];
    assert_eq!(
        apply_she_turn(
            &st_after_3,
            &SheTurn::ProposeAndSettleActuation(with_revoked)
        ),
        Err(SheRefusal::RevokedCustodianSigner { signer: 4 })
    );
}

#[test]
fn tof_relay_cbr_weak_zkml_nullifier_replay_budget_and_toctou_refused() {
    let st = canonical_genesis_state();

    // 1. Remote fiber/satellite ToF relay attack (`tof_round_trip_ticks = 51 > 50`).
    let mut relay = golden_turn_1();
    relay.tof_round_trip_ticks = 51;
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(relay)),
        Err(SheRefusal::TofProximityExceeded {
            actual_ticks: 51,
            max_ticks: 50
        })
    );

    // 2. Withdrawn CBR-weak zkML `(lb=6, q=19, pow=16)`: 130 CBR bits vs 34.563 UDR bits.
    let mut cbr_turn = golden_turn_1();
    cbr_turn.candidate.regime = ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr;
    cbr_turn.candidate.num_queries = 19;
    assert_eq!(legacy_withdrawn_cbr_milli_bits(&cbr_turn.candidate), 130_000);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(cbr_turn)),
        Err(SheRefusal::WithdrawnCbrRegimeRefused)
    );

    let mut weak_udr = golden_turn_1();
    weak_udr.candidate.regime = ZkmlSoundnessRegime::UniqueDecodingUdr;
    weak_udr.candidate.num_queries = 19;
    assert_eq!(proven_zkml_milli_bits(&weak_udr.candidate), 34_563);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(weak_udr)),
        Err(SheRefusal::BelowProven100BitFloor {
            actual_milli_bits: 34_563
        })
    );

    let mut fake_grind = golden_turn_1();
    fake_grind.candidate.regime = ZkmlSoundnessRegime::UniqueDecodingUdr;
    fake_grind.candidate.log_blowup = 1;
    fake_grind.candidate.num_queries = 1;
    fake_grind.candidate.grind_bits = 100;
    assert_eq!(proven_zkml_milli_bits(&fake_grind.candidate), 24_415);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(fake_grind)),
        Err(SheRefusal::BelowProven100BitFloor {
            actual_milli_bits: 24_415
        })
    );

    // 3. Multi-turn nullifier replay, sensor sequence rollback, budget overrun, & amplification.
    let st1 = apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(golden_turn_1())).unwrap();

    let mut non_monotone_seq = golden_turn_1();
    non_monotone_seq.sensor_seq = 1;
    non_monotone_seq.nullifier = [0x91; 32];
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::ProposeAndSettleActuation(non_monotone_seq)),
        Err(SheRefusal::NonMonotoneSensorSeq {
            current_seq: 1,
            proposed_seq: 1
        })
    );

    let mut replay = golden_turn_1();
    replay.sensor_seq = 2;
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::ProposeAndSettleActuation(replay)),
        Err(SheRefusal::NullifierReplayed)
    );

    let mut budget_overrun = golden_turn_1();
    budget_overrun.sensor_seq = 2;
    budget_overrun.nullifier = [0x92; 32];
    budget_overrun.mandate_cost = 76; // remaining after turn 1 is 75
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::ProposeAndSettleActuation(budget_overrun)),
        Err(SheRefusal::MandateBudgetExceeded {
            requested: 76,
            available: 75
        })
    );

    assert_eq!(
        apply_she_turn(
            &st1,
            &SheTurn::RevokeOrAttenuateMandate(MandateAttenuation {
                new_budget_cap: 80,
                new_max_proximity_ticks: 40,
                newly_revoked_custodians: vec![],
                reason_digest: [0x93; 32],
            })
        ),
        Err(SheRefusal::MandateAmplificationRefused)
    );

    // 4. `seL4` private-frame copy-before-verify mismatch & Simplex under-quorum QC refused.
    let mut toctou_mismatch = golden_turn_1();
    toctou_mismatch.dispatched_payload = b"EVIL".to_vec();
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(toctou_mismatch)),
        Err(SheRefusal::PrivateFrameCopyMismatch)
    );

    let mut bad_qc = golden_turn_1();
    bad_qc.simplex_finalize_signers = vec![0, 1]; // needs n - f = 3
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(bad_qc)),
        Err(SheRefusal::InvalidSimplexFinalityQc {
            signed_count: 2,
            required_quorum: 3
        })
    );
}

// ---------------------------------------------------------------------------
// End-to-End Integration with `obend-oracles-e2ee` TLSNotary + TDX + Hopper GPU + E2EE
// ---------------------------------------------------------------------------

fn make_ca_cert(
    subject_cn: &str,
    issuer_cn: &str,
    serial: u8,
    subject_signer: &FixtureSigner,
    issuer_signer: &FixtureSigner,
    sig_alg: SignatureAlgorithm,
) -> CertRecord {
    let der = fixture_issue_cert_der(
        &FixtureCertSpec {
            subject_cn,
            issuer_cn,
            serial: &[serial],
            not_before: 1_000,
            not_after: 10_000,
            subject_key: subject_signer.public_key(),
            basic_constraints: Some(BasicConstraints {
                is_ca: true,
                path_len_constraint: Some(2),
            }),
            key_usage: Some(KeyUsage::new(KEY_USAGE_KEY_CERT_SIGN)),
            ocsp_signing_eku: false,
            dice_fwid: None,
            amd_vcek_ext: None,
        },
        issuer_signer,
        sig_alg,
    );
    CertRecord::from_der(&der).expect("valid SHE CA cert DER")
}

fn make_leaf_cert(
    subject_cn: &str,
    issuer_cn: &str,
    serial: u8,
    fwid: Option<[u8; 48]>,
    subject_signer: &FixtureSigner,
    issuer_signer: &FixtureSigner,
    sig_alg: SignatureAlgorithm,
) -> CertRecord {
    let der = fixture_issue_cert_der(
        &FixtureCertSpec {
            subject_cn,
            issuer_cn,
            serial: &[serial],
            not_before: 1_000,
            not_after: 10_000,
            subject_key: subject_signer.public_key(),
            basic_constraints: Some(BasicConstraints {
                is_ca: false,
                path_len_constraint: None,
            }),
            key_usage: Some(KeyUsage::new(KEY_USAGE_DIGITAL_SIGNATURE)),
            ocsp_signing_eku: false,
            dice_fwid: fwid,
            amd_vcek_ext: None,
        },
        issuer_signer,
        sig_alg,
    );
    CertRecord::from_der(&der).expect("valid SHE leaf cert DER")
}

fn build_spdm_report(
    nonce: &[u8; SPDM_NONCE_LEN],
    fwid: &[u8; 48],
    meas1: &[u8],
    gpu_leaf_signer: &FixtureSigner,
) -> Vec<u8> {
    let mut req = vec![0x11, 0xE0, 0x00, 0x01];
    req.extend_from_slice(nonce);
    req.push(0x00);
    assert_eq!(req.len(), 37);

    let mut block = vec![0x01];
    block.extend_from_slice(&(meas1.len() as u16).to_le_bytes());
    block.extend_from_slice(meas1);
    let mut record = vec![1u8, 1u8];
    record.extend_from_slice(&(block.len() as u16).to_le_bytes());
    record.extend_from_slice(&block);

    let mut opaque = Vec::new();
    for (ty, val) in [
        (OPAQUE_CHIP_SKU, b"H100-SXM\0".as_slice()),
        (OPAQUE_PROJECT, b"2330\0".as_slice()),
        (OPAQUE_PROJECT_SKU, b"0200\0".as_slice()),
        (OPAQUE_FWID, fwid.as_slice()),
    ] {
        opaque.extend_from_slice(&ty.to_le_bytes());
        opaque.extend_from_slice(&(val.len() as u16).to_le_bytes());
        opaque.extend_from_slice(val);
    }

    let mut resp = vec![0x11, 0x60, 0x00, 0x00, 1u8];
    let rlen = record.len() as u32;
    resp.extend_from_slice(&[rlen as u8, (rlen >> 8) as u8, (rlen >> 16) as u8]);
    resp.extend_from_slice(&record);
    resp.extend_from_slice(&[0x55; SPDM_NONCE_LEN]);
    resp.extend_from_slice(&(opaque.len() as u16).to_le_bytes());
    resp.extend_from_slice(&opaque);
    resp.extend_from_slice(&[0u8; SPDM_SIGNATURE_LEN]);

    let mut full = req;
    full.extend_from_slice(&resp);
    fixture_sign_spdm_report(&mut full, gpu_leaf_signer);
    full
}

fn base64_encode(bytes: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b0 = chunk[0];
        let b1 = *chunk.get(1).unwrap_or(&0);
        let b2 = *chunk.get(2).unwrap_or(&0);
        out.push(TABLE[(b0 >> 2) as usize] as char);
        out.push(TABLE[(((b0 & 0x03) << 4) | (b1 >> 4)) as usize] as char);
        if chunk.len() > 1 {
            out.push(TABLE[(((b1 & 0x0F) << 2) | (b2 >> 6)) as usize] as char);
        } else {
            out.push('=');
        }
        if chunk.len() > 2 {
            out.push(TABLE[(b2 & 0x3F) as usize] as char);
        } else {
            out.push('=');
        }
    }
    out
}

#[test]
fn end_to_end_tlsn_tdx_gpu_e2ee_oracle_receipt_drives_sovereign_she_ceremony() {
    let now_secs = 2_000u64;

    // 1. Verify a registry-pinned TLSNotary HTTPS transcript with a real Ed25519 notary signature.
    let notary_signer = FixtureSigner::ed25519(b"pinned-she-notary-v1");
    let notary_key_sha = notary_key_fingerprint(&notary_signer.public_key());
    let registry = PinnedNotaryRegistry::new(vec![PinnedNotaryEntry {
        operator_id: "polis-notary-1".to_string(),
        notary_key_sha256: notary_key_sha,
        allowed_servers: vec!["sensor.polis.local".to_string()],
        valid_from: 1_000,
        valid_until: 5_000,
    }]);
    let mut tlsn_env = TlsnTranscriptEnvelope {
        server_name: "sensor.polis.local".to_string(),
        expected_path: "/v1/epiphany/frame".to_string(),
        connection_time: 2_000,
        sent_bytes: b"GET /v1/epiphany/frame HTTP/1.1\r\nHost: sensor.polis.local\r\n\r\n".to_vec(),
        recv_bytes: b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"hazard\":\"clear\",\"rois_redacted\":3}".to_vec(),
        unauthed_recv_ranges: Vec::new(),
        notary_public_key: notary_signer.public_key(),
        notary_signature_alg: SignatureAlgorithm::Ed25519,
        notary_signature: Vec::new(),
        claimed_notary_key_hex: None,
    };
    fixture_notarize(&mut tlsn_env, &notary_signer, SignatureAlgorithm::Ed25519);
    let verified_tlsn =
        verify_tlsn_transcript(&registry, &tlsn_env, Some("hazard"), now_secs).unwrap();
    assert_eq!(verified_tlsn.extracted_field(), Some("clear"));

    // 2. Verify Intel TDX CPU (P-256) + NVIDIA Hopper H100 GPU (P-384) TEE evidence & E2EE channel binding.
    let nonce_bytes = [0x42u8; 32];
    let nonce_hex = hex_encode_lower(&nonce_bytes);
    let mlkem_pub = vec![0x77u8; ML_KEM_768_PUBKEY_LEN];
    let pubkey_b64 = base64_encode(&mlkem_pub);
    let rd_32 = chutes_report_data_binding(&nonce_hex, &pubkey_b64);
    let mut cpu_report_data = [0u8; 64];
    cpu_report_data[..32].copy_from_slice(&rd_32);

    let intel_root_k = FixtureSigner::p256(b"she-intel-root");
    let pck_leaf_k = FixtureSigner::p256(b"she-pck-leaf");
    let tdx_att_k = FixtureSigner::p256(b"she-tdx-att-key");
    let intel_root = make_ca_cert(
        "Intel Root",
        "Intel Root",
        0x01,
        &intel_root_k,
        &intel_root_k,
        SignatureAlgorithm::EcdsaP256Sha256,
    );
    let pck_leaf = make_leaf_cert(
        "PCK Leaf",
        "Intel Root",
        0x02,
        None,
        &pck_leaf_k,
        &intel_root_k,
        SignatureAlgorithm::EcdsaP256Sha256,
    );

    let mr_td = [0x11u8; 48];
    let rt0 = [0x12u8; 48];
    let rt1 = [0x13u8; 48];
    let rt2 = [0x14u8; 48];
    let tdx_policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256(),
        measurement_pin: IntelTdxMeasurementPin {
            mr_td,
            rt_mr0: rt0,
            rt_mr1: rt1,
            rt_mr2: rt2,
            pin_rtmr3: None,
        },
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: Vec::new(),
    };
    let tdx_quote_bytes = fixture_build_intel_tdx_quote(
        &FixtureTdxQuoteFields {
            mr_td,
            rt_mr0: rt0,
            rt_mr1: rt1,
            rt_mr2: rt2,
            rt_mr3: [0u8; 48],
            mr_servicetd: Some(NO_SERVICE_TD),
            td_attributes: 0,
            report_data: cpu_report_data,
            qe_auth_data: b"she-qe-auth".to_vec(),
        },
        &[intel_root, pck_leaf],
        &pck_leaf_k,
        &tdx_att_k,
    );
    let tdx_att = IntelTdxAttestation {
        quote_bytes: tdx_quote_bytes,
        tcb_status: "UpToDate".to_string(),
    };
    let cpu_tee = verify_intel_tdx(&tdx_policy, &tdx_att, now_secs).unwrap();

    let fwid = [0x5Au8; 48];
    let meas1 = vec![0xDEu8; 48];
    let mut golden_measurements = BTreeMap::new();
    golden_measurements.insert(1u8, vec![meas1.clone()]);

    let nv_dev_root_k = FixtureSigner::p384(b"she-nv-dev-root");
    let nv_gpu_leaf_k = FixtureSigner::p384(b"she-nv-gpu-leaf");
    let nv_rim_root_k = FixtureSigner::p384(b"she-nv-rim-root");
    let nv_rim_leaf_k = FixtureSigner::p384(b"she-nv-rim-leaf");
    let p384_alg = SignatureAlgorithm::EcdsaP384Sha384;

    let nv_dev_root = make_ca_cert(
        "NVIDIA Device Root",
        "NVIDIA Device Root",
        0x11,
        &nv_dev_root_k,
        &nv_dev_root_k,
        p384_alg,
    );
    let nv_gpu_leaf = make_leaf_cert(
        "H100 Leaf",
        "NVIDIA Device Root",
        0x12,
        Some(fwid),
        &nv_gpu_leaf_k,
        &nv_dev_root_k,
        p384_alg,
    );
    let nv_rim_root = make_ca_cert(
        "NVIDIA RIM Root",
        "NVIDIA RIM Root",
        0x13,
        &nv_rim_root_k,
        &nv_rim_root_k,
        p384_alg,
    );
    let nv_rim_leaf = make_leaf_cert(
        "RIM Signer",
        "NVIDIA RIM Root",
        0x14,
        None,
        &nv_rim_leaf_k,
        &nv_rim_root_k,
        p384_alg,
    );

    let gpu_policy = NvidiaGpuPolicy {
        arch: GpuArch::HopperH100,
        pinned_device_root_sha256: nv_dev_root.cert_sha256(),
        pinned_corim_root_sha256: nv_rim_root.cert_sha256(),
        expected_driver_version: "550.54.15".to_string(),
        expected_vbios_version: "96.00.89.00.01".to_string(),
        pinned_fwid: fwid,
    };
    let driver_rim = fixture_build_nvidia_rim_swid_xml(
        GpuArch::HopperH100,
        "550.54.15",
        &[nv_rim_root.clone(), nv_rim_leaf.clone()],
        &golden_measurements,
        &nv_rim_leaf_k,
    );
    let vbios_rim = fixture_build_nvidia_rim_swid_xml(
        GpuArch::HopperH100,
        "96.00.89.00.01",
        &[nv_rim_root.clone(), nv_rim_leaf.clone()],
        &golden_measurements,
        &nv_rim_leaf_k,
    );

    let ocsp_dev = NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
        &nv_dev_root,
        &nv_gpu_leaf,
        NvidiaOcspStatus::Good,
        1_500,
        5_000,
        &nv_dev_root_k,
        p384_alg,
    ))
    .unwrap();
    let ocsp_rim = NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
        &nv_rim_root,
        &nv_rim_leaf,
        NvidiaOcspStatus::Good,
        1_500,
        5_000,
        &nv_rim_root_k,
        p384_alg,
    ))
    .unwrap();

    let gpu_att = NvidiaGpuAttestation {
        spdm_report_bytes: build_spdm_report(&nonce_bytes, &fwid, &meas1, &nv_gpu_leaf_k),
        device_cert_chain: vec![nv_dev_root, nv_gpu_leaf],
        driver_rim,
        vbios_rim,
        ocsp_responses: vec![ocsp_dev, ocsp_rim],
    };
    let gpu_tee = verify_nvidia_gpu(&gpu_policy, &gpu_att, &nonce_bytes, now_secs).unwrap();

    let e2ee_channel = verify_e2ee_channel(
        &E2eeChannelPolicy::default(),
        &E2eeChannelInput {
            chute_id: "epiphany-she-planner".to_string(),
            instance_id: "she-node-01".to_string(),
            attestation_nonce_hex: nonce_hex,
            e2e_pubkey_b64: pubkey_b64,
        },
        &cpu_tee,
        std::slice::from_ref(&gpu_tee),
        now_secs,
    )
    .unwrap();

    // 3. Seal Turn 1 from TLSNotary + TEE, and Turn 2 from E2EE channel + TEE!
    let ingress_1 = SealedOracleIngress::from_tlsn_and_tee(
        1,
        &verified_tlsn,
        &cpu_tee,
        std::slice::from_ref(&gpu_tee),
    )
    .unwrap();
    let st0 = canonical_genesis_state();
    let payload_1 = b"ACT_TLSN".to_vec();
    let mut act1 = golden_turn_1();
    act1.sensor_seq = ingress_1.mono_seq();
    act1.sensor_seal_digest = ingress_1.seal_digest();
    act1.attested_gpu_count = ingress_1.attested_gpu_count();
    act1.shared_ring_at_copy = payload_1.clone();
    act1.private_frame_copy = payload_1.clone();
    act1.dispatched_payload = payload_1.clone();
    act1.candidate.sensor_seal_digest = ingress_1.seal_digest();
    act1.candidate.action_payload_digest = she_payload_digest(&payload_1);

    let st1 = apply_oracle_attested_actuation(&st0, &ingress_1, &act1).unwrap();
    assert_eq!(st1.settled_outbox_actions.len(), 1);
    assert_eq!(
        st1.settled_outbox_actions[0].sensor_seal_digest,
        verified_tlsn.transcript_digest()
    );

    // Mismatched seal digest against SealedOracleIngress is fail-closed refused.
    let ingress_2 =
        SealedOracleIngress::from_verified_e2ee_channel(2, &e2ee_channel, &cpu_tee).unwrap();
    let mut forged_act = act1.clone();
    forged_act.sensor_seq = 2;
    forged_act.nullifier = [0x99; 32];
    assert_eq!(
        apply_oracle_attested_actuation(&st1, &ingress_2, &forged_act),
        Err(SheRefusal::OracleEvidenceBindingMismatch)
    );
}
