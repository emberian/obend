#![forbid(unsafe_code)]
//! Multi-Turn Sovereign SHE ("Anti-Vaz") Ceremony & Cross-Language Conformance Suite.
//!
//! Verifies byte-exact parity against `lean/Obend/Polis/SecureHardwareEnv.lean` and
//! `lean/tests/metasystem/SecureHardwareEnvTest.lean` with REAL grounded cryptography:
//! - Grounded `ZkmlSuiteArtifact` + `CandidateComputation` `UD-100` receipt gate (`1 <= logArity`,
//!   pinned `observed_num_queries == pinned_num_queries`, post-commit PoW grinding, supporting both
//!   `(lb=6, q=86, pow=16)` and wide-leaf `(lb=2, q=148, pow=0)`, refusing withdrawn `CBR`);
//! - Sampled bit-exact `s8 x E2M1` (`MXFP4`) integer recompute audit (`fpaudit` commit-before-coin
//!   Fiat–Shamir catching steered argmaxes that any positive logit-tolerance `tau > 0` admits);
//! - Full-width 256-bit post-quantum `cshake256Suite` (`w=4, ell1=128` `WOTS+C` + `XMSS`
//!   and stateless `leanSPHINCS` with `20×5 = 100`-bit `FORS`) custodian & Simplex QC quorums;
//! - Fail-closed refusals against steered logits, commit-after-coin, non-E2M1/out-of-s8 witnesses,
//!   unpinned `numQueries`/`logArity = 0`, weak 16-bit PQ parameter downgrades, forged/replayed PQ
//!   signatures, reused stateful XMSS leaves, Vaz coercive floor downgrades, `< t` coalitions,
//!   ToF relay attacks, withdrawn CBR, nullifier replays, budget overruns, `seL4` TOCTOU mismatches,
//!   and end-to-end TLSNotary + TDX + H100 GPU + E2EE oracle ingress (treating external sensors/displays
//!   strictly as untrusted I/O).

use std::collections::BTreeMap;

use obend_oracles_e2ee::she_ceremony::{
    argmax_idx, build_honest_candidate, candidate_pow_hash, candidate_statement_digest,
    check_suite_artifact, derive_pq_public_key, eval_pq_single_sign, exact_int_dot,
    fpaudit_commit_root, fpaudit_opened_round_idx, fpaudit_output_root, fpaudit_weights_root,
    has_low_zero_bits, she_custodian_actuation_msg, she_custodian_upgrade_msg, she_simplex_qc_msg,
    she_state_digest, suite_artifact_digest, suite_proven_milli_bits, tolerance_logit_check,
    verify_candidate_computation, verify_exact_recompute_audit, verify_she_pq_sig, zigzag_encode,
    PqHashParams, PqHashSig, PqPublicKey, PqSecretKey, ZkmlSuiteArtifact,
};
use obend_oracles_e2ee::{
    apply_oracle_attested_actuation, apply_she_turn, chutes_report_data_binding,
    fixture_build_intel_tdx_quote, fixture_build_nvidia_rim_swid_xml, fixture_issue_cert_der,
    fixture_issue_ocsp_der, fixture_notarize, fixture_sign_spdm_report, hex_encode_lower,
    legacy_withdrawn_cbr_milli_bits, notary_key_fingerprint, proven_zkml_milli_bits, run_she_trace,
    she_floors_digest, she_payload_digest, she_turn_envelope_digest, verify_e2ee_channel,
    verify_intel_tdx, verify_nvidia_gpu, verify_tlsn_transcript, ActuationTurnProposal,
    BasicConstraints, CertRecord, E2eeChannelInput, E2eeChannelPolicy,
    FixtureCertSpec, FixtureSigner, FixtureTdxQuoteFields, GpuArch, IntelTdxAttestation,
    IntelTdxMeasurementPin, IntelTdxPolicy, KeyUsage, MandateAttenuation, NvidiaGpuAttestation,
    NvidiaGpuPolicy, NvidiaOcspResponse, NvidiaOcspStatus, PinnedNotaryEntry,
    PinnedNotaryRegistry, SealedOracleIngress, SheFloor, SheRefusal, SheState, SheTurn,
    SignatureAlgorithm, TlsnTranscriptEnvelope, UpgradeAuthorityClaim, UpgradeJudgeProposal,
    ZkmlSoundnessRegime, KEY_USAGE_DIGITAL_SIGNATURE, KEY_USAGE_KEY_CERT_SIGN,
    ML_KEM_768_PUBKEY_LEN, NO_SERVICE_TD, OPAQUE_CHIP_SKU, OPAQUE_FWID, OPAQUE_PROJECT,
    OPAQUE_PROJECT_SKU, SPDM_NONCE_LEN, SPDM_SIGNATURE_LEN,
};

const OPT_RAND: [u8; 32] = [0x5A; 32];
const MAX_GRIND: u32 = 4096;

fn canonical_mxfp4_weights() -> (Vec<Vec<i64>>, Vec<u64>) {
    (
        vec![
            vec![2, -1, 4, 3],
            vec![-2, 1, 2, -4],
            vec![6, -3, 1, 2],
        ],
        vec![0, 1, 0],
    )
}

fn canonical_round_inputs_t1() -> Vec<Vec<i64>> {
    vec![
        vec![3, -2, 5, -1],
        vec![4, 1, -2, 6],
        vec![-1, 3, 2, 4],
    ]
}

fn canonical_round_inputs_t4() -> Vec<Vec<i64>> {
    vec![
        vec![2, 5, -3, 1],
        vec![-4, 2, 3, -1],
        vec![1, -2, 4, 3],
    ]
}

fn canonical_weights_root() -> [u8; 32] {
    let (ws, sh) = canonical_mxfp4_weights();
    fpaudit_weights_root(&ws, &sh)
}

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

fn upgraded_floors() -> Vec<SheFloor> {
    let mut fs = canonical_genesis_floors();
    fs.push(SheFloor::SensorRoiRedaction {
        min_redacted_rois: 4,
    });
    fs
}

fn custodian_sk(idx: u8) -> PqSecretKey {
    PqSecretKey {
        sk_seed: [0xA0 + idx; 32],
        sk_prf: [0xB0 + idx; 32],
        pk_seed: [0xC0 + idx; 32],
    }
}

fn simplex_sk(idx: u8) -> PqSecretKey {
    PqSecretKey {
        sk_seed: [0xD0 + idx; 32],
        sk_prf: [0xE0 + idx; 32],
        pk_seed: [0xF0 + idx; 32],
    }
}

fn custodian_pks(params: &PqHashParams) -> Vec<PqPublicKey> {
    (0u8..5)
        .map(|i| derive_pq_public_key(params, &custodian_sk(i)))
        .collect()
}

fn simplex_pks(params: &PqHashParams) -> Vec<PqPublicKey> {
    (0u8..4)
        .map(|i| derive_pq_public_key(params, &simplex_sk(i)))
        .collect()
}

fn genesis_state_with_params(params: PqHashParams) -> SheState {
    let cust = custodian_pks(&params);
    let simp = simplex_pks(&params);
    SheState {
        habitat_judge_digest: [0x10; 32],
        pinned_model_weights_root: canonical_weights_root(),
        pinned_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_small()),
        mono_sensor_seq: 0,
        consumed_nullifiers: Vec::new(),
        remaining_mandate_budget: 100,
        active_safety_and_privacy_floors: canonical_genesis_floors(),
        settled_outbox_actions: Vec::new(),
        pq_params: params,
        custodian_pks: cust,
        simplex_validator_pks: simp,
        consumed_custodian_leaves: Vec::new(),
        consumed_simplex_leaves: Vec::new(),
        custodian_threshold_t: 3,
        custodian_total_n: 5,
        custodian_quorum_epoch: 1,
        revoked_custodians: Vec::new(),
        max_proximity_ticks: 50,
        revert_window_steps: 4,
    }
}

fn canonical_genesis_state() -> SheState {
    genesis_state_with_params(PqHashParams::SHE_STATEFUL_XMSS_256)
}

fn sign_custodians(
    params: &PqHashParams,
    msg: &[u8; 32],
    signers: &[(u64, usize)],
) -> Vec<(u64, PqHashSig)> {
    signers
        .iter()
        .map(|&(idx, leaf)| {
            let sig = eval_pq_single_sign(
                params,
                &custodian_sk(idx as u8),
                msg,
                &OPT_RAND,
                leaf,
                MAX_GRIND,
            )
            .expect("honest custodian PQ signing must succeed");
            (idx, sig)
        })
        .collect()
}

fn sign_simplex(
    params: &PqHashParams,
    msg: &[u8; 32],
    validators: &[(u64, usize)],
) -> Vec<(u64, PqHashSig)> {
    validators
        .iter()
        .map(|&(idx, leaf)| {
            let sig = eval_pq_single_sign(
                params,
                &simplex_sk(idx as u8),
                msg,
                &OPT_RAND,
                leaf,
                MAX_GRIND,
            )
            .expect("honest Simplex validator PQ signing must succeed");
            (idx, sig)
        })
        .collect()
}

fn build_signed_turn_1(st0: &SheState, pow_override: Option<u64>) -> ActuationTurnProposal {
    let payload = b"ACT1".to_vec();
    let floors = canonical_genesis_floors();
    let (ws, sh) = canonical_mxfp4_weights();
    let suite = ZkmlSuiteArtifact::canonical_ud100_small();
    let candidate = build_honest_candidate(
        &suite,
        [0x33; 32],
        she_floors_digest(&floors),
        she_payload_digest(&payload),
        [0x19; 32],
        pow_override,
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert!(verify_candidate_computation(&candidate));
    assert_eq!(proven_zkml_milli_bits(&candidate), 100_022);
    let mut act = ActuationTurnProposal {
        sensor_seq: 1,
        sensor_seal_digest: [0x33; 32],
        candidate,
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
        simplex_qc_signatures: Vec::new(),
        custodian_epoch: 1,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 18,
    };
    let simp_msg = she_simplex_qc_msg(st0, &act);
    let cust_msg = she_custodian_actuation_msg(st0, &act);
    act.simplex_qc_signatures = sign_simplex(&st0.pq_params, &simp_msg, &[(0, 0), (1, 0), (2, 0)]);
    act.custodian_signatures = sign_custodians(&st0.pq_params, &cust_msg, &[(0, 0), (2, 0), (3, 0)]);
    act
}

fn build_signed_turn_2(st1: &SheState) -> UpgradeJudgeProposal {
    let mut up = UpgradeJudgeProposal {
        new_judge_digest: [0x55; 32],
        new_model_weights_root: canonical_weights_root(),
        new_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_wide_leaf()),
        new_floors: upgraded_floors(),
        new_revert_window_steps: 6,
        new_custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 15,
        authority_claim: UpgradeAuthorityClaim::LocalCustodianCeremony,
    };
    let cust_msg = she_custodian_upgrade_msg(st1, &up);
    up.custodian_signatures = sign_custodians(&st1.pq_params, &cust_msg, &[(0, 1), (1, 1), (3, 1)]);
    up
}

fn build_turn_3() -> MandateAttenuation {
    MandateAttenuation {
        new_budget_cap: 50,
        new_max_proximity_ticks: 30,
        newly_revoked_custodians: vec![4],
        reason_digest: [0x66; 32],
    }
}

fn build_signed_turn_4(st3: &SheState) -> ActuationTurnProposal {
    let payload = b"ACT2".to_vec();
    let (ws, sh) = canonical_mxfp4_weights();
    let suite = ZkmlSuiteArtifact::canonical_ud100_wide_leaf();
    let candidate = build_honest_candidate(
        &suite,
        [0x72; 32],
        she_floors_digest(&upgraded_floors()),
        she_payload_digest(&payload),
        [0x29; 32],
        Some(0),
        &canonical_round_inputs_t4(),
        &ws,
        &sh,
    );
    assert!(verify_candidate_computation(&candidate));
    assert_eq!(proven_zkml_milli_bits(&candidate), 100_344);
    let mut act = ActuationTurnProposal {
        sensor_seq: 2,
        sensor_seal_digest: [0x72; 32],
        candidate,
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
        simplex_qc_signatures: Vec::new(),
        custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 22,
    };
    let simp_msg = she_simplex_qc_msg(st3, &act);
    let cust_msg = she_custodian_actuation_msg(st3, &act);
    act.simplex_qc_signatures = sign_simplex(&st3.pq_params, &simp_msg, &[(1, 1), (2, 1), (3, 1)]);
    act.custodian_signatures = sign_custodians(&st3.pq_params, &cust_msg, &[(0, 2), (1, 2), (2, 2)]);
    act
}

const LOCKED_POW_TURN_1: u64 = 8_268;

fn build_4turn_ceremony() -> (
    SheState,
    ActuationTurnProposal,
    UpgradeJudgeProposal,
    MandateAttenuation,
    ActuationTurnProposal,
) {
    let st0 = canonical_genesis_state();
    let t1 = build_signed_turn_1(&st0, Some(LOCKED_POW_TURN_1));
    let st1 = apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(t1.clone()))
        .expect("turn 1 should settle");
    let t2 = build_signed_turn_2(&st1);
    let st2 = apply_she_turn(&st1, &SheTurn::UpgradeHabitatJudge(t2.clone()))
        .expect("turn 2 should upgrade");
    let t3 = build_turn_3();
    let st3 = apply_she_turn(&st2, &SheTurn::RevokeOrAttenuateMandate(t3.clone()))
        .expect("turn 3 should attenuate");
    let t4 = build_signed_turn_4(&st3);
    (st0, t1, t2, t3, t4)
}

#[test]
fn lean_rust_she_turn_wire_vectors_match_byte_for_byte() {
    let (st0, t1, t2, t3, t4) = build_4turn_ceremony();
    assert_eq!(
        hex_encode_lower(&she_floors_digest(&canonical_genesis_floors())),
        "6f6491a661a8e2d178544e84cd4917fda6e6eb451ae9f49c4a211588096c6811"
    );
    assert_eq!(
        hex_encode_lower(&she_payload_digest(b"ACT1")),
        "1839254e8817686d0ea77ebcdf95f57f61b01582ed8ed01dc471c60f2a602d57"
    );
    assert_eq!(t1.candidate.pow_nonce, LOCKED_POW_TURN_1);
    assert_eq!(
        hex_encode_lower(&suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_small())),
        "fb1c5f28ef8774797858dbb4268130ff259c6ae77a8c75b4d2ecdda06ef278a7"
    );
    assert_eq!(
        hex_encode_lower(&suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_wide_leaf())),
        "372ae7d6c020c55d8f2b86cb240771dd07ce5b76ed3515552b79e385fca8e84c"
    );
    assert_eq!(
        hex_encode_lower(&canonical_weights_root()),
        "b254bd4c5833be2e57d92953d8cd6f2e3b7c20297c7cf7875c3430d150e1da51"
    );
    assert_eq!(
        hex_encode_lower(&st0.custodian_pks[0].pk_root),
        "890b7e07b96ce870b8e5e09f91f7f1b2652d9e6024d425d4dd6e9679c61ea854"
    );
    assert_eq!(
        hex_encode_lower(&st0.simplex_validator_pks[0].pk_root),
        "3461a82d0f7fd72aa3bd6f1ce4fb77961d0b0fe0ef8873ee83c5ff4f2fdd8bec"
    );
    assert_eq!(
        hex_encode_lower(&she_state_digest(&st0)),
        "291c9e627a693fa89b6d01041e08eaeda2e4eb50cf43e93828ee0e3365e1b1d6"
    );
    assert_eq!(
        hex_encode_lower(&she_custodian_actuation_msg(&st0, &t1)),
        "42b97c049002fd5fb7525043d22d7d993f9014a79f48f8c770303ce8d8753d89"
    );
    assert_eq!(
        hex_encode_lower(&she_simplex_qc_msg(&st0, &t1)),
        "64219a5a05909884b06f5fdeaaa92de2bb91f9364b7696587ff93a856a137198"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(&SheTurn::ProposeAndSettleActuation(t1))),
        "280faa8cf6ec0297adb3d805b43291770ca4ab2f59ca0e958bafa1fb2fbd47b3"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(&SheTurn::UpgradeHabitatJudge(t2))),
        "2543e5d467c29c5b99cac0900a64ebf0d759fc8623c8a99c2c662ad11cf35ca4"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(&SheTurn::RevokeOrAttenuateMandate(t3))),
        "4703fd475cbe80a9dee00cc86a023b0341874af30ba13a45aa61080a05f159ac"
    );
    assert_eq!(
        hex_encode_lower(&she_turn_envelope_digest(&SheTurn::ProposeAndSettleActuation(t4))),
        "4ab8149d6eac0744b4696844bb2ce0d872ccc5976859911896e982d6bc4770dc"
    );
}

#[test]
fn multi_turn_sovereign_she_ceremony_conserves_budget_and_verifies_pq_and_zkml() {
    let (init, t1, t2, t3, t4) = build_4turn_ceremony();
    assert!(init.well_formed());
    let trace = vec![
        SheTurn::ProposeAndSettleActuation(t1),
        SheTurn::UpgradeHabitatJudge(t2),
        SheTurn::RevokeOrAttenuateMandate(t3),
        SheTurn::ProposeAndSettleActuation(t4),
    ];
    let end = run_she_trace(&init, &trace)
        .expect("valid 4-turn 256-bit PQ + UD-100 + fpaudit ceremony must pass");
    assert_eq!(end.mono_sensor_seq, 2);
    assert_eq!(end.settled_outbox_actions.len(), 2);
    assert_eq!(end.settled_total_cost(), 65);
    assert_eq!(end.remaining_mandate_budget, 10);
    assert!(
        end.settled_total_cost() + end.remaining_mandate_budget <= init.remaining_mandate_budget
    );
    assert_eq!(end.custodian_quorum_epoch, 2);
    assert_eq!(end.max_proximity_ticks, 30);
    assert_eq!(end.consumed_custodian_leaves.len(), 9);
    assert_eq!(end.consumed_simplex_leaves.len(), 6);
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
fn pq_policy_rejects_weak_half_digest_w16_multilayer_and_nonempty_genesis() {
    // 1. Weak 16-bit WOTS+C params (`w=4, ell1=8`) MUST be rejected!
    assert!(!PqHashParams::COMPACT_LEAN_SIG.she_policy_valid());
    assert!(!PqHashParams::COMPACT_GOLDEN.she_policy_valid());
    assert!(!genesis_state_with_params(PqHashParams::COMPACT_LEAN_SIG).well_formed());

    // 2. Half-digest `w=16` (128-bit truncation) AND unpatched multi-layer stateless `num_layers=2`
    //    MUST be rejected by `she_policy_valid` (Astra #8/#9 + Fable H3/M3)!
    let half_digest_w16 = PqHashParams {
        w: 16,
        ell1: 64,
        ..PqHashParams::SHE_STATEFUL_XMSS_256
    };
    assert!(!half_digest_w16.she_policy_valid());
    assert!(!PqHashParams::SHE_STATELESS_SPHINCS_256.she_policy_valid());
    assert!(PqHashParams::SHE_STATEFUL_XMSS_256.she_policy_valid());

    // 3. `run_she_trace` refuses preloaded non-empty genesis history (Astra #14 / Fable L6)!
    let (st0, t1, _, _, _) = build_4turn_ceremony();
    let st1 = apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(t1)).unwrap();
    assert!(!st1.well_formed());
    assert_eq!(run_she_trace(&st1, &[]), Err((0, SheRefusal::MalformedInitialState)));

    // 4. `zigzag_encode(i64::MIN)` never panics in debug builds (Astra #5 / Fable L1)!
    assert_eq!(zigzag_encode(i64::MIN), u64::MAX);
    assert_eq!(zigzag_encode(0), 0);
    assert_eq!(zigzag_encode(-1), 1);
    assert_eq!(zigzag_encode(1), 2);
}

#[test]
fn fpaudit_exact_recompute_catches_steering_commit_after_coin_and_unpinned_suites() {
    let st0 = canonical_genesis_state();
    let t1 = build_signed_turn_1(&st0, None);
    let (ws, sh) = canonical_mxfp4_weights();

    // 1. Exact integer dot product is summation-order invariant (unlike float32 kernels).
    let xs = vec![3, -2, 5, -1];
    let xs_rev: Vec<i64> = xs.iter().copied().rev().collect();
    let w_rev: Vec<i64> = ws[0].iter().copied().rev().collect();
    assert_eq!(exact_int_dot(&xs, &ws[0]), exact_int_dot(&xs_rev, &w_rev));

    // 2. For ANY positive logit tolerance `tau > 0`, tolerance checking admits steered argmaxes
    //    while bit-exact integer recompute (`tau = 0`) unconditionally refuses!
    for tau in [1u64, 2, 5, 22] {
        let actual = vec![tau as i64, (tau as i64) - 1];
        let steered = vec![(tau as i64) - 1, tau as i64];
        assert!(tolerance_logit_check(tau, &actual, &steered));
        assert_ne!(argmax_idx(&actual), argmax_idx(&steered));
        assert_ne!(actual, steered);
    }

    // 3. Steered logit/argmax at the opened round WITH recomputed commit_root, output_root,
    //    statement_digest, AND re-ground PoW -> STILL caught by exact integer recompute!
    let mut steered = t1.clone();
    let rounds = &mut steered.candidate.recompute_audit.committed_rounds;
    for r in rounds.iter_mut() {
        r.claimed_logits[0] += 1;
        r.claimed_argmax = argmax_idx(&r.claimed_logits);
    }
    steered.candidate.recompute_audit.commit_root =
        fpaudit_commit_root(&steered.candidate.recompute_audit.committed_rounds);
    steered.candidate.output_root =
        fpaudit_output_root(&steered.candidate.recompute_audit.committed_rounds);
    steered.candidate.statement_digest = candidate_statement_digest(
        &steered.candidate.suite,
        &steered.candidate.model_weights_root,
        &steered.candidate.input_root,
        &steered.candidate.recompute_audit.commit_root,
        &steered.candidate.output_root,
        steered.candidate.recompute_audit.committed_rounds.len(),
        &steered.candidate.bound_floors_digest,
        &steered.candidate.action_payload_digest,
    );
    let mut reground = 0u64;
    while !has_low_zero_bits(
        &candidate_pow_hash(
            &steered.candidate.statement_digest,
            &steered.candidate.proof_transcript_digest,
            reground,
        ),
        16,
    ) {
        reground += 1;
    }
    steered.candidate.pow_nonce = reground;
    let new_open = fpaudit_opened_round_idx(
        &steered.candidate.statement_digest,
        &steered.candidate.recompute_audit.commit_root,
        &steered.candidate.output_root,
        &steered.candidate.proof_transcript_digest,
        reground,
        steered.candidate.recompute_audit.committed_rounds.len(),
    );
    steered.candidate.recompute_audit.opened_round_idx = new_open;
    steered.candidate.recompute_audit.opened_inputs = canonical_round_inputs_t1()[new_open].clone();
    assert!(!verify_exact_recompute_audit(&steered.candidate));
    assert!(!verify_candidate_computation(&steered.candidate));
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(steered)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    // 4. Commit-after-coin attack: tampering opened_round_idx -> ZkmlProofUnverified!
    let opened = t1.candidate.recompute_audit.opened_round_idx;
    let mut bad_coin = t1.clone();
    bad_coin.candidate.recompute_audit.opened_round_idx =
        (opened + 1) % bad_coin.candidate.recompute_audit.committed_rounds.len();
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(bad_coin)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    // 5a. Unpinned suite substitution (wide-leaf suite when state pins small suite) -> ZkmlSuiteNotPinned!
    let mut unpinned_suite_turn = t1.clone();
    unpinned_suite_turn.candidate = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert!(verify_candidate_computation(&unpinned_suite_turn.candidate));
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(unpinned_suite_turn)),
        Err(SheRefusal::ZkmlSuiteNotPinned)
    );

    // 5b. Unbounded JBR `log_blowup = 200, pinned_num_queries = 1` bypass (Fable H2) -> refused!
    let jbr_bypass_suite = ZkmlSuiteArtifact {
        suite_id: b"obend.jbr.unbounded.blowup".to_vec(),
        regime: ZkmlSoundnessRegime::JohnsonBoundJbr,
        log_blowup: 200,
        log_arity: 1,
        pinned_num_queries: 1,
        pow_bits: 0,
        ext_field_bits: 100,
    };
    assert!(!check_suite_artifact(&jbr_bypass_suite));

    // 5c. Rogue weights (valid E2M1, pinned suite, different weights root) -> ModelWeightsRootMismatch!
    let mut st_wide = st0.clone();
    st_wide.pinned_zkml_suite_digest =
        suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_wide_leaf());
    let mut rogue_ws = ws.clone();
    rogue_ws[0][0] = 4; // still E2M1, different root
    let mut rogue_turn = t1.clone();
    rogue_turn.candidate = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &rogue_ws,
        &sh,
    );
    assert!(verify_candidate_computation(&rogue_turn.candidate));
    assert_eq!(
        apply_she_turn(&st_wide, &SheTurn::ProposeAndSettleActuation(rogue_turn)),
        Err(SheRefusal::ModelWeightsRootMismatch)
    );

    // 6. Non-E2M1 weight mantissa (`5` not in `{0, +-1, +-2, +-3, +-4, +-6, +-8, +-12}`) -> ZkmlProofUnverified!
    let mut bad_e2m1_ws = ws.clone();
    bad_e2m1_ws[0][0] = 5;
    let bad_e2m1 = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &bad_e2m1_ws,
        &sh,
    );
    assert!(!verify_candidate_computation(&bad_e2m1));

    // 7. Out-of-range s8 activation (`128`) -> ZkmlProofUnverified!
    let mut bad_s8_in = canonical_round_inputs_t1();
    bad_s8_in[0][0] = 128;
    bad_s8_in[1][0] = 128;
    bad_s8_in[2][0] = 128;
    let bad_s8 = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &bad_s8_in,
        &ws,
        &sh,
    );
    assert!(!verify_candidate_computation(&bad_s8));

    // 8. Unpinned `observed_num_queries != suite.pinned_num_queries` -> ZkmlProofUnverified!
    let mut bad_q = t1.clone();
    bad_q.candidate.observed_num_queries = 19;
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(bad_q)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    // 9. Unpinned `log_arity = 0` -> ZkmlProofUnverified!
    let mut zero_arity_suite = ZkmlSuiteArtifact::canonical_ud100_wide_leaf();
    zero_arity_suite.log_arity = 0;
    assert!(!check_suite_artifact(&zero_arity_suite));
    let mut zero_arity_turn = t1.clone();
    zero_arity_turn.candidate = build_honest_candidate(
        &zero_arity_suite,
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(zero_arity_turn)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    // 10. Tampered 16-bit post-commit PoW nonce -> ZkmlProofUnverified!
    let mut bad_pow = t1.clone();
    bad_pow.candidate.pow_nonce = bad_pow.candidate.pow_nonce.wrapping_add(1);
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(bad_pow)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    // 10b. Zero-PoW canonical nonce check (`pow_bits == 0` MUST pin `pow_nonce == 0` to prevent free coin re-rolling)!
    let mut noncanonical_zero_pow = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(1),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert!(!verify_candidate_computation(&noncanonical_zero_pow));
    noncanonical_zero_pow.pow_nonce = 0;
    // Changing nonce without recomputing opened_round_idx also fails coin binding.
    let canonical_zero_pow = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert!(verify_candidate_computation(&canonical_zero_pow));

    // 11. Tampered action_payload_digest without re-binding statementDigest -> ZkmlProofUnverified!
    let mut unbound_payload = t1;
    unbound_payload.candidate.action_payload_digest[0] ^= 0xFF;
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(unbound_payload)),
        Err(SheRefusal::ZkmlProofUnverified)
    );
}

#[test]
fn forged_pq_signatures_cross_epoch_replay_and_xmss_leaf_reuse_refused() {
    let (st0, t1, _t2, _t3, _t4) = build_4turn_ceremony();

    // 1. Corrupt 1 byte in custodian 2's 256-bit WOTS+C chain -> InvalidCustodianPqSignature { signer: 2 }!
    let mut bad_cust_sig = t1.clone();
    bad_cust_sig.custodian_signatures[1].1.layer_sigs[0].wots_chains[0][0] ^= 0x01;
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(bad_cust_sig)),
        Err(SheRefusal::InvalidCustodianPqSignature { signer: 2 })
    );

    // 2. Corrupt 1 byte in Simplex validator 1's Merkle auth path -> InvalidSimplexPqSignature { validator: 1 }!
    let mut bad_simp_sig = t1.clone();
    bad_simp_sig.simplex_qc_signatures[1].1.layer_sigs[0].auth_path[0][0] ^= 0x01;
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(bad_simp_sig)),
        Err(SheRefusal::InvalidSimplexPqSignature { validator: 1 })
    );

    // 3. Cross-message replay -> InvalidSimplexPqSignature!
    let mut replayed_sig = t1.clone();
    replayed_sig.nullifier = [0x99; 32];
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(replayed_sig)),
        Err(SheRefusal::InvalidSimplexPqSignature { validator: 0 })
    );

    // 3b. Permuted quorum certificate ordering (Astra #12 malleability) -> DuplicateOrOutOfRangeSigner!
    let mut permuted_cust = t1.clone();
    permuted_cust.custodian_signatures.swap(0, 1);
    assert_eq!(
        apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(permuted_cust)),
        Err(SheRefusal::DuplicateOrOutOfRangeSigner)
    );

    // 3c. Genuine cross-epoch replay: valid Simplex QC on epoch-2 state `st2`, but replaying Turn 1's
    //     epoch-1 custodian signatures -> CustodianEpochMismatch { expected: 2, actual: 1 }!
    let st1 = apply_she_turn(&st0, &SheTurn::ProposeAndSettleActuation(t1.clone())).unwrap();
    let st2 = apply_she_turn(&st1, &SheTurn::UpgradeHabitatJudge(_t2)).unwrap();
    let mut cross_epoch_replay = _t4;
    cross_epoch_replay.custodian_epoch = 1;
    let simp_msg_st2 = she_simplex_qc_msg(&st2, &cross_epoch_replay);
    cross_epoch_replay.simplex_qc_signatures =
        sign_simplex(&st2.pq_params, &simp_msg_st2, &[(1, 1), (2, 1), (3, 1)]);
    cross_epoch_replay.custodian_signatures = t1.custodian_signatures.clone();
    assert_eq!(
        apply_she_turn(&st2, &SheTurn::ProposeAndSettleActuation(cross_epoch_replay)),
        Err(SheRefusal::CustodianEpochMismatch {
            expected: 2,
            actual: 1
        })
    );

    // 4. Reusing stateful XMSS leaf 0 in a subsequent turn -> ReusedStatefulPqLeaf!
    let mut reuse_up = UpgradeJudgeProposal {
        new_judge_digest: [0x55; 32],
        new_model_weights_root: canonical_weights_root(),
        new_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_wide_leaf()),
        new_floors: upgraded_floors(),
        new_revert_window_steps: 6,
        new_custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 15,
        authority_claim: UpgradeAuthorityClaim::LocalCustodianCeremony,
    };
    let msg_up = she_custodian_upgrade_msg(&st1, &reuse_up);
    reuse_up.custodian_signatures =
        sign_custodians(&st1.pq_params, &msg_up, &[(0, 0), (1, 1), (3, 1)]);
    assert!(verify_she_pq_sig(
        &st1.pq_params,
        &st1.custodian_pks[0],
        &msg_up,
        &reuse_up.custodian_signatures[0].1
    ));
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::UpgradeHabitatJudge(reuse_up)),
        Err(SheRefusal::ReusedStatefulPqLeaf {
            signer: 0,
            leaf_idx: 0
        })
    );
}

#[test]
fn vaz_coercive_floor_downgrades_refused_under_vendor_and_agency_signatures() {
    let st = canonical_genesis_state();

    let mut dropped_roi = canonical_genesis_floors();
    dropped_roi.retain(|f| !matches!(f, SheFloor::SensorRoiRedaction { .. }));
    let mut agency_up = UpgradeJudgeProposal {
        new_judge_digest: [0x99; 32],
        new_model_weights_root: canonical_weights_root(),
        new_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_small()),
        new_floors: dropped_roi,
        new_revert_window_steps: 4,
        new_custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 10,
        authority_claim: UpgradeAuthorityClaim::AgencyEmergencyOrder {
            agency_id: b"EXTERNAL_CABAL_VAZ".to_vec(),
            agency_sig: vec![0xAB; 64],
        },
    };
    let msg1 = she_custodian_upgrade_msg(&st, &agency_up);
    agency_up.custodian_signatures = sign_custodians(
        &st.pq_params,
        &msg1,
        &[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)],
    );
    assert_eq!(
        apply_she_turn(&st, &SheTurn::UpgradeHabitatJudge(agency_up)),
        Err(SheRefusal::CoerciveFloorDowngrade {
            dropped_floor: SheFloor::SensorRoiRedaction {
                min_redacted_rois: 2
            }
        })
    );

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
    let mut vendor_up = UpgradeJudgeProposal {
        new_judge_digest: [0x98; 32],
        new_model_weights_root: canonical_weights_root(),
        new_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_small()),
        new_floors: weakened_zkml,
        new_revert_window_steps: 4,
        new_custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 10,
        authority_claim: UpgradeAuthorityClaim::VendorRootDirective {
            vendor_sig: vec![0xCD; 64],
        },
    };
    let msg2 = she_custodian_upgrade_msg(&st, &vendor_up);
    vendor_up.custodian_signatures =
        sign_custodians(&st.pq_params, &msg2, &[(0, 0), (1, 0), (2, 0), (3, 0)]);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::UpgradeHabitatJudge(vendor_up)),
        Err(SheRefusal::CoerciveFloorDowngrade {
            dropped_floor: SheFloor::ZkmlProvenSoundnessMilliBits {
                min_milli_bits: 100_000
            }
        })
    );

    // Even WITHOUT dropping any floor, an external vendor/agency authority claim is refused (Fable L3)!
    let mut external_no_drop = UpgradeJudgeProposal {
        new_judge_digest: [0x97; 32],
        new_model_weights_root: canonical_weights_root(),
        new_zkml_suite_digest: suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_small()),
        new_floors: canonical_genesis_floors(),
        new_revert_window_steps: 4,
        new_custodian_epoch: 2,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 10,
        authority_claim: UpgradeAuthorityClaim::VendorRootDirective {
            vendor_sig: vec![0xEF; 64],
        },
    };
    let msg3 = she_custodian_upgrade_msg(&st, &external_no_drop);
    external_no_drop.custodian_signatures =
        sign_custodians(&st.pq_params, &msg3, &[(0, 0), (1, 0), (2, 0)]);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::UpgradeHabitatJudge(external_no_drop)),
        Err(SheRefusal::ExternalAuthorityRefused)
    );
}

#[test]
fn subthreshold_duplicate_and_revoked_custodian_coalitions_refused() {
    let (st, t1, t2, t3, t4) = build_4turn_ceremony();

    let mut subthreshold = t1.clone();
    subthreshold.custodian_signatures.truncate(2);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(subthreshold)),
        Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: 2,
            required_t: 3
        })
    );

    let mut dup_signers = t1.clone();
    let s0 = dup_signers.custodian_signatures[0].clone();
    dup_signers.custodian_signatures[1] = s0;
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(dup_signers)),
        Err(SheRefusal::DuplicateOrOutOfRangeSigner)
    );

    let st_after_3 = run_she_trace(
        &st,
        &[
            SheTurn::ProposeAndSettleActuation(t1),
            SheTurn::UpgradeHabitatJudge(t2),
            SheTurn::RevokeOrAttenuateMandate(t3),
        ],
    )
    .unwrap();
    let mut with_revoked = t4;
    let msg4 = she_custodian_actuation_msg(&st_after_3, &with_revoked);
    with_revoked.custodian_signatures =
        sign_custodians(&st_after_3.pq_params, &msg4, &[(0, 2), (1, 2), (4, 2)]);
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
    let t1 = build_signed_turn_1(&st, None);
    let (ws, sh) = canonical_mxfp4_weights();

    let mut relay = t1.clone();
    relay.tof_round_trip_ticks = 51;
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(relay)),
        Err(SheRefusal::TofProximityExceeded {
            actual_ticks: 51,
            max_ticks: 50
        })
    );

    let cbr_suite = ZkmlSuiteArtifact {
        suite_id: b"obend.legacy.cbr130.withdrawn".to_vec(),
        regime: ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr,
        log_blowup: 6,
        log_arity: 1,
        pinned_num_queries: 19,
        pow_bits: 16,
        ext_field_bits: 128,
    };
    assert_eq!(legacy_withdrawn_cbr_milli_bits(&cbr_suite), 130_000);
    assert_eq!(suite_proven_milli_bits(&cbr_suite), 0);
    let mut cbr_turn = t1.clone();
    cbr_turn.candidate = build_honest_candidate(
        &cbr_suite,
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(cbr_turn)),
        Err(SheRefusal::WithdrawnCbrRegimeRefused)
    );

    let weak_udr_suite = ZkmlSuiteArtifact {
        suite_id: b"obend.weak.udr34".to_vec(),
        regime: ZkmlSoundnessRegime::UniqueDecodingUdr,
        log_blowup: 6,
        log_arity: 1,
        pinned_num_queries: 19,
        pow_bits: 16,
        ext_field_bits: 128,
    };
    assert_eq!(suite_proven_milli_bits(&weak_udr_suite), 34_563);
    assert!(!check_suite_artifact(&weak_udr_suite));
    let mut weak_udr = t1.clone();
    weak_udr.candidate = build_honest_candidate(
        &weak_udr_suite,
        t1.sensor_seal_digest,
        t1.candidate.bound_floors_digest,
        t1.candidate.action_payload_digest,
        t1.candidate.proof_transcript_digest,
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    assert_eq!(proven_zkml_milli_bits(&weak_udr.candidate), 0);
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(weak_udr)),
        Err(SheRefusal::ZkmlProofUnverified)
    );

    let fake_grind_suite = ZkmlSuiteArtifact {
        suite_id: b"obend.weak.grind16".to_vec(),
        regime: ZkmlSoundnessRegime::UniqueDecodingUdr,
        log_blowup: 1,
        log_arity: 1,
        pinned_num_queries: 1,
        pow_bits: 16,
        ext_field_bits: 128,
    };
    assert_eq!(suite_proven_milli_bits(&fake_grind_suite), 16_415);
    assert!(!check_suite_artifact(&fake_grind_suite));

    let st1 = apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(t1.clone())).unwrap();

    let mut non_monotone_seq = t1.clone();
    non_monotone_seq.sensor_seq = 1;
    non_monotone_seq.nullifier = [0x91; 32];
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::ProposeAndSettleActuation(non_monotone_seq)),
        Err(SheRefusal::NonMonotoneSensorSeq {
            current_seq: 1,
            proposed_seq: 1
        })
    );

    let mut replay = t1.clone();
    replay.sensor_seq = 2;
    assert_eq!(
        apply_she_turn(&st1, &SheTurn::ProposeAndSettleActuation(replay)),
        Err(SheRefusal::NullifierReplayed)
    );

    let mut budget_overrun = t1.clone();
    budget_overrun.sensor_seq = 2;
    budget_overrun.nullifier = [0x92; 32];
    budget_overrun.mandate_cost = 76;
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

    let mut toctou_mismatch = t1.clone();
    toctou_mismatch.dispatched_payload = b"EVIL".to_vec();
    assert_eq!(
        apply_she_turn(&st, &SheTurn::ProposeAndSettleActuation(toctou_mismatch)),
        Err(SheRefusal::PrivateFrameCopyMismatch)
    );

    let mut bad_qc = t1;
    bad_qc.simplex_qc_signatures.truncate(2);
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

    // Duplicate GPU receipt inflation MUST be refused (Astra #15)!
    assert_eq!(
        SealedOracleIngress::from_tlsn_and_tee(
            1,
            &verified_tlsn,
            &cpu_tee,
            &[gpu_tee.clone(), gpu_tee.clone()],
        ),
        Err(SheRefusal::OracleEvidenceBindingMismatch)
    );

    let ingress_1 = SealedOracleIngress::from_tlsn_and_tee(
        1,
        &verified_tlsn,
        &cpu_tee,
        std::slice::from_ref(&gpu_tee),
    )
    .unwrap();
    // Seal digest binds mono_seq + TLSN transcript + CPU TEE + GPU receipts (not raw transcript alone)!
    assert_ne!(ingress_1.seal_digest(), verified_tlsn.transcript_digest());
    let mut st0 = canonical_genesis_state();
    st0.pinned_zkml_suite_digest =
        suite_artifact_digest(&ZkmlSuiteArtifact::canonical_ud100_wide_leaf());
    let payload_1 = b"ACT_TLSN".to_vec();
    let (ws, sh) = canonical_mxfp4_weights();
    let candidate = build_honest_candidate(
        &ZkmlSuiteArtifact::canonical_ud100_wide_leaf(),
        ingress_1.seal_digest(),
        she_floors_digest(&canonical_genesis_floors()),
        she_payload_digest(&payload_1),
        [0x39; 32],
        Some(0),
        &canonical_round_inputs_t1(),
        &ws,
        &sh,
    );
    let mut act1 = ActuationTurnProposal {
        sensor_seq: ingress_1.mono_seq(),
        sensor_seal_digest: ingress_1.seal_digest(),
        candidate,
        nullifier: [0x44; 32],
        mandate_cost: 25,
        redacted_roi_count: 3,
        consent_band_height_px: 40,
        attested_gpu_count: ingress_1.attested_gpu_count(),
        shared_ring_at_copy: payload_1.clone(),
        private_frame_copy: payload_1.clone(),
        dispatched_payload: payload_1,
        simplex_committee_n: 4,
        simplex_faulty_f: 1,
        simplex_qc_signatures: Vec::new(),
        custodian_epoch: 1,
        custodian_signatures: Vec::new(),
        tof_round_trip_ticks: 18,
    };
    let simp_msg = she_simplex_qc_msg(&st0, &act1);
    let cust_msg = she_custodian_actuation_msg(&st0, &act1);
    act1.simplex_qc_signatures = sign_simplex(&st0.pq_params, &simp_msg, &[(0, 0), (1, 0), (2, 0)]);
    act1.custodian_signatures =
        sign_custodians(&st0.pq_params, &cust_msg, &[(0, 0), (2, 0), (3, 0)]);

    let st1 = apply_oracle_attested_actuation(&st0, &ingress_1, &act1).unwrap();
    assert_eq!(st1.settled_outbox_actions.len(), 1);
    assert_eq!(
        st1.settled_outbox_actions[0].sensor_seal_digest,
        ingress_1.seal_digest()
    );

    let ingress_2 =
        SealedOracleIngress::from_verified_e2ee_channel(2, &e2ee_channel, &cpu_tee).unwrap();
    let mut forged_act = act1;
    forged_act.sensor_seq = 2;
    forged_act.nullifier = [0x99; 32];
    assert_eq!(
        apply_oracle_attested_actuation(&st1, &ingress_2, &forged_act),
        Err(SheRefusal::OracleEvidenceBindingMismatch)
    );
}
