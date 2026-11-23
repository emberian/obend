#![forbid(unsafe_code)]

use obend_prove_worker::zkml_gate::{
    cshake256_32, decode_chunk_chain_bytes, digest_has_low_zero_bits, encode_chunk_chain_bytes,
    encode_zkml_chunk_preimage, fold_chunk_roots, grind_zkml_chunk_pow, is_valid_e2m1_mantissa,
    jbr_query_milli_bits, legacy_cbr_query_milli_bits, mxfp4_contract_table, mxfp4_deg_schedule,
    mxfp4_mantissa_root, mxfp4_shift_root, prove_mxfp4_chunk_iop, spawn_streaming_zkml_service,
    udr_query_milli_bits, verify_candidate_computation, verify_mxfp4_chunk_iop,
    verify_zkml_chunk_chain, Goldilocks, Mxfp4ChunkWitness, Mxfp4LayerKey, Mxfp4ModelManifest,
    SecurityRegime, StreamingChunkInput, StreamingZkmlBackend, StreamingZkmlJob, ZkmlGateRefusal,
    ZkmlSuiteArtifact, ZkmlSuiteProfile, GOLDILOCKS_MODULUS_BITS, PROVEN_MIN_MILLI_BITS,
};
use obend_prove_worker::{CancelToken, JobId, ProveServiceConfig, WaitError};

fn hex32(s: &str) -> [u8; 32] {
    assert_eq!(s.len(), 64);
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("valid hex byte");
    }
    out
}

/// Shared 2-layer `MXFP4` (`E2M1` + `2^sh`) test model matching `sampleChainModel` in `EinSumcheckMxfp4.lean`:
/// - Layer 0: `(logI=1, logJ=2, logK=1, logB=1)` (`8` inputs -> `8` outputs)
/// - Layer 1: `(logI=1, logJ=1, logK=1, logB=1)` (`8` inputs -> `4` outputs)
fn sample_chain_model_and_witnesses() -> (Mxfp4ModelManifest, Mxfp4ChunkWitness, Mxfp4ChunkWitness)
{
    let q0: Vec<i64> = vec![1, -2, 3, 4, -6, 8, -12, 2, 2, 1, -3, 6, 4, -1, 8, -4];
    let s0: Vec<u32> = vec![0, 1, 2, 1, 1, 0, 2, 3];
    let q1: Vec<i64> = vec![2, -1, 4, -3, 6, -4, 1, 12];
    let s1: Vec<u32> = vec![1, 0, 1, 2];

    let l0 = Mxfp4LayerKey {
        log_i: 1,
        log_j: 2,
        log_k: 1,
        log_b: 1,
        q_merkle_root: mxfp4_mantissa_root(&q0),
        s_merkle_root: mxfp4_shift_root(&s0),
    };
    let l1 = Mxfp4LayerKey {
        log_i: 1,
        log_j: 1,
        log_k: 1,
        log_b: 1,
        q_merkle_root: mxfp4_mantissa_root(&q1),
        s_merkle_root: mxfp4_shift_root(&s1),
    };
    let model = Mxfp4ModelManifest {
        layers: vec![l0, l1],
    };

    let x0 = vec![
        Goldilocks::new(3),
        Goldilocks::new(5),
        Goldilocks::new(2),
        Goldilocks::new(7),
        Goldilocks::new(4),
        Goldilocks::new(1),
        Goldilocks::new(6),
        Goldilocks::new(2),
    ];
    let w0 = Mxfp4ChunkWitness::build(model.clone(), 0, 1, 2, 1, 1, x0, q0, s0).expect("w0 valid");
    let w1 = Mxfp4ChunkWitness::build(model.clone(), 1, 1, 1, 1, 1, w0.d_tbl().to_vec(), q1, s1)
        .expect("w1 valid");
    (model, w0, w1)
}

#[test]
fn cshake256_matches_nist_sp800_185_vectors() {
    let msg: [u8; 4] = [0x00, 0x01, 0x02, 0x03];
    let out = cshake256_32(b"Email Signature", &msg);
    assert_eq!(
        out,
        hex32("d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1")
    );
}

#[test]
fn udr_strictly_below_jbr_and_withdrawn_cbr_and_ud100_small_vs_wide_leaf() {
    let legacy = ZkmlSuiteProfile::deployed_ir2_babybear_ext4_legacy();
    assert_eq!(legacy.udr_milli_bits(), 34_563);
    assert_eq!(legacy.jbr_milli_bits(), 73_000);
    assert_eq!(legacy.legacy_withdrawn_cbr_milli_bits(), 130_000);
    assert!(legacy.udr_milli_bits() < legacy.jbr_milli_bits());
    assert!(legacy.jbr_milli_bits() < legacy.legacy_withdrawn_cbr_milli_bits());

    // Small-leaf UD-100 `(lb=6, q=86, pow=16)` vs `q=85`:
    let mut q85 = ZkmlSuiteProfile::proven_udr100_babybear_ext4();
    q85.num_queries = 85;
    assert_eq!(q85.udr_milli_bits(), 99_045);
    assert!(q85
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .is_err());
    let q86 = ZkmlSuiteProfile::proven_udr100_babybear_ext4();
    assert_eq!(q86.udr_milli_bits(), 100_022);
    assert!(q86.check_proven_floor(SecurityRegime::ProvenUdr100).is_ok());

    // Wide-leaf UD-100 `(lb=2, q=148, pow=0, log_arity=4)` vs `q=147`:
    let mut wide147 = ZkmlSuiteProfile::wide_leaf_udr100_goldilocks_ext2();
    wide147.num_queries = 147;
    assert_eq!(wide147.udr_milli_bits(), 99_666);
    assert!(wide147
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .is_err());
    let wide148 = ZkmlSuiteProfile::wide_leaf_udr100_goldilocks_ext2();
    assert_eq!(wide148.udr_milli_bits(), 100_344);
    assert!(wide148
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .is_ok());

    // `log_arity == 0` is refused even at >= 100-bit UDR:
    let mut zero_arity = wide148;
    zero_arity.log_arity = 0;
    assert!(matches!(
        zero_arity.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite { .. })
    ));

    // Grinding is additive and regime-free:
    for lb in 1..=8 {
        assert!(udr_query_milli_bits(lb) < jbr_query_milli_bits(lb));
        assert!(jbr_query_milli_bits(lb) < legacy_cbr_query_milli_bits(lb));
    }
    let mut plus4 = q86;
    plus4.grind_bits += 4;
    assert_eq!(plus4.udr_milli_bits() - q86.udr_milli_bits(), 4_000);
    assert_eq!(plus4.jbr_milli_bits() - q86.jbr_milli_bits(), 4_000);
}

#[test]
fn soundness_gate_refuses_legacy_cbr_tall_logup_and_admits_ud100_profiles() {
    let legacy_suite = ZkmlSuiteArtifact::babybear_fri(
        "dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1",
        ZkmlSuiteProfile::deployed_ir2_babybear_ext4_legacy(),
    );
    assert!(matches!(
        legacy_suite.check_proven_floor(SecurityRegime::WithdrawnCapacityBound),
        Err(ZkmlGateRefusal::WithdrawnCbrRegime { .. })
    ));
    assert!(matches!(
        legacy_suite.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits { .. })
    ));

    for bad_height in [21u32, 24u32, 25u32] {
        let mut tall = ZkmlSuiteProfile::proven_udr100_babybear_ext4();
        tall.log_trace_height = bad_height; // (31 - 1)*4 - h < 100 (BabyBear 4*log2(p) = 123.628)!
        let tall_suite = ZkmlSuiteArtifact::babybear_fri("tall-trace-ext4", tall);
        assert!(matches!(
            tall_suite.check_proven_floor(SecurityRegime::ProvenUdr100),
            Err(ZkmlGateRefusal::LogUpExtensionWall { .. })
        ));
    }

    let ext5_suite = ZkmlSuiteArtifact::babybear_fri(
        "tall-trace-ext5",
        ZkmlSuiteProfile::proven_udr100_babybear_ext5(),
    );
    assert!(ext5_suite
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .is_ok());

    let gl_suite = ZkmlSuiteArtifact::goldilocks_einsumcheck_mxfp4(
        "obend.she.goldilocks.mxfp4.v1",
        ZkmlSuiteProfile::proven_udr100_goldilocks_ext2(),
    );
    let rep = gl_suite
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .expect("Goldilocks UD-100 passes");
    assert!(rep.effective_proven_milli_bits >= PROVEN_MIN_MILLI_BITS);
}

#[test]
fn mxfp4_e2m1_contraction_degrees_codecs_and_lean_parity_vectors() {
    // Exact round degree schedule `(2^logB, 3^logK, 3^logJ)` — never degree 4!
    let sched = mxfp4_deg_schedule(5, 3, 2);
    assert_eq!(sched, vec![2, 2, 2, 2, 2, 3, 3, 3, 3, 3]);
    assert!(sched.iter().all(|&d| d == 2 || d == 3));

    for &q in &[-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12] {
        assert!(is_valid_e2m1_mantissa(q));
    }
    for &bad in &[-13, -11, -9, -7, -5, 5, 7, 9, 10, 11, 13, 16] {
        assert!(!is_valid_e2m1_mantissa(bad));
    }

    let (model, w0, w1) = sample_chain_model_and_witnesses();
    assert_eq!(w0.state_out_commit(), w1.state_in_commit());

    // Verify native MXFP4 contraction output of `sampleMxfp4Witness0` (`(1, 1, 1, 1)`):
    let q0_small: Vec<i64> = vec![1, -2, 3, 4, -6, 8, -12, 2];
    let s0_small: Vec<u32> = vec![0, 1, 2, 1];
    let x0_small = w0.x_tbl().to_vec();
    let d_small = mxfp4_contract_table(1, 1, 1, 1, &x0_small, &q0_small, &s0_small);
    // j=0: k=0 (S=1, Q=[1,-2]): i=0 => 1*3 + (-2)*2 = -1; i=1 => 1*5 + (-2)*7 = -9
    //      k=1 (S=2, Q=[3,4]):  i=0 => 2*(3*4 + 4*6) = 72; i=1 => 2*(3*1 + 4*2) = 22
    //   => D[0,0] = 71, D[1,0] = 13
    // j=1: k=0 (S=4, Q=[-6,8]): i=0 => 4*(-6*3 + 8*2) = -8; i=1 => 4*(-6*5 + 8*7) = 104
    //      k=1 (S=2, Q=[-12,2]): i=0 => 2*(-12*4 + 2*6) = -72; i=1 => 2*(-12*1 + 2*2) = -16
    //   => D[0,1] = p - 80, D[1,1] = 88
    assert_eq!(
        d_small,
        vec![
            Goldilocks::new(71),
            Goldilocks::new(13),
            Goldilocks::ZERO.sub(Goldilocks::new(80)),
            Goldilocks::new(88),
        ]
    );

    let policy = [0x22u8; 32];
    let cancel = CancelToken::new();

    let golden_profile = ZkmlSuiteProfile {
        field_modulus_bits: GOLDILOCKS_MODULUS_BITS,
        ext_degree: 2,
        log_blowup: 2,
        num_queries: 2,
        grind_bits: 0,
        log_trace_height: 20,
        digest_bits: 256,
        log_arity: 4,
    };
    let golden_suite_d = golden_profile.profile_digest();
    let c0 = prove_mxfp4_chunk_iop(
        &golden_profile,
        &policy,
        &golden_suite_d,
        0,
        &w0,
        16,
        1,
        &cancel,
    )
    .expect("prove w0");
    let c1 = prove_mxfp4_chunk_iop(
        &golden_profile,
        &policy,
        &golden_suite_d,
        1,
        &w1,
        16,
        1,
        &cancel,
    )
    .expect("prove w1");

    // Round degree invariant: `w0` has `(logB=1, logK=1, logJ=2)` => rounds have coeffs len `[3, 4, 4, 4]`!
    let round_lens_0: Vec<usize> = c0
        .iop_proof
        .sumcheck_rounds
        .iter()
        .map(|r| r.coeffs.len())
        .collect();
    assert_eq!(round_lens_0, vec![3, 4, 4, 4]);
    let round_lens_1: Vec<usize> = c1
        .iop_proof
        .sumcheck_rounds
        .iter()
        .map(|r| r.coeffs.len())
        .collect();
    assert_eq!(round_lens_1, vec![3, 4, 4]);

    verify_mxfp4_chunk_iop(&golden_profile, &model, 0, &c0).expect("c0 verifies");
    verify_mxfp4_chunk_iop(&golden_profile, &model, 0, &c1).expect("c1 verifies");
    // Non-canonical `pow_nonce != 0` when `required_pow_bits == 0` is refused (no free query grinding!):
    let mut rerolled_c0 = c0.clone();
    rerolled_c0.iop_proof.pow_nonce = 1;
    assert!(matches!(
        verify_mxfp4_chunk_iop(&golden_profile, &model, 0, &rerolled_c0),
        Err(ZkmlGateRefusal::InvalidChunkPow {
            chunk_idx: 0,
            required_bits: 0,
            pow_nonce: 1,
        })
    ));

    // Byte-for-byte golden KAT parity with `lean/tests/metasystem/ProvenZkmlGateTest.lean`:
    assert_eq!(
        model.root(),
        hex32("762f45dde0a05eed9cd34395e82a02a6a62308ffe0bdd625485225e0b373eae5")
    );
    assert_eq!(
        c0.state_in_commit,
        hex32("ba697cdee5e9c34eba685d0bed9067e6326a4da6b2d586e645328a42cef8ef1e")
    );
    assert_eq!(
        c0.state_out_commit,
        hex32("9ad1dbd66b7c9169ddc14ceb281d8b754a33345506add4b9533eaf1fcacee467")
    );
    assert_eq!(
        c1.state_out_commit,
        hex32("384c2c6b9d228ec4a7823b3619867d96f22a51cfbbbbbd1851e9b7e35f2d0c3b")
    );
    assert_eq!(c0.iop_proof.encode().len(), 3063);
    assert_eq!(c0.encode_preimage().len(), 3314);
    assert_eq!(
        golden_suite_d,
        hex32("34a5a0f8a1b87b1c386f07b60e44574cf021693c388890d404565d56a3144499")
    );
    assert_eq!(
        c0.chunk_commitment,
        hex32("46f7fb825d329096db84770071f1cadad8900ab87b89476c42a40e310ea5cd58")
    );
    assert_eq!(
        c1.chunk_commitment,
        hex32("514ba9e346519b4f80831bdf63171581100e5c55963c9ef190232627429fecd7")
    );

    // 8-bit PoW 2-chunk chain (`nonces = [145, 289]`) + verify `w - 1` is provably invalid!
    let pow8_profile = ZkmlSuiteProfile {
        field_modulus_bits: GOLDILOCKS_MODULUS_BITS,
        ext_degree: 2,
        log_blowup: 6,
        num_queries: 95,
        grind_bits: 8,
        log_trace_height: 20,
        digest_bits: 256,
        log_arity: 1,
    };
    let pow8_suite_d = pow8_profile.profile_digest();
    assert_eq!(
        pow8_suite_d,
        hex32("0143dab34e24656cc84341a732c5300bf03943afa6b33248b6d2bfc78e7033b1")
    );
    let p0 = prove_mxfp4_chunk_iop(
        &pow8_profile,
        &policy,
        &pow8_suite_d,
        0,
        &w0,
        1 << 16,
        4,
        &cancel,
    )
    .expect("pow8 c0");
    let p1 = prove_mxfp4_chunk_iop(
        &pow8_profile,
        &policy,
        &pow8_suite_d,
        1,
        &w1,
        1 << 16,
        4,
        &cancel,
    )
    .expect("pow8 c1");
    verify_mxfp4_chunk_iop(&pow8_profile, &model, 8, &p0).expect("pow8 c0 verifies");
    verify_mxfp4_chunk_iop(&pow8_profile, &model, 8, &p1).expect("pow8 c1 verifies");
    assert_eq!((p0.iop_proof.pow_nonce, p1.iop_proof.pow_nonce), (145, 289));
    assert_eq!(
        p0.chunk_commitment,
        hex32("f237251918da6520f706e72c8748e5cad6c4c3e3213994984ff81eca78ba0e3e")
    );
    assert_eq!(
        p1.chunk_commitment,
        hex32("73b5c347c45dc42989521240f69c4bfc5f99544aa7b78835d9a89cd92150f774")
    );
    // Verify production `StreamingZkmlBackend::prove_job` emits identical Lean-verifiable chunk commitments:
    let pow8_suite_art =
        ZkmlSuiteArtifact::goldilocks_einsumcheck_mxfp4("obend.she.pow8.mxfp4.v1", pow8_profile);
    let pow8_job = StreamingZkmlJob {
        request_id: [0x33u8; 32],
        model_id: "mxfp4-pow8".to_string(),
        model_weights_root: model.root(),
        policy_floor_digest: policy,
        suite: pow8_suite_art.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        pinned_num_queries: Some(pow8_profile.num_queries),
        initial_state_commit: w0.state_in_commit(),
        chunks: vec![
            StreamingChunkInput::from_witness(0, w0.clone()),
            StreamingChunkInput::from_witness(1, w1.clone()),
        ],
        grind_threads: 4,
        grind_span: 1 << 16,
    };
    let pow8_cand = StreamingZkmlBackend::pinned(model.root(), policy)
        .prove_job(&pow8_job, &cancel)
        .expect("production pow8 prove_job");
    assert_eq!(pow8_cand.chunk_receipts[0], p0);
    assert_eq!(pow8_cand.chunk_receipts[1], p1);
    let mut alt_checker_cand = pow8_cand.clone();
    alt_checker_cand.checker_id = "obend-symbolic-zk-mxfp4-v2".to_string();
    assert_ne!(
        pow8_cand.outer_statement_digest(),
        alt_checker_cand.outer_statement_digest()
    );
    // Exercise `StreamingZkmlJob.grind_threads = 100_000` + lowered worker ceiling `.with_max_grind_threads(2)`:
    let mut pow8_job_100k = pow8_job.clone();
    pow8_job_100k.grind_threads = 100_000;
    let pow8_cand_capped = StreamingZkmlBackend::pinned(model.root(), policy)
        .with_max_grind_threads(2)
        .prove_job(&pow8_job_100k, &cancel)
        .expect("capped 100k-thread job proves cleanly");
    assert_eq!(pow8_cand_capped.proof_bytes, pow8_cand.proof_bytes);
    // Typed receipt with oversized `d_fold_roots` is refused BEFORE `recompute_commitment()` hashes it:
    let mut oversized_c0 = p0.clone();
    oversized_c0.iop_proof.d_fold_roots = vec![[0xAAu8; 32]; 1_024];
    assert!(matches!(
        verify_zkml_chunk_chain(
            &pow8_profile,
            &model,
            &[oversized_c0, p1.clone()],
            &model.root(),
            &policy,
            &pow8_suite_d,
            &w0.state_in_commit(),
            8,
            Some(pow8_profile.num_queries),
        ),
        Err(ZkmlGateRefusal::InvalidChunkIopProof { chunk_idx: 0, .. })
    ));
    verify_candidate_computation(
        &pow8_cand,
        &pow8_job.request_id,
        &pow8_job.initial_state_commit,
        &model,
        &model.root(),
        &policy,
        &pow8_suite_art,
        SecurityRegime::ProvenUdr100,
    )
    .expect("production pow8 candidate verifies");
    for p in [&p0, &p1] {
        let mut pred = p.clone();
        pred.iop_proof.pow_nonce -= 1;
        assert!(matches!(
            verify_mxfp4_chunk_iop(&pow8_profile, &model, 8, &pred),
            Err(ZkmlGateRefusal::InvalidChunkPow { .. })
        ));
    }

    // Codec round-trip + OOM DoS guard on `u64::MAX` count header:
    let chain_bytes = encode_chunk_chain_bytes(&[c0.clone(), c1.clone()]);
    let decoded = decode_chunk_chain_bytes(&chain_bytes).expect("round-trip decode");
    assert_eq!(decoded, vec![c0.clone(), c1]);
    assert!(matches!(
        decode_chunk_chain_bytes(&[0xffu8; 16]),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    let base_pre = encode_zkml_chunk_preimage(
        &c0.model_weights_root,
        &c0.policy_floor_digest,
        &c0.suite_digest,
        c0.chunk_idx,
        c0.layer_idx,
        &c0.state_in_commit,
        &c0.state_out_commit,
        &c0.q_merkle_root,
        &c0.s_merkle_root,
        &c0.iop_proof,
    );
    assert_eq!(base_pre, c0.encode_preimage());
}

#[test]
fn windowed_pow_1t_equals_nt_and_predecessor_is_strictly_invalid() {
    let post_fold_state = cshake256_32(b"ZKML.TEST.POW", b"mxfp4-einsumcheck-state");
    let cancel = CancelToken::new();
    let w_1t = grind_zkml_chunk_pow(&post_fold_state, 9, 12, 1 << 20, 1, &cancel)
        .expect("1T finds 12-bit PoW");
    let w_8t = grind_zkml_chunk_pow(&post_fold_state, 9, 12, 1 << 20, 8, &cancel)
        .expect("8T finds 12-bit PoW");
    let w_16t = grind_zkml_chunk_pow(&post_fold_state, 9, 12, 1 << 20, 16, &cancel)
        .expect("16T finds 12-bit PoW");
    // Service ceiling clamps abusive `grind_threads = 100_000` without OS thread exhaustion while preserving `1T == NT`:
    let w_huge = grind_zkml_chunk_pow(&post_fold_state, 9, 12, 1 << 20, 100_000, &cancel)
        .expect("clamped huge thread request finds identical 12-bit PoW");
    assert_eq!(w_1t, w_8t);
    assert_eq!(w_1t, w_16t);
    assert_eq!(w_1t, w_huge);
    assert!(w_1t > 0);
    // Exhaustively check every `u < w_1t` (including `w_1t - 1`) is invalid via 1-unit span below `w_1t`:
    assert_eq!(
        grind_zkml_chunk_pow(&post_fold_state, 9, 12, w_1t, 4, &cancel),
        None
    );
    // Zero-span PoW returns `None` (exact parity with Lean `grindChunkPowWindowed`):
    assert_eq!(
        grind_zkml_chunk_pow(&post_fold_state, 9, 0, 0, 1, &cancel),
        None
    );
    assert!(digest_has_low_zero_bits(&[0u8; 32], 64));
}

#[test]
fn streaming_mxfp4_prove_service_1t_equals_nt_and_verifies_ud100_profiles() {
    let (model, w0, w1) = sample_chain_model_and_witnesses();
    let policy = [0x44u8; 32];

    // Both wide-leaf `(lb=2, q=148, pow=0, log_arity=4)` and small-leaf `(lb=6, q=86, pow=16)` UD-100:
    for profile in [
        ZkmlSuiteProfile::wide_leaf_udr100_goldilocks_ext2(),
        ZkmlSuiteProfile::proven_udr100_goldilocks_ext2(),
    ] {
        let suite =
            ZkmlSuiteArtifact::goldilocks_einsumcheck_mxfp4("obend.she.ud100.mxfp4.v1", profile);
        let base_job = StreamingZkmlJob {
            request_id: [0x55u8; 32],
            model_id: "mxfp4-2layer".to_string(),
            model_weights_root: model.root(),
            policy_floor_digest: policy,
            suite: suite.clone(),
            requested_regime: SecurityRegime::ProvenUdr100,
            pinned_num_queries: Some(profile.num_queries),
            initial_state_commit: w0.state_in_commit(),
            chunks: vec![
                StreamingChunkInput::from_witness(0, w0.clone()),
                StreamingChunkInput::from_witness(1, w1.clone()),
            ],
            grind_threads: 1,
            grind_span: 1 << 22,
        };

        let backend = StreamingZkmlBackend::pinned(model.root(), policy);
        let cancel = CancelToken::new();
        let cand_1t = backend.prove_job(&base_job, &cancel).expect("1T prove");

        let mut job_8t = base_job.clone();
        job_8t.grind_threads = 8;
        let service = spawn_streaming_zkml_service(
            backend,
            ProveServiceConfig {
                workers: 2,
                queue_depth: 8,
                max_retained_settled: 16,
                settled_ttl: None,
            },
        );
        let outcome = service.enqueue_dedup([0x77; 32], 1, job_8t).unwrap();
        let cand_8t = service.wait(outcome.id).unwrap();
        assert_eq!(cand_1t.proof_bytes, cand_8t.proof_bytes);
        assert_eq!(cand_1t.final_state_commit, w1.state_out_commit());
        assert_eq!(
            cand_1t.canonical_input_root,
            fold_chunk_roots(&[w0.state_in_commit(), w1.state_in_commit()])
        );
        assert_eq!(
            cand_1t.canonical_output_root,
            fold_chunk_roots(&[w0.state_out_commit(), w1.state_out_commit()])
        );

        let report = verify_candidate_computation(
            &cand_8t,
            &base_job.request_id,
            &base_job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        )
        .expect("UD-100 candidate verifies");
        assert!(report.effective_proven_milli_bits >= PROVEN_MIN_MILLI_BITS);
    }
}

#[test]
fn verifier_refuses_degree4_poly_invalid_e2m1_unpinned_queries_jbr_and_tampering() {
    let (model, w0, w1) = sample_chain_model_and_witnesses();
    let policy = [0x44u8; 32];
    let profile = ZkmlSuiteProfile::wide_leaf_udr100_goldilocks_ext2();
    let suite =
        ZkmlSuiteArtifact::goldilocks_einsumcheck_mxfp4("obend.she.wide148.mxfp4.v1", profile);
    let backend = StreamingZkmlBackend::pinned(model.root(), policy);
    let cancel = CancelToken::new();

    let job = StreamingZkmlJob {
        request_id: [0x66u8; 32],
        model_id: "mxfp4-2layer".to_string(),
        model_weights_root: model.root(),
        policy_floor_digest: policy,
        suite: suite.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        pinned_num_queries: Some(profile.num_queries),
        initial_state_commit: w0.state_in_commit(),
        chunks: vec![
            StreamingChunkInput::from_witness(0, w0.clone()),
            StreamingChunkInput::from_witness(1, w1),
        ],
        grind_threads: 2,
        grind_span: 64,
    };
    let cand = backend.prove_job(&job, &cancel).expect("honest prove");

    // 1. Unpinned `pinned_num_queries: None` or mismatched `Some(147)` refused:
    let mut unpinned = cand.clone();
    unpinned.pinned_num_queries = None;
    assert!(matches!(
        verify_candidate_computation(
            &unpinned,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite { .. })
    ));

    // 2. Non-UDR regime (`ProvenJbr100`) refused by live UD-100 candidate gate:
    assert!(matches!(
        verify_candidate_computation(
            &cand,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenJbr100,
        ),
        Err(ZkmlGateRefusal::InsufficientProvenBits { .. })
    ));

    // 3. Degree-3 polynomial injected into a `b`-round (`max_deg = 2`) or degree-4 into `k`-round refused:
    let mut deg3_in_b = cand.clone();
    let r0 = &mut deg3_in_b.chunk_receipts[0];
    r0.iop_proof.sumcheck_rounds[0]
        .coeffs
        .push(Goldilocks::ZERO); // len 4 => deg 3 > 2!
    r0.chunk_commitment = r0.recompute_commitment();
    deg3_in_b.proof_bytes = encode_chunk_chain_bytes(&deg3_in_b.chunk_receipts);
    assert!(matches!(
        verify_candidate_computation(
            &deg3_in_b,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::InvalidChunkIopProof { chunk_idx: 0, .. })
    ));

    let mut deg4_in_k = cand.clone();
    let r0k = &mut deg4_in_k.chunk_receipts[0];
    r0k.iop_proof.sumcheck_rounds[1]
        .coeffs
        .push(Goldilocks::ZERO); // len 5 => deg 4 > 3!
    r0k.chunk_commitment = r0k.recompute_commitment();
    assert!(matches!(
        verify_mxfp4_chunk_iop(&profile, &model, 0, &deg4_in_k.chunk_receipts[0]),
        Err(ZkmlGateRefusal::InvalidChunkIopProof { chunk_idx: 0, .. })
    ));
    deg4_in_k.proof_bytes = encode_chunk_chain_bytes(&deg4_in_k.chunk_receipts);
    // Pre-allocation wire decoder refuses >4 coefficients per round before allocating:
    assert!(matches!(
        verify_candidate_computation(
            &deg4_in_k,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    // 4. Invalid E2M1 mantissa (`5` not in `{0, +-1, +-2, +-3, +-4, +-6, +-8, +-12}`) refused:
    let mut bad_e2m1 = cand.clone();
    let r0q = &mut bad_e2m1.chunk_receipts[0];
    r0q.iop_proof.query_openings[0].q_mantissa = 5;
    r0q.chunk_commitment = r0q.recompute_commitment();
    bad_e2m1.proof_bytes = encode_chunk_chain_bytes(&bad_e2m1.chunk_receipts);
    assert!(matches!(
        verify_candidate_computation(
            &bad_e2m1,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::InvalidChunkIopProof { chunk_idx: 0, .. })
    ));

    // 5. Broken inter-layer activation carry (`chunk 1` `state_in_commit` tampered) refused:
    let mut broken_carry = cand.clone();
    broken_carry.chunk_receipts[1].state_in_commit = [0xeeu8; 32];
    broken_carry.chunk_receipts[1].chunk_commitment =
        broken_carry.chunk_receipts[1].recompute_commitment();
    broken_carry.proof_bytes = encode_chunk_chain_bytes(&broken_carry.chunk_receipts);
    assert!(matches!(
        verify_candidate_computation(
            &broken_carry,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::BrokenChunkCarry { chunk_idx: 1, .. })
    ));

    // 6. Truncated 1-chunk prefix of 2-layer model refused:
    let mut prefix = cand.clone();
    prefix.chunk_receipts.truncate(1);
    prefix.final_state_commit = prefix.chunk_receipts[0].state_out_commit;
    prefix.canonical_input_root = fold_chunk_roots(&[prefix.chunk_receipts[0].state_in_commit]);
    prefix.canonical_output_root = fold_chunk_roots(&[prefix.chunk_receipts[0].state_out_commit]);
    prefix.proof_bytes = encode_chunk_chain_bytes(&prefix.chunk_receipts);
    assert!(matches!(
        verify_candidate_computation(
            &prefix,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    // 7. Out-of-order / repeated `layer_idx` (`layer_idx = 0` at `chunk_idx = 1`) refused:
    let mut bad_layer = cand.clone();
    bad_layer.chunk_receipts[1].layer_idx = 0;
    bad_layer.chunk_receipts[1].chunk_commitment =
        bad_layer.chunk_receipts[1].recompute_commitment();
    bad_layer.proof_bytes = encode_chunk_chain_bytes(&bad_layer.chunk_receipts);
    assert!(matches!(
        verify_candidate_computation(
            &bad_layer,
            &job.request_id,
            &job.initial_state_commit,
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    // 8. Forged `expected_initial_state_commit` refused:
    assert!(matches!(
        verify_candidate_computation(
            &cand,
            &job.request_id,
            &[0xabu8; 32],
            &model,
            &model.root(),
            &policy,
            &suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::BrokenChunkCarry { chunk_idx: 0, .. })
    ));

    // 9. Hypercube dimension cap (`>= 20`) rejected at witness construction:
    assert!(Mxfp4ChunkWitness::build(
        model.clone(),
        0,
        10,
        10,
        1,
        1,
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
    .is_err());
}

#[test]
fn streaming_zkml_prove_service_cooperatively_cancels_stale_epoch_job() {
    let (model, w0, w1) = sample_chain_model_and_witnesses();
    let mut impossible_pow = ZkmlSuiteProfile::proven_udr100_goldilocks_ext2();
    impossible_pow.grind_bits = 48;
    let suite = ZkmlSuiteArtifact::goldilocks_einsumcheck_mxfp4("impossible-pow", impossible_pow);
    let job = StreamingZkmlJob {
        request_id: [0x99u8; 32],
        model_id: "cancel-test".to_string(),
        model_weights_root: model.root(),
        policy_floor_digest: [0x22u8; 32],
        suite,
        requested_regime: SecurityRegime::ProvenUdr100,
        pinned_num_queries: Some(impossible_pow.num_queries),
        initial_state_commit: w0.state_in_commit(),
        chunks: vec![
            StreamingChunkInput::from_witness(0, w0),
            StreamingChunkInput::from_witness(1, w1),
        ],
        grind_threads: 2,
        grind_span: 1 << 30,
    };

    let service = spawn_streaming_zkml_service(
        StreamingZkmlBackend::new(),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 4,
            max_retained_settled: 8,
            settled_ttl: None,
        },
    );
    let outcome = service.enqueue_with_id(JobId(77), 3, job).unwrap();
    let report = service.cancel_stale_epoch(4);
    assert!(report.cancelled_queued + report.marked_in_flight >= 1);
    let status = service.wait(outcome.id);
    assert!(matches!(status, Err(WaitError::Cancelled(JobId(77)))));
}
