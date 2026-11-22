//! Conformance, unconditional soundness-floor gate, byte-exact `OBEND.SHE.ZKML_CHUNK/v1`
//! `cSHAKE256` commitment, and multi-threaded `ProveService` streaming Gated-DeltaNet chunk-carry
//! test suite for *Rainbows End* SHE Gap #4.

use std::time::{Duration, Instant};

use obend_prove_worker::{
    compute_zkml_chunk_commitment, cshake256_32, digest_has_low_zero_bits,
    encode_zkml_chunk_preimage, jbr_query_milli_bits, legacy_cbr_query_milli_bits, sha256,
    spawn_streaming_zkml_service, udr_query_milli_bits, verify_candidate_computation,
    verify_zkml_chunk_chain, CancelToken, ProveServiceConfig, SecurityRegime, StreamingChunkInput,
    StreamingZkmlBackend, StreamingZkmlJob, WaitError, ZkmlGateRefusal, ZkmlSuiteArtifact,
    ZkmlSuiteProfile, BABYBEAR_MODULUS_BITS, PROVEN_MIN_MILLI_BITS, ZKML_CHUNK_DOMAIN_TAG,
};

fn hex32(hex: &str) -> [u8; 32] {
    assert_eq!(hex.len(), 64);
    let mut out = [0u8; 32];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("valid hex byte");
    }
    out
}

fn build_gdn_chunks(initial_state: [u8; 32], count: usize) -> Vec<StreamingChunkInput> {
    let mut chunks = Vec::with_capacity(count);
    let mut state = initial_state;
    for i in 0..count {
        let idx = i as u64;
        let input_commit = sha256(&[b"gdn-input-", &idx.to_be_bytes()[..]].concat());
        let state_out_commit = sha256(&[&state[..], &input_commit[..], b"state"].concat());
        let output_commit = sha256(&[&state_out_commit[..], &input_commit[..], b"out"].concat());
        chunks.push(StreamingChunkInput {
            chunk_idx: idx,
            state_in_commit: state,
            input_commit,
            state_out_commit,
            output_commit,
        });
        state = state_out_commit;
    }
    chunks
}

// ---------------------------------------------------------------------------
// 1. NIST FIPS 202 / SP 800-185 cSHAKE256 Known-Answer & Framing Tests
// ---------------------------------------------------------------------------

#[test]
fn cshake256_matches_nist_sp800_185_vectors() {
    // Empty customization falls back to SHAKE256(empty, 256).
    assert_eq!(
        cshake256_32(b"", b""),
        hex32("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f")
    );
    // SP 800-185 official sample: cSHAKE256(X=00010203, L=256, N="", S="Email Signature").
    assert_eq!(
        cshake256_32(b"Email Signature", &[0x00, 0x01, 0x02, 0x03]),
        hex32("d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1")
    );
    // Domain separation across customization strings.
    assert_ne!(
        cshake256_32(ZKML_CHUNK_DOMAIN_TAG, b"payload"),
        cshake256_32(b"TEST.OTHER.ZKML_CHUNK/v2", b"payload")
    );
}

#[test]
fn zkml_chunk_v1_matches_lean_proven_zkml_gate_golden_vector() {
    // Locked cross-language golden vector shared with `Obend.SymbolicZk.ProvenZkmlGate`:
    //   model_weights_root  = [0x11; 32]
    //   policy_floor_digest = [0x22; 32]
    //   suite_digest        = [0x33; 32]
    //   chunk_idx           = 7
    //   state_in_commit     = [0x44; 32]
    //   input_commit        = [0x55; 32]
    //   state_out_commit    = [0x66; 32]
    //   output_commit       = [0x77; 32]
    //   pow_nonce           = 0x0102_0304_0506_0708
    let weights = [0x11u8; 32];
    let policy = [0x22u8; 32];
    let suite = [0x33u8; 32];
    let s_in = [0x44u8; 32];
    let input = [0x55u8; 32];
    let s_out = [0x66u8; 32];
    let output = [0x77u8; 32];
    let pow_nonce = 0x0102_0304_0506_0708u64;

    let pre = encode_zkml_chunk_preimage(
        &weights, &policy, &suite, 7, &s_in, &input, &s_out, &output, pow_nonce,
    );
    assert_eq!(pre.len(), 249);

    let digest = compute_zkml_chunk_commitment(
        &weights, &policy, &suite, 7, &s_in, &input, &s_out, &output, pow_nonce,
    );
    assert_eq!(
        digest,
        hex32("55ba31a844562b65c394aa34485773e0849871b3e72c639fbfed21823dfb27c1"),
        "Rust OBEND.SHE.ZKML_CHUNK/v1 commitment must match Lean ProvenZkmlGate golden vector byte-for-byte"
    );
}

#[test]
fn zkml_chunk_preimage_framing_is_249_bytes_and_field_injective() {
    let weights = [0x11u8; 32];
    let policy = [0x22u8; 32];
    let suite = [0x33u8; 32];
    let s_in = [0x44u8; 32];
    let input = [0x55u8; 32];
    let s_out = [0x66u8; 32];
    let output = [0x77u8; 32];

    let pre = encode_zkml_chunk_preimage(&weights, &policy, &suite, 7, &s_in, &input, &s_out, &output, 42);
    assert_eq!(pre.len(), 249, "7*(1+32) + 2*(1+8) = 249 bytes");
    assert_eq!(pre[0], 0x20, "LEB128 length prefix for 32-byte field");
    assert_eq!(pre[3 * 33], 0x08, "LEB128 length prefix for 8-byte chunk_idx");
    assert_eq!(pre[240], 0x08, "LEB128 length prefix for 8-byte pow_nonce");

    let base_commit = compute_zkml_chunk_commitment(
        &weights, &policy, &suite, 7, &s_in, &input, &s_out, &output, 42,
    );
    // Flipping any single field must change the commitment.
    let mut w2 = weights;
    w2[0] ^= 1;
    assert_ne!(
        base_commit,
        compute_zkml_chunk_commitment(&w2, &policy, &suite, 7, &s_in, &input, &s_out, &output, 42)
    );
    let mut p2 = policy;
    p2[31] ^= 1;
    assert_ne!(
        base_commit,
        compute_zkml_chunk_commitment(&weights, &p2, &suite, 7, &s_in, &input, &s_out, &output, 42)
    );
    assert_ne!(
        base_commit,
        compute_zkml_chunk_commitment(&weights, &policy, &suite, 8, &s_in, &input, &s_out, &output, 42)
    );
    assert_ne!(
        base_commit,
        compute_zkml_chunk_commitment(&weights, &policy, &suite, 7, &s_in, &input, &s_out, &output, 43)
    );
}

// ---------------------------------------------------------------------------
// 2. Unconditional UDR / JBR vs. Withdrawn CBR Soundness Gate Tests
// ---------------------------------------------------------------------------

#[test]
fn udr_strictly_below_jbr_and_withdrawn_cbr_and_grind_is_additive() {
    for lb in 1u32..=12 {
        assert!(
            udr_query_milli_bits(lb) < jbr_query_milli_bits(lb),
            "UDR must be strictly below JBR at lb={lb}"
        );
        assert!(
            jbr_query_milli_bits(lb) < legacy_cbr_query_milli_bits(lb),
            "JBR must be strictly below withdrawn CBR at lb={lb}"
        );
    }

    // Grind bits are strictly additive (+1000 * g) and regime-free across UDR, JBR, CBR.
    let p0 = ZkmlSuiteProfile {
        field_modulus_bits: BABYBEAR_MODULUS_BITS,
        ext_degree: 4,
        log_blowup: 6,
        num_queries: 19,
        grind_bits: 0,
        log_trace_height: 20,
        digest_bits: 256,
    };
    let p16 = ZkmlSuiteProfile {
        grind_bits: 16,
        ..p0
    };
    assert_eq!(p16.udr_milli_bits() - p0.udr_milli_bits(), 16_000);
    assert_eq!(p16.jbr_milli_bits() - p0.jbr_milli_bits(), 16_000);
    assert_eq!(
        p16.legacy_withdrawn_cbr_milli_bits() - p0.legacy_withdrawn_cbr_milli_bits(),
        16_000
    );
}

#[test]
fn soundness_gate_refuses_legacy_cbr_and_19_query_udr_but_admits_86_query_and_ext5() {
    // 1. Legacy deployed IR-v2 (lb=6, q=19, pow=16) over BabyBear Ext4:
    //    UDR = 19 * 977 + 16_000 = 34_563 (~34.56 bits), JBR = 73_000, CBR = 130_000.
    let legacy = ZkmlSuiteProfile::deployed_ir2_babybear_ext4_legacy();
    assert_eq!(legacy.udr_milli_bits(), 34_563);
    assert_eq!(legacy.jbr_milli_bits(), 73_000);
    assert_eq!(legacy.legacy_withdrawn_cbr_milli_bits(), 130_000);

    // Refused under WithdrawnCapacityBound even though legacy CBR is 130 bits!
    assert_eq!(
        legacy.check_proven_floor(SecurityRegime::WithdrawnCapacityBound),
        Err(ZkmlGateRefusal::WithdrawnCbrRegime {
            legacy_cbr_milli_bits: 130_000,
            udr_milli_bits: 34_563,
        })
    );
    // Refused under ProvenUdr100 (~34.56 < 100 bits).
    assert_eq!(
        legacy.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits {
            regime: SecurityRegime::ProvenUdr100,
            achieved_milli_bits: 34_563,
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        })
    );
    // Refused under ProvenJbr100 (73 < 100 bits).
    assert_eq!(
        legacy.check_proven_floor(SecurityRegime::ProvenJbr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits {
            regime: SecurityRegime::ProvenJbr100,
            achieved_milli_bits: 73_000,
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        })
    );

    // 2. Boundary sharpness: q=85 at (lb=6, pow=16) gives 99_045 < 100_000 (REFUSED),
    //    while q=86 gives 100_022 >= 100_000 (ADMITTED).
    let q85 = ZkmlSuiteProfile {
        num_queries: 85,
        ..ZkmlSuiteProfile::proven_udr100_babybear_ext4()
    };
    assert_eq!(q85.udr_milli_bits(), 99_045);
    assert_eq!(
        q85.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits {
            regime: SecurityRegime::ProvenUdr100,
            achieved_milli_bits: 99_045,
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        })
    );

    let udr_ext4 = ZkmlSuiteProfile::proven_udr100_babybear_ext4();
    let r_ext4 = udr_ext4
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .expect("(lb=6, q=86, pow=16) Ext4 passes ProvenUdr100");
    assert_eq!(r_ext4.udr_milli_bits, 100_022);
    assert_eq!(r_ext4.logup_ext_ceiling_milli_bits, 104_000);
    assert_eq!(r_ext4.bcs_digest_ceiling_milli_bits, 128_000);
    assert_eq!(r_ext4.effective_proven_milli_bits, 100_022);

    // 3. LogUp extension-degree wall: at log_trace_height = 25, Ext4 hits 4*31 - 25 = 99 bits
    //    (REFUSED with LogUpExtensionWall), while Ext5 gives 5*31 - 25 = 130 bits (PASSES!).
    let ext4_tall = ZkmlSuiteProfile {
        log_trace_height: 25,
        ..udr_ext4
    };
    assert_eq!(
        ext4_tall.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::LogUpExtensionWall {
            ext_degree: 4,
            field_modulus_bits: 31,
            log_trace_height: 25,
            realized_milli_bits: 99_000,
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        })
    );

    let ext5_tall = ZkmlSuiteProfile::proven_udr100_babybear_ext5();
    let r_ext5 = ext5_tall
        .check_proven_floor(SecurityRegime::ProvenUdr100)
        .expect("Ext5 clears LogUp wall at log_trace_height=25");
    assert_eq!(r_ext5.logup_ext_ceiling_milli_bits, 130_000);
    assert_eq!(r_ext5.effective_proven_milli_bits, 100_022);

    // 4. BCS digest ceiling wall: 160-bit digest -> 80-bit birthday ceiling (< 100 bits REFUSED).
    let narrow_bcs = ZkmlSuiteProfile {
        digest_bits: 160,
        ..ext5_tall
    };
    assert_eq!(
        narrow_bcs.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits {
            regime: SecurityRegime::ProvenUdr100,
            achieved_milli_bits: 80_000,
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        })
    );

    // 5. JBR-only profile (lb=6, q=28, pow=16) passes ProvenJbr100 (100_000) but fails ProvenUdr100.
    let jbr_only = ZkmlSuiteProfile::proven_jbr100_babybear_ext4();
    assert!(jbr_only.check_proven_floor(SecurityRegime::ProvenJbr100).is_ok());
    assert!(matches!(
        jbr_only.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::InsufficientProvenBits { .. })
    ));
}

// ---------------------------------------------------------------------------
// 3. Multi-Threaded ProveService Streaming GDN Chunk-Carry & 1T == NT Parity
// ---------------------------------------------------------------------------

#[test]
fn streaming_gdn_prove_service_1t_equals_nt_bit_identical_and_verifies_end_to_end() {
    let weights_root = sha256(b"gdn-qwen35-weights-root-v1");
    let policy_floor = sha256(b"obend-she-zkml-udr100-policy-v1");
    let init_state = sha256(b"gdn-initial-recurrent-state-0");
    let request_id = sha256(b"gdn-streaming-req-42");

    // Use a proven UDR-100 Ext5 suite with 10-bit chunk PoW (`93 * 977 + 10_000 = 100_861 >= 100_000`)
    // for rapid multi-thread sweep across 1T, 2T, 4T, 8T.
    let fast_udr100_profile = ZkmlSuiteProfile {
        num_queries: 93,
        grind_bits: 10,
        ..ZkmlSuiteProfile::proven_udr100_babybear_ext5()
    };
    let suite = ZkmlSuiteArtifact::babybear_fri(
        "dregg.ir2.babybear-ext5.poseidon2-w16.fri.udr100.v1",
        fast_udr100_profile,
    );
    let chunks = build_gdn_chunks(init_state, 4);

    let svc = spawn_streaming_zkml_service(
        StreamingZkmlBackend::pinned(weights_root, policy_floor),
        ProveServiceConfig {
            workers: 4,
            queue_depth: 16,
            max_retained_settled: 32,
            settled_ttl: None,
        },
    );

    let mut job_ids = Vec::new();
    for &threads in &[1usize, 2, 4, 8] {
        let job = StreamingZkmlJob {
            request_id,
            model_id: "gdn-ssm-edge-4b".to_string(),
            model_weights_root: weights_root,
            policy_floor_digest: policy_floor,
            suite: suite.clone(),
            requested_regime: SecurityRegime::ProvenUdr100,
            initial_state_commit: init_state,
            chunks: chunks.clone(),
            grind_threads: threads,
            grind_span: 1 << 22,
        };
        job_ids.push((threads, svc.enqueue_with_epoch(1, job).expect("enqueue")));
    }

    let baseline = svc.wait(job_ids[0].1).expect("1T streaming job completes");
    let report = verify_candidate_computation(
        &baseline,
        &request_id,
        &weights_root,
        &policy_floor,
        &suite,
        SecurityRegime::ProvenUdr100,
    )
    .expect("1T CandidateComputation passes fail-closed verifier");
    assert_eq!(report.effective_proven_milli_bits, 100_861);
    assert_eq!(baseline.chunk_receipts.len(), 4);

    // Verify every chunk receipt has minimal pow_nonce (strictly no lower valid nonce exists!).
    for receipt in &baseline.chunk_receipts {
        assert!(digest_has_low_zero_bits(&receipt.chunk_commitment, 10));
        for lower in 0..receipt.pow_nonce {
            let commit = compute_zkml_chunk_commitment(
                &receipt.model_weights_root,
                &receipt.policy_floor_digest,
                &receipt.suite_digest,
                receipt.chunk_idx,
                &receipt.state_in_commit,
                &receipt.input_commit,
                &receipt.state_out_commit,
                &receipt.output_commit,
                lower,
            );
            assert!(
                !digest_has_low_zero_bits(&commit, 10),
                "chunk {}: found lower valid pow_nonce {} < {}",
                receipt.chunk_idx,
                lower,
                receipt.pow_nonce
            );
        }
    }

    // 2T, 4T, 8T MUST be bit-for-bit identical to 1T (including proof_bytes & every pow_nonce).
    for &(threads, id) in &job_ids[1..] {
        let cand = svc.wait(id).expect("NT streaming job completes");
        assert_eq!(
            cand, baseline,
            "CandidateComputation diverged between 1T and {threads}T"
        );
    }
}

#[test]
fn deployed_16bit_pow_86_query_udr100_profile_proves_and_verifies_via_prove_service() {
    let weights_root = sha256(b"gdn-deployed-weights-v1");
    let policy_floor = sha256(b"obend-she-zkml-udr100-16bit-pow");
    let init_state = sha256(b"gdn-state-zero");
    let request_id = sha256(b"gdn-deployed-req-1");
    let suite = ZkmlSuiteArtifact::babybear_fri(
        "dregg.ir2.babybear-ext4.poseidon2-w16.fri.udr100.q86.pow16.v1",
        ZkmlSuiteProfile::proven_udr100_babybear_ext4(),
    );

    let svc = spawn_streaming_zkml_service(
        StreamingZkmlBackend::pinned(weights_root, policy_floor),
        ProveServiceConfig {
            workers: 2,
            queue_depth: 4,
            max_retained_settled: 8,
            settled_ttl: None,
        },
    );

    let chunks = build_gdn_chunks(init_state, 2);
    let j1 = svc
        .enqueue_with_epoch(
            1,
            StreamingZkmlJob {
                request_id,
                model_id: "gdn-deployed".to_string(),
                model_weights_root: weights_root,
                policy_floor_digest: policy_floor,
                suite: suite.clone(),
                requested_regime: SecurityRegime::ProvenUdr100,
                initial_state_commit: init_state,
                chunks: chunks.clone(),
                grind_threads: 1,
                grind_span: 1 << 24,
            },
        )
        .expect("enqueue 1T");
    let j4 = svc
        .enqueue_with_epoch(
            1,
            StreamingZkmlJob {
                request_id,
                model_id: "gdn-deployed".to_string(),
                model_weights_root: weights_root,
                policy_floor_digest: policy_floor,
                suite: suite.clone(),
                requested_regime: SecurityRegime::ProvenUdr100,
                initial_state_commit: init_state,
                chunks,
                grind_threads: 4,
                grind_span: 1 << 24,
            },
        )
        .expect("enqueue 4T");

    let c1 = svc.wait(j1).expect("1T 16-bit job succeeds");
    let c4 = svc.wait(j4).expect("4T 16-bit job succeeds");
    assert_eq!(c1, c4, "16-bit PoW 1T == 4T parity");
    assert_eq!(c1.soundness_report.udr_milli_bits, 100_022);
    verify_candidate_computation(
        &c1,
        &request_id,
        &weights_root,
        &policy_floor,
        &suite,
        SecurityRegime::ProvenUdr100,
    )
    .expect("deployed (lb=6, q=86, pow=16) receipt verifies");
}

// ---------------------------------------------------------------------------
// 4. Adversarial Refusal & Tampering Tests (Fail-Closed Teeth)
// ---------------------------------------------------------------------------

#[test]
fn streaming_backend_and_verifier_refuse_tampered_carry_weights_pow_and_legacy_suite() {
    let weights_root = sha256(b"gdn-weights-pinned");
    let policy_floor = sha256(b"gdn-policy-pinned");
    let init_state = sha256(b"gdn-init-0");
    let request_id = sha256(b"gdn-req-tamper");
    let backend = StreamingZkmlBackend::pinned(weights_root, policy_floor);
    let cancel = CancelToken::new();

    let good_profile = ZkmlSuiteProfile {
        num_queries: 95,
        grind_bits: 8,
        ..ZkmlSuiteProfile::proven_udr100_babybear_ext5()
    };
    let good_suite = ZkmlSuiteArtifact::babybear_fri("gdn-good-udr100", good_profile);
    let good_chunks = build_gdn_chunks(init_state, 3);

    // A. Legacy (lb=6, q=19, pow=16) refused by backend before proving.
    let legacy_job = StreamingZkmlJob {
        request_id,
        model_id: "gdn".to_string(),
        model_weights_root: weights_root,
        policy_floor_digest: policy_floor,
        suite: ZkmlSuiteArtifact::babybear_fri(
            "legacy-19q",
            ZkmlSuiteProfile::deployed_ir2_babybear_ext4_legacy(),
        ),
        requested_regime: SecurityRegime::ProvenUdr100,
        initial_state_commit: init_state,
        chunks: good_chunks.clone(),
        grind_threads: 2,
        grind_span: 1 << 20,
    };
    assert!(matches!(
        backend.prove_job(&legacy_job, &cancel),
        Err(ZkmlGateRefusal::InsufficientProvenBits { .. })
    ));

    // B. WithdrawnCapacityBound refused even on a strong profile.
    let cbr_job = StreamingZkmlJob {
        suite: good_suite.clone(),
        requested_regime: SecurityRegime::WithdrawnCapacityBound,
        ..legacy_job.clone()
    };
    assert!(matches!(
        backend.prove_job(&cbr_job, &cancel),
        Err(ZkmlGateRefusal::WithdrawnCbrRegime { .. })
    ));

    // C. Weight root drift refused by pinned backend.
    let bad_weights_job = StreamingZkmlJob {
        model_weights_root: sha256(b"rogue-weights"),
        suite: good_suite.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        ..legacy_job.clone()
    };
    assert!(matches!(
        backend.prove_job(&bad_weights_job, &cancel),
        Err(ZkmlGateRefusal::WeightRootMismatch { chunk_idx: None, .. })
    ));

    // D. Broken recurrent hidden-state carry refused before grinding.
    let mut broken_chunks = good_chunks.clone();
    broken_chunks[2].state_in_commit[0] ^= 0xff;
    let broken_carry_job = StreamingZkmlJob {
        suite: good_suite.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        chunks: broken_chunks,
        ..legacy_job.clone()
    };
    assert!(matches!(
        backend.prove_job(&broken_carry_job, &cancel),
        Err(ZkmlGateRefusal::BrokenChunkCarry { chunk_idx: 2, .. })
    ));

    // E. Produce an honest CandidateComputation, then mutate receipts and verify fail-closed refusals.
    let honest_job = StreamingZkmlJob {
        suite: good_suite.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        chunks: good_chunks,
        ..legacy_job
    };
    let honest = backend.prove_job(&honest_job, &cancel).expect("honest prove");
    let suite_digest = good_suite.suite_digest();

    // E1. Tampered weights root inside chunk 1 (even with recomputed commitment) -> WeightRootMismatch.
    let mut receipts_bad_w = honest.chunk_receipts.clone();
    receipts_bad_w[1].model_weights_root[0] ^= 1;
    receipts_bad_w[1].chunk_commitment = receipts_bad_w[1].recompute_commitment();
    assert!(matches!(
        verify_zkml_chunk_chain(&receipts_bad_w, &weights_root, &policy_floor, &suite_digest, &init_state, 8),
        Err(ZkmlGateRefusal::WeightRootMismatch { chunk_idx: Some(1), .. })
    ));

    // E2. Tampered hidden state carry between chunk 1 and chunk 2 -> BrokenChunkCarry.
    let mut receipts_bad_carry = honest.chunk_receipts.clone();
    receipts_bad_carry[2].state_in_commit[5] ^= 0x80;
    receipts_bad_carry[2].chunk_commitment = receipts_bad_carry[2].recompute_commitment();
    assert!(matches!(
        verify_zkml_chunk_chain(&receipts_bad_carry, &weights_root, &policy_floor, &suite_digest, &init_state, 8),
        Err(ZkmlGateRefusal::BrokenChunkCarry { chunk_idx: 2, .. })
    ));

    // E3. Tampered PoW nonce (recomputed commitment does not satisfy 8 low zero bits) -> InvalidChunkPow.
    let mut receipts_bad_pow = honest.chunk_receipts.clone();
    // Since pow_nonce is the minimal valid nonce, try pow_nonce + 1 (or search a non-zero-bit nonce).
    let bad_nonce = (0u64..10_000)
        .find(|&n| {
            let mut r = receipts_bad_pow[0].clone();
            r.pow_nonce = n;
            !digest_has_low_zero_bits(&r.recompute_commitment(), 8)
        })
        .expect("non-passing nonce exists");
    receipts_bad_pow[0].pow_nonce = bad_nonce;
    receipts_bad_pow[0].chunk_commitment = receipts_bad_pow[0].recompute_commitment();
    assert!(matches!(
        verify_zkml_chunk_chain(&receipts_bad_pow, &weights_root, &policy_floor, &suite_digest, &init_state, 8),
        Err(ZkmlGateRefusal::InvalidChunkPow { chunk_idx: 0, required_bits: 8, .. })
    ));

    // E4. Truncated proof_bytes -> CandidateBindingMismatch.
    let mut truncated = honest.clone();
    truncated.proof_bytes.pop();
    assert!(matches!(
        verify_candidate_computation(
            &truncated,
            &request_id,
            &weights_root,
            &policy_floor,
            &good_suite,
            SecurityRegime::ProvenUdr100,
        ),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------
// 5. Epoch-Cancellation Behavior on ProveService
// ---------------------------------------------------------------------------

#[test]
fn streaming_zkml_prove_service_cooperatively_cancels_stale_epoch_job() {
    let weights_root = sha256(b"gdn-cancel-weights");
    let policy_floor = sha256(b"gdn-cancel-policy");
    let init_state = sha256(b"gdn-cancel-init");
    let request_id = sha256(b"gdn-cancel-req");

    let svc = spawn_streaming_zkml_service(
        StreamingZkmlBackend::pinned(weights_root, policy_floor),
        ProveServiceConfig {
            workers: 2,
            queue_depth: 8,
            max_retained_settled: 16,
            settled_ttl: None,
        },
    );

    // 28-bit PoW passes UDR-100 (`74 * 977 + 28_000 = 100_298 >= 100_000`) and runs long enough
    // to exercise cooperative in-flight CancelToken termination inside windowed_find_map_first.
    let hard_suite = ZkmlSuiteArtifact::babybear_fri(
        "gdn-hard-28bit",
        ZkmlSuiteProfile {
            num_queries: 74,
            grind_bits: 28,
            ..ZkmlSuiteProfile::proven_udr100_babybear_ext5()
        },
    );

    let hard_job = svc
        .enqueue_with_epoch(
            1,
            StreamingZkmlJob {
                request_id,
                model_id: "gdn-hard".to_string(),
                model_weights_root: weights_root,
                policy_floor_digest: policy_floor,
                suite: hard_suite,
                requested_regime: SecurityRegime::ProvenUdr100,
                initial_state_commit: init_state,
                chunks: build_gdn_chunks(init_state, 2),
                grind_threads: 2,
                grind_span: 1 << 32,
            },
        )
        .expect("enqueue epoch-1 hard job");

    std::thread::sleep(Duration::from_millis(20));
    let t0 = Instant::now();
    let report = svc.cancel_stale_epoch(2);
    assert_eq!(report.min_active_epoch, 2);
    assert_eq!(svc.wait(hard_job), Err(WaitError::Cancelled(hard_job)));
    assert!(
        t0.elapsed() < Duration::from_secs(3),
        "stale-epoch cancellation took too long: {:?}",
        t0.elapsed()
    );

    // Fresh epoch-2 job immediately succeeds on the same ProveService!
    let fast_suite = ZkmlSuiteArtifact::babybear_fri(
        "gdn-fast-8bit",
        ZkmlSuiteProfile {
            num_queries: 95,
            grind_bits: 8,
            ..ZkmlSuiteProfile::proven_udr100_babybear_ext5()
        },
    );
    let fresh_job = svc
        .enqueue_with_epoch(
            2,
            StreamingZkmlJob {
                request_id,
                model_id: "gdn-fresh".to_string(),
                model_weights_root: weights_root,
                policy_floor_digest: policy_floor,
                suite: fast_suite.clone(),
                requested_regime: SecurityRegime::ProvenUdr100,
                initial_state_commit: init_state,
                chunks: build_gdn_chunks(init_state, 3),
                grind_threads: 4,
                grind_span: 1 << 20,
            },
        )
        .expect("enqueue epoch-2 fresh job");

    let fresh = svc.wait(fresh_job).expect("epoch-2 job completes");
    verify_candidate_computation(
        &fresh,
        &request_id,
        &weights_root,
        &policy_floor,
        &fast_suite,
        SecurityRegime::ProvenUdr100,
    )
    .expect("fresh epoch-2 candidate verifies");
}

#[test]
fn streaming_zkml_refuses_policy_suite_index_empty_and_supports_prove_service_dedup() {
    let weights_root = sha256(b"gdn-extra-weights");
    let policy_floor = sha256(b"gdn-extra-policy");
    let init_state = sha256(b"gdn-extra-init");
    let request_id = sha256(b"gdn-extra-req");

    let profile = ZkmlSuiteProfile {
        num_queries: 95,
        grind_bits: 8,
        ..ZkmlSuiteProfile::proven_udr100_babybear_ext5()
    };
    let mut mismatched_artifact = ZkmlSuiteArtifact::babybear_fri("bad-ext", profile);
    mismatched_artifact.ext_degree = 4;
    assert!(matches!(
        mismatched_artifact.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    // Spoofing field_modulus_bits > actual base_field_modulus bit-width (or modulus < 2) must be
    // refused so an attacker cannot bypass LogUpExtensionWall.
    let mut inflated_field_bits = ZkmlSuiteArtifact::babybear_fri("bad-field-bits", profile);
    inflated_field_bits.profile.field_modulus_bits = 64;
    assert!(matches!(
        inflated_field_bits.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));
    let mut tiny_modulus = ZkmlSuiteArtifact::babybear_fri("tiny-modulus", profile);
    tiny_modulus.base_field_modulus = 1;
    tiny_modulus.profile.field_modulus_bits = 1;
    assert!(matches!(
        tiny_modulus.check_proven_floor(SecurityRegime::ProvenUdr100),
        Err(ZkmlGateRefusal::CandidateBindingMismatch { .. })
    ));

    let suite = ZkmlSuiteArtifact::babybear_fri("gdn-dedup-udr100", profile);
    let backend = StreamingZkmlBackend::pinned(weights_root, policy_floor);
    let cancel = CancelToken::new();

    // Empty chunk chain refused.
    let empty_job = StreamingZkmlJob {
        request_id,
        model_id: "gdn".to_string(),
        model_weights_root: weights_root,
        policy_floor_digest: policy_floor,
        suite: suite.clone(),
        requested_regime: SecurityRegime::ProvenUdr100,
        initial_state_commit: init_state,
        chunks: Vec::new(),
        grind_threads: 2,
        grind_span: 1 << 20,
    };
    assert_eq!(
        backend.prove_job(&empty_job, &cancel),
        Err(ZkmlGateRefusal::EmptyChunkChain)
    );

    // Non-contiguous chunk index refused.
    let mut bad_idx_chunks = build_gdn_chunks(init_state, 2);
    bad_idx_chunks[1].chunk_idx = 5;
    let bad_idx_job = StreamingZkmlJob {
        chunks: bad_idx_chunks,
        ..empty_job.clone()
    };
    assert_eq!(
        backend.prove_job(&bad_idx_job, &cancel),
        Err(ZkmlGateRefusal::ChunkIndexMismatch {
            expected: 1,
            actual: 5
        })
    );

    // Policy floor drift refused.
    let bad_policy_job = StreamingZkmlJob {
        policy_floor_digest: sha256(b"rogue-policy"),
        chunks: build_gdn_chunks(init_state, 2),
        ..empty_job.clone()
    };
    assert!(matches!(
        backend.prove_job(&bad_policy_job, &cancel),
        Err(ZkmlGateRefusal::PolicyFloorMismatch { chunk_idx: None, .. })
    ));

    // ProveService 256-bit digest deduplication executes backend once and returns identical receipt.
    let svc = spawn_streaming_zkml_service(
        backend,
        ProveServiceConfig {
            workers: 2,
            queue_depth: 8,
            max_retained_settled: 16,
            settled_ttl: None,
        },
    );
    let good_job = StreamingZkmlJob {
        chunks: build_gdn_chunks(init_state, 3),
        ..empty_job
    };
    let dedup_key = sha256(b"gdn-dedup-job-key-1");
    let first = svc
        .enqueue_dedup(dedup_key, 1, good_job.clone())
        .expect("first enqueue");
    assert!(!first.deduplicated);
    let second = svc
        .enqueue_dedup(dedup_key, 1, good_job)
        .expect("dedup enqueue");
    assert!(second.deduplicated);
    assert_eq!(first.id, second.id);

    let out = svc.wait(first.id).expect("dedup job completes");
    assert_eq!(svc.metrics().completed, 1);
    assert_eq!(svc.metrics().deduplicated, 1);

    // Mutate stored chunk_commitment without updating preimage -> ChunkCommitmentMismatch.
    let mut bad_commit = out.chunk_receipts.clone();
    bad_commit[0].chunk_commitment[0] ^= 0x01;
    assert!(matches!(
        verify_zkml_chunk_chain(
            &bad_commit,
            &weights_root,
            &policy_floor,
            &suite.suite_digest(),
            &init_state,
            8
        ),
        Err(ZkmlGateRefusal::ChunkCommitmentMismatch { chunk_idx: 0, .. })
    ));

    // Mutate suite_digest on receipt -> SuiteDigestMismatch.
    let mut bad_suite = out.chunk_receipts.clone();
    bad_suite[1].suite_digest[0] ^= 0xff;
    assert!(matches!(
        verify_zkml_chunk_chain(
            &bad_suite,
            &weights_root,
            &policy_floor,
            &suite.suite_digest(),
            &init_state,
            8
        ),
        Err(ZkmlGateRefusal::SuiteDigestMismatch { chunk_idx: Some(1), .. })
    ));
}
