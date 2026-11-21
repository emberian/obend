//! Conformance & S11 attack tests for `obend-lightclients`.

use obend_lightclients::{
    compute_fork_digest, compute_ics23_root, cosmos_denom_asset_id, decode_bank_balance_kv,
    period_of_slot, sha256, sha256_pair, verify_comet_header_s11,
    verify_cosmos_bank_balance_envelope, verify_eth_header_s11, CometAdvanceMode, CometGateError,
    CometHeaderUpdate, CometTrustAnchor, EnvelopeError, EthGateError, EthHeaderUpdate,
    EthTrustAnchor, Ics23ExistenceProof, Ics23InnerOp, Ics23LeafOp, Ics23TwoLevelProof,
    BALANCES_PREFIX, BANK_STORE_KEY, COSMOS_CHAIN_TAG, EXECUTION_PAYLOAD_DEPTH,
    EXECUTION_PAYLOAD_SUBTREE_INDEX, FINALIZED_ROOT_DEPTH_ELECTRA, FINALIZED_ROOT_SUBTREE_INDEX,
    SYNC_COMMITTEE_SIZE,
};

fn build_merkle_root(leaf: &[u8; 32], branch: &[[u8; 32]], index: u64) -> [u8; 32] {
    let mut acc = *leaf;
    for (i, sib) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            acc = sha256_pair(sib, &acc);
        } else {
            acc = sha256_pair(&acc, sib);
        }
    }
    acc
}

fn golden_eth_anchor() -> EthTrustAnchor {
    EthTrustAnchor {
        expected_chain_id: 1,
        expected_fork_digest: 0x6A95_A1A9,
        current_period: 1800,
        trusted_attested_slot: 14_745_600,
        trusted_finalized_slot: 14_745_536,
        max_staleness: 3600,
        max_clock_drift: 60,
    }
}

fn golden_eth_electra_397() -> EthHeaderUpdate {
    let finalized_beacon_root = sha256(b"mainnet-period-1800-finalized-beacon-header");
    let finality_branch: Vec<[u8; 32]> = (0..FINALIZED_ROOT_DEPTH_ELECTRA)
        .map(|i| sha256(&[0xF0, i as u8]))
        .collect();
    let attested_state_root = build_merkle_root(
        &finalized_beacon_root,
        &finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
    );
    let execution_payload_root = sha256(b"mainnet-period-1800-exec-payload-header");
    let execution_branch: Vec<[u8; 32]> = (0..EXECUTION_PAYLOAD_DEPTH)
        .map(|i| sha256(&[0xE0, i as u8]))
        .collect();
    let finalized_body_root = build_merkle_root(
        &execution_payload_root,
        &execution_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
    );
    EthHeaderUpdate {
        chain_id: 1,
        fork_digest: 0x6A95_A1A9,
        attested_slot: 14_745_664,
        signature_slot: 14_745_665,
        finalized_slot: 14_745_600,
        attested_time: 1_780_000_000,
        committee_len: SYNC_COMMITTEE_SIZE,
        bits_len: SYNC_COMMITTEE_SIZE,
        participant_count: 397,
        bls_agg_ok: true,
        attested_state_root,
        finalized_beacon_root,
        finality_branch,
        finalized_body_root,
        execution_payload_root,
        execution_branch,
        execution_state_root: sha256(b"mainnet-period-1800-evm-state-root"),
    }
}

#[test]
fn eth_electra_s11_golden_and_attacks() {
    let anchor = golden_eth_anchor();
    let u = golden_eth_electra_397();
    let now = 1_780_000_120;

    assert_eq!(period_of_slot(u.signature_slot), 1800);
    let v = verify_eth_header_s11(&anchor, &u, now).expect("397/512 Electra accepts");
    assert_eq!(v.chain_id(), 1);
    assert_eq!(v.finalized_slot(), 14_745_600);

    let mut u_342 = u.clone();
    u_342.participant_count = 342;
    assert!(verify_eth_header_s11(&anchor, &u_342, now).is_ok());

    let mut u_341 = u.clone();
    u_341.participant_count = 341;
    assert_eq!(
        verify_eth_header_s11(&anchor, &u_341, now),
        Err(EthGateError::InsufficientParticipation)
    );

    let mut cross = u.clone();
    cross.chain_id = 11_155_111;
    assert_eq!(
        verify_eth_header_s11(&anchor, &cross, now),
        Err(EthGateError::ChainIdMismatch)
    );

    let mut future_slot = u.clone();
    future_slot.signature_slot = future_slot.attested_slot - 1;
    assert_eq!(
        verify_eth_header_s11(&anchor, &future_slot, now),
        Err(EthGateError::FutureSlotSpoof)
    );

    assert_eq!(
        verify_eth_header_s11(&anchor, &u, u.attested_time + anchor.max_staleness + 1),
        Err(EthGateError::StaleHeader)
    );

    let gvr = sha256(b"gvr");
    assert_ne!(
        compute_fork_digest(1, [5, 0, 0, 0], &gvr),
        compute_fork_digest(11_155_111, [5, 0, 0, 0], &gvr)
    );
}

#[test]
fn comet_s11_and_two_level_ics23_sealed_holding() {
    let addr = [0x42u8; 20];
    let mut key = vec![BALANCES_PREFIX, 20];
    key.extend_from_slice(&addr);
    key.extend_from_slice(b"uatom");

    let sub_proof = Ics23ExistenceProof {
        key,
        value: b"331305561223899".to_vec(),
        leaf: Ics23LeafOp {
            prefix: vec![0x00, 0x02, 0x02],
            prehash_value: true,
        },
        path: vec![Ics23InnerOp {
            prefix: vec![0x02, 0x04, 0x20],
            suffix: sha256(b"sib-0").to_vec(),
        }],
    };
    let store_root = compute_ics23_root(&sub_proof);
    let root_proof = Ics23ExistenceProof {
        key: BANK_STORE_KEY.to_vec(),
        value: store_root.to_vec(),
        leaf: Ics23LeafOp {
            prefix: vec![0x00],
            prehash_value: true,
        },
        path: vec![Ics23InnerOp {
            prefix: vec![0x01, 0x20],
            suffix: sha256(b"ms-0").to_vec(),
        }],
    };
    let app_hash = compute_ics23_root(&root_proof);
    let proof = Ics23TwoLevelProof {
        store_key: BANK_STORE_KEY.to_vec(),
        store_root,
        sub_proof,
        root_proof,
    };

    let anchor = CometTrustAnchor {
        expected_chain_id: "cosmoshub-4".into(),
        expected_fork_digest: 0xC054_0504,
        trusted_height: 26_000_000,
        trusted_header_time: 1_780_000_000,
        trusting_period: 1_209_600,
        max_staleness: 3600,
        max_clock_drift: 60,
    };
    let skip = CometHeaderUpdate {
        chain_id: "cosmoshub-4".into(),
        fork_digest: 0xC054_0504,
        height: 26_000_095,
        header_time: 1_780_000_570,
        app_hash,
        epoch_bind_ok: false,
        self_bind_ok: true,
        commit_matches_header: true,
        total_power: 300,
        signed_power: 240,
        trusted_total_power: 300,
        trusted_signed_power: 101,
    };

    let verified = verify_comet_header_s11(&anchor, &skip, 1_780_000_600).expect("skip accepts");
    assert_eq!(verified.mode(), CometAdvanceMode::Skipping);

    let holding = verify_cosmos_bank_balance_envelope(&verified, &proof).expect("holding mints");
    assert_eq!(holding.chain_tag(), COSMOS_CHAIN_TAG);
    assert_eq!(holding.chain_id(), "cosmoshub-4");
    assert_eq!(holding.amount(), 331_305_561_223_899);
    assert_eq!(holding.asset(), cosmos_denom_asset_id("uatom"));
    assert!(holding.consensus_proven());

    // Attacks: cross-chain, expired trust period, exact 2/3, zero-overlap skip, supply key
    let mut cross = skip.clone();
    cross.chain_id = "theta-testnet-001".into();
    assert_eq!(
        verify_comet_header_s11(&anchor, &cross, 1_780_000_600),
        Err(CometGateError::ChainIdMismatch)
    );
    assert_eq!(
        verify_comet_header_s11(
            &anchor,
            &skip,
            anchor.trusted_header_time + anchor.trusting_period
        ),
        Err(CometGateError::TrustedStateExpired)
    );
    let mut exact_2_3 = skip.clone();
    exact_2_3.signed_power = 200;
    assert_eq!(
        verify_comet_header_s11(&anchor, &exact_2_3, 1_780_000_600),
        Err(CometGateError::InsufficientVotingPower)
    );
    let mut zero_ov = skip;
    zero_ov.trusted_signed_power = 0;
    assert_eq!(
        verify_comet_header_s11(&anchor, &zero_ov, 1_780_000_600),
        Err(CometGateError::InsufficientTrustOverlap)
    );
    assert_eq!(
        decode_bank_balance_kv(BANK_STORE_KEY, &[0x00, 5, b'u', b'a', b't', b'o', b'm'], b"10"),
        Err(EnvelopeError::NotBalanceKey)
    );
}
