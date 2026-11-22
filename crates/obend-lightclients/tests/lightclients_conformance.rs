#![forbid(unsafe_code)]
//! Conformance, Mainnet KAT, & S11 adversarial tests for `obend-lightclients`:
//! - Real BLS12-381 `SyncAggregate` (`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`) over a full
//!   512-validator sync committee pinned by SSZ `SyncCommittee::hash_tree_root` and bound to
//!   exact Ethereum Consensus-Spec `(attested_header, DOMAIN_SYNC_COMMITTEE, fork_version, gvr)`.
//! - Real Ethereum Mainnet post-Electra (`fulu`) `BeaconBlockHeader` + 17-field
//!   `ExecutionPayloadHeader` + `finality_branch` + `execution_branch` KAT.
//! - RFC 9380 `hash_to_g2` & Ethereum `fast_aggregate_verify` KATs + forged-signature,
//!   non-subgroup, identity, rogue-cancellation, unpinned-committee, and state-root-swap refusals.
//! - Real Mainnet `cosmoshub-4` height `31989761` `Header::Hash()` (`merkle.HashFromByteSlices`
//!   over 14 Protobuf fields) + Protobuf `CanonicalVote` Ed25519 validator signature KAT.
//! - Real RFC 8032 Ed25519 `verify_strict` CometBFT validator-quorum verification (`Adjacent` and
//!   `Skipping` modes) + two-level ICS-23 `IavlSpec` / `TendermintSpec` `ProvenForeignHolding`.

use std::sync::OnceLock;

use obend_lightclients::bls12_381::{
    self, fast_aggregate_verify_bytes, fixture_aggregate_signatures, fixture_sign,
    fixture_sk_to_pk, g1_from_compressed, g2_from_compressed, hash_to_g2, key_validate, BlsError,
    G1Affine, G2Affine, DST_POP,
};
use obend_lightclients::{
    compute_comet_block_id_hash, compute_eth_signing_root, compute_fork_digest,
    compute_ics23_root, compute_sync_committee_root, compute_validator_set_hash,
    cosmos_denom_asset_id, decode_bank_balance_kv, ed25519, encode_canonical_precommit_vote,
    is_valid_merkle_branch, period_of_slot, sha256, sha256_pair, verify_comet_header_s11,
    verify_cosmos_bank_balance_envelope, verify_eth_header_s11, BeaconBlockHeader,
    CometAdvanceMode, CometBlockId, CometCommitSig, CometGateError, CometHeader,
    CometHeaderUpdate, CometTrustAnchor, CometValidator, EnvelopeError, EthGateError,
    EthHeaderUpdate, EthTrustAnchor, ExecutionPayloadHeader, Ics23ExistenceProof, Ics23InnerOp,
    Ics23LeafOp, Ics23TwoLevelProof, BALANCES_PREFIX, BANK_STORE_KEY, COSMOS_CHAIN_TAG,
    EXECUTION_PAYLOAD_DEPTH, EXECUTION_PAYLOAD_SUBTREE_INDEX, FINALIZED_ROOT_DEPTH_ELECTRA,
    FINALIZED_ROOT_SUBTREE_INDEX, SECONDS_PER_SLOT, SYNC_COMMITTEE_BITS_BYTES, SYNC_COMMITTEE_SIZE,
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

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn h32(s: &str) -> [u8; 32] {
    unhex(s).try_into().unwrap()
}

fn h20(s: &str) -> [u8; 20] {
    unhex(s).try_into().unwrap()
}

struct SyncCommitteeFixture {
    sks: Vec<[u8; 32]>,
    pks: Vec<[u8; 48]>,
    root: [u8; 32],
}

fn committee_512() -> &'static SyncCommitteeFixture {
    static FIX: OnceLock<SyncCommitteeFixture> = OnceLock::new();
    FIX.get_or_init(|| {
        let sks: Vec<[u8; 32]> = (0..SYNC_COMMITTEE_SIZE)
            .map(|i| {
                let mut seed = b"eth-sync-committee-test-seed/v1".to_vec();
                seed.extend_from_slice(&(i as u32).to_be_bytes());
                sha256(&seed)
            })
            .collect();
        let pks: Vec<[u8; 48]> = sks.iter().map(fixture_sk_to_pk).collect();
        let root = compute_sync_committee_root(&pks).expect("valid 512-key SyncCommittee");
        SyncCommitteeFixture { sks, pks, root }
    })
}

fn sign_sync_aggregate(signing_root: &[u8; 32], participant_count: usize) -> ([u8; 64], [u8; 96]) {
    let c = committee_512();
    let mut bits = [0u8; SYNC_COMMITTEE_BITS_BYTES];
    let mut sigs = Vec::with_capacity(participant_count);
    for i in 0..participant_count {
        bits[i / 8] |= 1u8 << (i % 8);
        sigs.push(fixture_sign(&c.sks[i], signing_root));
    }
    let agg_sig = if sigs.is_empty() {
        G2Affine::generator().to_compressed()
    } else {
        fixture_aggregate_signatures(&sigs)
    };
    (bits, agg_sig)
}

const ELECTRA_FORK_VERSION: [u8; 4] = [0x05, 0x00, 0x00, 0x00];

fn golden_gvr() -> [u8; 32] {
    h32("4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95")
}

fn golden_eth_anchor() -> EthTrustAnchor {
    let gvr = golden_gvr();
    let fork_digest = compute_fork_digest(ELECTRA_FORK_VERSION, &gvr);
    EthTrustAnchor {
        expected_chain_id: 1,
        fork_version: ELECTRA_FORK_VERSION,
        genesis_validators_root: gvr,
        expected_fork_digest: fork_digest,
        genesis_time: 1_780_000_000 - 14_745_664 * SECONDS_PER_SLOT,
        current_period: 1800,
        trusted_sync_committee_root: committee_512().root,
        trusted_attested_slot: 14_745_600,
        trusted_finalized_slot: 14_745_536,
        max_staleness: 3600,
        max_clock_drift: 60,
    }
}

fn golden_eth_electra(participant_count: usize) -> EthHeaderUpdate {
    let c = committee_512();
    let gvr = golden_gvr();
    let fork_digest = compute_fork_digest(ELECTRA_FORK_VERSION, &gvr);

    let execution_payload_header = ExecutionPayloadHeader {
        parent_hash: sha256(b"exec-parent-hash"),
        fee_recipient: [0x11; 20],
        state_root: sha256(b"mainnet-period-1800-evm-state-root"),
        receipts_root: sha256(b"exec-receipts-root"),
        logs_bloom: [0u8; 256],
        prev_randao: sha256(b"exec-prev-randao"),
        block_number: 22_000_000,
        gas_limit: 36_000_000,
        gas_used: 18_000_000,
        timestamp: 1_779_999_988,
        extra_data: b"electra".to_vec(),
        base_fee_per_gas: [0x01; 32],
        block_hash: sha256(b"mainnet-period-1800-exec-block-hash"),
        transactions_root: sha256(b"exec-tx-root"),
        withdrawals_root: sha256(b"exec-withdrawals-root"),
        blob_gas_used: 131_072,
        excess_blob_gas: 0,
    };
    let execution_payload_root = execution_payload_header.hash_tree_root().unwrap();
    let execution_branch: Vec<[u8; 32]> = (0..EXECUTION_PAYLOAD_DEPTH)
        .map(|i| sha256(&[0xE0, i as u8]))
        .collect();
    let finalized_body_root = build_merkle_root(
        &execution_payload_root,
        &execution_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
    );
    let finalized_header = BeaconBlockHeader {
        slot: 14_745_600,
        proposer_index: 42,
        parent_root: sha256(b"finalized-parent"),
        state_root: sha256(b"finalized-beacon-state-root"),
        body_root: finalized_body_root,
    };
    let finalized_beacon_root = finalized_header.hash_tree_root();
    let finality_branch: Vec<[u8; 32]> = (0..FINALIZED_ROOT_DEPTH_ELECTRA)
        .map(|i| sha256(&[0xF0, i as u8]))
        .collect();
    let attested_state_root = build_merkle_root(
        &finalized_beacon_root,
        &finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
    );
    let attested_header = BeaconBlockHeader {
        slot: 14_745_664,
        proposer_index: 99,
        parent_root: sha256(b"attested-parent"),
        state_root: attested_state_root,
        body_root: sha256(b"attested-body"),
    };
    let signing_root = compute_eth_signing_root(&attested_header, ELECTRA_FORK_VERSION, &gvr);
    let (sync_committee_bits, sync_aggregate_signature) =
        sign_sync_aggregate(&signing_root, participant_count);

    EthHeaderUpdate {
        chain_id: 1,
        fork_digest,
        attested_header,
        signature_slot: 14_745_665,
        attested_time: 1_780_000_000,
        sync_committee_pubkeys: c.pks.clone(),
        sync_committee_bits,
        signing_root,
        sync_aggregate_signature,
        finalized_header,
        finality_branch,
        execution_payload_header,
        execution_branch,
    }
}

#[test]
fn eth_mainnet_post_electra_ssz_finality_and_execution_kat() {
    // Real Ethereum Mainnet post-Electra (`fulu`) beacon `light_client/finality_update`
    // (slot 14,749,306 -> finalized slot 14,749,216 -> execution block 25,512,833).
    // Validates exact Consensus-Spec `BeaconBlockHeader::hash_tree_root`, 17-field
    // `ExecutionPayloadHeader::hash_tree_root`, depth-7 `finality_branch`, and depth-4 `execution_branch`.
    let mainnet_gvr = h32("4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95");
    // Known Ethereum Mainnet Deneb ForkDigest (`fork_version = 0x04000000` -> `0x6a95a1a9`).
    assert_eq!(
        compute_fork_digest([0x04, 0x00, 0x00, 0x00], &mainnet_gvr),
        [0x6a, 0x95, 0xa1, 0xa9]
    );

    let attested_state_root =
        h32("169384fde580fa8a71df6f31c0e14e056c1e3f3f2dcacf7fb8218a6bcc64d1bf");
    let fin_beacon = BeaconBlockHeader {
        slot: 14_749_216,
        proposer_index: 797_812,
        parent_root: h32("9f5cc4f188c21fb76c9f4ba450b368469ccf717e10773adf6747db0f6b988022"),
        state_root: h32("5de754cc369692b4e9a6d1990a452b9eef07a16b362de717bf47a1890255a2ed"),
        body_root: h32("a42d0e7c4700ffb08b52a003ee65c11f8f7ca87eab9325745fc8727e64608d90"),
    };
    let finality_branch = [
        h32("7108070000000000000000000000000000000000000000000000000000000000"),
        h32("106b2759d67d19a09efbddd029afef8618ea739a0b7ae2b33826d78c0755b867"),
        h32("750ca07658c35fcd8c92c3487f3fac2a9146399369d12157252255020deb0584"),
        h32("7fddfaa6e8175bc74feb5ac97cf7f3f1c17a2f5c930f92f738d687df7cfd02f4"),
        h32("a360f6fd8d0eb71aa27203cc6b0ca654f74b61336977dd3b7cdaff6deb546872"),
        h32("8ecfbf67c4707509a84de6b249032f3fd7b0d67538dcffe8e53e4a532af78a1a"),
        h32("815c47cbb9ad933d24bdf2db508ff33badfad0094a39e1017af2b6f1fea71799"),
    ];
    assert!(is_valid_merkle_branch(
        &fin_beacon.hash_tree_root(),
        &finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
        &attested_state_root,
    ));

    let logs_bloom: [u8; 256] = unhex("ad65506bf9967fff6e4defeea9d2dfa15f5d7d1fd5b956f6ef79f7bd7e57bfbfd89ffecff37af5ab879effc1edced5e4dfb9d77dbf7fafef5f99bff5fefd7dbe76bfbe7bd8fdeaef7bfddde8ffedf6fc52eeb6ff7f7e1fb65bfb7f3be3edf7c7bf7d8e73ff6cb5eb7fd4f9fdadd5cfdffbf749ffd8bef7bf578e5aff381ebeda337dbcda3f3c5ffd7eff566ba72e5fbf6384fdffffdfcfcf7bcc6f75fffed9fad6c6ed77fad67eb3fbf7bbfedd5f37c8efd3fcff04bc44da57ff6a33fede7c7764be5f7f43cffa7a75ffbe27d7fbb30957bf7dda5ffd36b655bff3fadff77edb5fdcb7c7fbf799fb1f79affadfeb1d52ed7fffbbdf3f84d65ffbf976ffebe797").try_into().unwrap();
    let exec = ExecutionPayloadHeader {
        parent_hash: h32("11b448b1b8e05ddfbe3747756fb7741e75b45879811d34966e56bc5ec3b6c01b"),
        fee_recipient: h20("dadb0d80178819f2319190d340ce9a924f783711"),
        state_root: h32("5e7354b2096400d76b30ebb80753aec8dd275763fc186480152e7a1f2eeb054d"),
        receipts_root: h32("651e41785b1df29be5395fbd312f13209a5119f91a8353e396c2373b168efd71"),
        logs_bloom,
        prev_randao: h32("106657a49e27cc42c6cc3366ff813c76fa7e0eb0ef35483be2e4549d9ac0c85e"),
        block_number: 25_512_833,
        gas_limit: 60_000_000,
        gas_used: 52_161_058,
        timestamp: 1_783_814_615,
        extra_data: unhex("4275696c6465724e6574"),
        base_fee_per_gas: h32("43e85e0700000000000000000000000000000000000000000000000000000000"),
        block_hash: h32("60105537fc77d9d2a3aaa5304de109bfd975a31943cad560a4e7e34f72464c51"),
        transactions_root: h32("0d68121074548acea5bcee3c14828d88384ae41948c84151269b769fd0d2acc4"),
        withdrawals_root: h32("ecf269eb9e6bc6472efad1657b49be5b7f087b3fc015cbbe3fec6310822b33d5"),
        blob_gas_used: 393_216,
        excess_blob_gas: 184_985_647,
    };
    let exec_branch = [
        h32("3ecfd8cb63b54450410304cfc75b2fc58901b078521b8b8110d3ce968772f306"),
        h32("bad9c658e495b1c9e35f5901a1f4603495195b3f71690de647e65525276b11eb"),
        h32("6dd3b9955d892d92338b19976fd07084bfe88a76c3063482b7f30ee60feb2a58"),
        h32("2ae0602805a8e78d1512723dcecdf13c05d8ea5d905e6f401b1cd102bb60b0fb"),
    ];
    assert!(is_valid_merkle_branch(
        &exec.hash_tree_root().unwrap(),
        &exec_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
        &fin_beacon.body_root,
    ));
}

#[test]
fn eth_electra_s11_real_bls_sync_aggregate_and_attacks() {
    let anchor = golden_eth_anchor();
    let u = golden_eth_electra(397);
    let now = 1_780_000_120;

    assert_eq!(period_of_slot(u.signature_slot), 1800);
    let v = verify_eth_header_s11(&anchor, &u, now).expect("real 397/512 BLS SyncAggregate accepts");
    assert_eq!(v.chain_id(), 1);
    assert_eq!(v.finalized_slot(), 14_745_600);
    assert_eq!(
        v.execution_state_root(),
        sha256(b"mainnet-period-1800-evm-state-root")
    );

    // Exact 2/3 threshold boundary: 342/512 passes, 341/512 fails.
    let u_342 = golden_eth_electra(342);
    assert!(verify_eth_header_s11(&anchor, &u_342, now).is_ok());

    let u_341 = golden_eth_electra(341);
    assert_eq!(
        verify_eth_header_s11(&anchor, &u_341, now),
        Err(EthGateError::InsufficientParticipation)
    );

    // Zero participants refused.
    let mut u_zero = u.clone();
    u_zero.sync_committee_bits = [0u8; SYNC_COMMITTEE_BITS_BYTES];
    assert_eq!(
        verify_eth_header_s11(&anchor, &u_zero, now),
        Err(EthGateError::ZeroParticipants)
    );

    // ATTACK 1: 1-bit tamper in BLS aggregate signature refused.
    let mut bad_sig = u.clone();
    bad_sig.sync_aggregate_signature[40] ^= 0x01;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_sig, now),
        Err(EthGateError::BadBlsSignature)
    );

    // ATTACK 2: Signature by 396 signers when bitfield claims 397 signers refused.
    let mut wrong_subset = u.clone();
    let (_, sig_396) = sign_sync_aggregate(&u.signing_root, 396);
    wrong_subset.sync_aggregate_signature = sig_396;
    assert_eq!(
        verify_eth_header_s11(&anchor, &wrong_subset, now),
        Err(EthGateError::BadBlsSignature)
    );

    // ATTACK 3: Attacker swaps `attested_header.state_root` while keeping valid `signing_root` + sig!
    let mut swapped_header = u.clone();
    swapped_header.attested_header.state_root[0] ^= 0xFF;
    assert_eq!(
        verify_eth_header_s11(&anchor, &swapped_header, now),
        Err(EthGateError::SigningRootMismatch)
    );

    // ATTACK 4: Attacker supplies their own 512 BLS keypairs (valid signature, unpinned committee)!
    let rogue_sk = sha256(b"rogue-sync-committee-key");
    let rogue_pk = fixture_sk_to_pk(&rogue_sk);
    let mut rogue_committee = u.clone();
    rogue_committee.sync_committee_pubkeys[0] = rogue_pk;
    assert_eq!(
        verify_eth_header_s11(&anchor, &rogue_committee, now),
        Err(EthGateError::SyncCommitteeRootMismatch)
    );

    // ATTACK 5: Attacker mutates `execution_payload_header.state_root` without updating body_root!
    let mut swapped_evm = u.clone();
    swapped_evm.execution_payload_header.state_root[0] ^= 0xAA;
    assert_eq!(
        verify_eth_header_s11(&anchor, &swapped_evm, now),
        Err(EthGateError::BadExecutionBranch)
    );

    // S11 temporal / domain checks preserved.
    let mut cross = u.clone();
    cross.chain_id = 11_155_111;
    assert_eq!(
        verify_eth_header_s11(&anchor, &cross, now),
        Err(EthGateError::ChainIdMismatch)
    );

    let mut future_slot = u.clone();
    future_slot.signature_slot = future_slot.attested_header.slot - 1;
    assert_eq!(
        verify_eth_header_s11(&anchor, &future_slot, now),
        Err(EthGateError::FutureSlotSpoof)
    );

    // Strict Altair..Electra `signature_slot > attested_header.slot` check.
    let mut eq_slot = u.clone();
    eq_slot.signature_slot = eq_slot.attested_header.slot;
    assert_eq!(
        verify_eth_header_s11(&anchor, &eq_slot, now),
        Err(EthGateError::FutureSlotSpoof)
    );

    // Spoofed `attested_time` differing from `genesis_time + attested_slot * 12` refused!
    let mut spoofed_time = u.clone();
    spoofed_time.attested_time += SECONDS_PER_SLOT;
    assert_eq!(
        verify_eth_header_s11(&anchor, &spoofed_time, now),
        Err(EthGateError::AttestedTimeMismatch)
    );

    // Future `signature_slot` beyond `host_now + max_clock_drift` refused!
    let mut future_sig_slot = u.clone();
    future_sig_slot.signature_slot = u.attested_header.slot + 20;
    assert_eq!(
        verify_eth_header_s11(&anchor, &future_sig_slot, u.attested_time),
        Err(EthGateError::FutureTimestampSpoof)
    );

    assert_eq!(
        verify_eth_header_s11(&anchor, &u, u.attested_time + anchor.max_staleness + 1),
        Err(EthGateError::StaleHeader)
    );
    assert_eq!(
        verify_eth_header_s11(&anchor, &u, 0),
        Err(EthGateError::InvalidClock)
    );

    let sepolia_gvr = h32("d8ea171f3c94aea21ebc42a1ed61052acf3f9209c00e4efbaaddac09ed9b8078");
    assert_ne!(
        compute_fork_digest([5, 0, 0, 0], &golden_gvr()),
        compute_fork_digest([5, 0, 0, 0], &sepolia_gvr)
    );
}

#[test]
fn bls12_381_rfc9380_ethereum_kat_and_rogue_subgroup_refusals() {
    // Official Ethereum `bls12-381-tests` v0.1.2 `fast_aggregate_verify_valid_3d7576f3c0e3570a` KAT (3 validators).
    let pk1: [u8; 48] = unhex("a491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a").try_into().unwrap();
    let pk2: [u8; 48] = unhex("b301803f8b5ac4a1133581fc676dfedc60d891dd5fa99028805e5ea5b08d3491af75d0707adab3b70c6a6a580217bf81").try_into().unwrap();
    let pk3: [u8; 48] = unhex("b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f").try_into().unwrap();
    let msg = unhex("abababababababababababababababababababababababababababababababab");
    let sig: [u8; 96] = unhex(
        "9712c3edd73a209c742b8250759db12549b3eaf43b5ca61376d9f30e2747dbcf842d8b2ac0901d2a093713e20284a76\
         70fcf6954e9ab93de991bb9b313e664785a075fc285806fa5224c82bde146561b446ccfc706a64b8579513cfc4ff1d930",
    )
    .try_into()
    .unwrap();
    assert!(fast_aggregate_verify_bytes(&[pk1, pk2, pk3], &msg, &sig));
    assert!(!fast_aggregate_verify_bytes(&[pk1, pk2], &msg, &sig));
    assert!(!fast_aggregate_verify_bytes(&[], &msg, &sig));

    // Identity G1 key (`0xc0 || 0^47`) and identity G2 signature (`0xc0 || 0^95`) refused.
    let mut inf_g1 = [0u8; 48];
    inf_g1[0] = 0xc0;
    assert_eq!(key_validate(&inf_g1), Err(BlsError::IdentityPublicKey));
    assert!(!fast_aggregate_verify_bytes(&[pk1, inf_g1], &msg, &sig));

    let mut inf_g2 = [0u8; 96];
    inf_g2[0] = 0xc0;
    assert!(g2_from_compressed(&inf_g2).unwrap().is_identity());
    assert!(!fast_aggregate_verify_bytes(&[pk1, pk2, pk3], &msg, &inf_g2));

    // Official Ethereum `deserialization_fails_not_in_G1` & `deserialization_fails_not_in_G2` vectors.
    let non_subgroup_g1: [u8; 48] = unhex(
        "8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    )
    .try_into()
    .unwrap();
    assert_eq!(
        g1_from_compressed(&non_subgroup_g1),
        Err(BlsError::NotInSubgroup)
    );
    let non_subgroup_g2: [u8; 96] = unhex(
        "8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\
         0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    )
    .try_into()
    .unwrap();
    assert_eq!(
        g2_from_compressed(&non_subgroup_g2),
        Err(BlsError::NotInSubgroup)
    );
    assert!(!fast_aggregate_verify_bytes(&[pk1, pk2, pk3], &msg, &non_subgroup_g2));

    // Rogue-key cancellation (`PK` paired with `-PK` so `agg_pk == O`) refused.
    let g1 = G1Affine::generator();
    let mut neg_g1_bytes = g1.to_compressed();
    neg_g1_bytes[0] ^= 0x20;
    let neg_g1 = key_validate(&neg_g1_bytes).unwrap();
    let h = hash_to_g2(b"rogue-cancel", DST_POP);
    assert!(!h.is_identity());
    assert!(!bls12_381::fast_aggregate_verify(
        &[g1, neg_g1],
        b"rogue-cancel",
        &sig
    ));
}

#[test]
fn cosmoshub_4_mainnet_height_31989761_header_and_ed25519_vote_kat() {
    // Genuine Mainnet `cosmoshub-4` block 31,989,761 header & validator[0] Precommit signature!
    // Proves exact wire compatibility with CometBFT `Header::Hash()` (RFC 6962 `merkle.HashFromByteSlices`
    // over 14 Protobuf fields) and Protobuf length-delimited `CanonicalVote`.
    let hdr = CometHeader {
        version_block: 11,
        version_app: 0,
        chain_id: "cosmoshub-4".to_string(),
        height: 31_989_761,
        header_time_secs: 1_783_815_254,
        header_time_nanos: 896_417_755,
        last_block_id: CometBlockId::parts(
            h32("f4c1e1aba516b4bf76eac5653a87283e91b68d28f9454a0248dd3d4df084ee07"),
            1,
            h32("c5c25af1d8b16a14112a101ec1f3684b8c49010b6448b27fe94ea3fe2aa57a5a"),
        ),
        last_commit_hash: unhex("a147d9d2d13266c526558862f6f7be91570f794f662f12210c00ea790b2d2871"),
        data_hash: unhex("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        validators_hash: h32("76cc8f2f5536f372a50b2d705b0d23e91c2068df11972389bcc50ba2b5e4a3ac"),
        next_validators_hash: h32("76cc8f2f5536f372a50b2d705b0d23e91c2068df11972389bcc50ba2b5e4a3ac"),
        consensus_hash: h32("20ca5e3f42e07a0cdb7bd986eff1947a23fc27ff47204303e082bc44bb348e0b"),
        app_hash: h32("9dd53e05c32bba32d5f0c0d16fe4384dcdaca28be4d6e372818c0e9b54dbe37f"),
        last_results_hash: unhex("6c47cc6495fedefffa1df1c7ce451426e1db91e8fec6773f0d69767ce2fde60c"),
        evidence_hash: unhex("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        proposer_address: h20("56b2f053ad136642d3fc9098fb2dd01454f396d5"),
    };
    let expected_block_hash =
        h32("36511a7b86ad0807a303d1c295a93f171007ee17157d0fe148f54a5cd8e67a6c");
    assert_eq!(compute_comet_block_id_hash(&hdr), expected_block_hash);

    let commit_bid = CometBlockId::parts(
        expected_block_hash,
        1,
        h32("5e63e43b2dc289c4430ebd9613281c8ef6947cbf4ce11f0edca0cd7adaaa6b38"),
    );
    let vote_bytes = encode_canonical_precommit_vote(
        "cosmoshub-4",
        31_989_761,
        0,
        &commit_bid,
        1_783_815_260,
        736_805_749,
    );
    let val0_pk = h32("925acb357c71717c75bf446f7a58fd6448daacff065ef78e4454a51899700103");
    let sig0: [u8; 64] = unhex("5bb99a99e378851e7fc939d22d23a6e23d183cd287f21c375d609d3aadf623f804c46d0b694610b8180bc4566e4abc4f04410cec213d28a168d832a7733e030e")
        .try_into()
        .unwrap();
    assert!(ed25519::verify_strict(&val0_pk, &vote_bytes, &sig0));
}

fn make_comet_validators(tag: &[u8], powers: &[u64]) -> (Vec<[u8; 32]>, Vec<CometValidator>, [u8; 32]) {
    let mut seeds = Vec::with_capacity(powers.len());
    let mut vals = Vec::with_capacity(powers.len());
    for (i, &power) in powers.iter().enumerate() {
        let mut s = tag.to_vec();
        s.extend_from_slice(&(i as u32).to_be_bytes());
        let seed = sha256(&s);
        let pubkey = ed25519::fixture_public_key(&seed);
        seeds.push(seed);
        vals.push(CometValidator {
            pubkey,
            voting_power: power,
        });
    }
    let hash = compute_validator_set_hash(&vals).expect("valid validator set");
    (seeds, vals, hash)
}

fn sign_comet_commit(
    seeds: &[[u8; 32]],
    signer_indices: &[usize],
    header: &CometHeader,
    round: u32,
) -> (CometBlockId, Vec<CometCommitSig>) {
    let block_id_hash = compute_comet_block_id_hash(header);
    let block_id = CometBlockId::parts(block_id_hash, 1, sha256(&block_id_hash));
    let sigs = signer_indices
        .iter()
        .map(|&idx| {
            let ts_secs = header.header_time_secs;
            let ts_nanos = (idx as u32) + 1;
            let vote_bytes = encode_canonical_precommit_vote(
                &header.chain_id,
                header.height,
                round,
                &block_id,
                ts_secs,
                ts_nanos,
            );
            CometCommitSig {
                validator_index: idx,
                timestamp_secs: ts_secs,
                timestamp_nanos: ts_nanos,
                signature: ed25519::fixture_sign(&seeds[idx], &vote_bytes),
            }
        })
        .collect();
    (block_id, sigs)
}

#[test]
fn comet_s11_real_ed25519_quorum_and_two_level_ics23_sealed_holding() {
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

    // Trusted validator set (4 validators, total power = 300: [101, 67, 66, 66]).
    let (trusted_seeds, trusted_vals, trusted_vals_hash) =
        make_comet_validators(b"comet-epoch-1", &[101, 67, 66, 66]);
    // Skipping target validator set shares validator 0 (101/300 > 1/3 trusted overlap!) + 3 new validators:
    let (new_seeds, mut new_vals, _) = make_comet_validators(b"comet-epoch-2", &[101, 70, 70, 59]);
    new_vals[0] = trusted_vals[0].clone();
    let mut skip_seeds = new_seeds;
    skip_seeds[0] = trusted_seeds[0];
    let skip_vals_hash = compute_validator_set_hash(&new_vals).unwrap();
    let next_vals_hash = sha256(b"comet-epoch-3-next");
    let proposer = [0x11u8; 20];

    let anchor = CometTrustAnchor {
        expected_chain_id: "cosmoshub-4".into(),
        trusted_height: 26_000_000,
        trusted_header_time: 1_780_000_000,
        trusted_next_validators: trusted_vals.clone(),
        trusted_next_validators_hash: trusted_vals_hash,
        trusting_period: 1_209_600,
        max_staleness: 3600,
        max_clock_drift: 60,
    };

    // 1. Adjacent advance (height = 26_000_001) signed by [0, 1, 2] -> 234/300 > 2/3.
    let adj_header = CometHeader::new_standard(
        "cosmoshub-4",
        26_000_001,
        1_780_000_006,
        trusted_vals_hash,
        skip_vals_hash,
        app_hash,
        proposer,
    );
    let (adj_bid, adj_sigs) = sign_comet_commit(&trusted_seeds, &[0, 1, 2], &adj_header, 0);
    let adj_update = CometHeaderUpdate {
        header: adj_header,
        commit_round: 0,
        commit_block_id: adj_bid,
        validators: trusted_vals,
        commit_sigs: adj_sigs,
    };
    let adj_verified =
        verify_comet_header_s11(&anchor, &adj_update, 1_780_000_010).expect("adjacent accepts");
    assert_eq!(adj_verified.mode(), CometAdvanceMode::Adjacent);

    // 2. Skipping advance (height = 26_000_095) signed by [0, 1, 2] -> 241/300 > 2/3 & 101/300 > 1/3!
    let skip_header = CometHeader::new_standard(
        "cosmoshub-4",
        26_000_095,
        1_780_000_570,
        skip_vals_hash,
        next_vals_hash,
        app_hash,
        proposer,
    );
    let (skip_bid, skip_sigs) = sign_comet_commit(&skip_seeds, &[0, 1, 2], &skip_header, 1);
    let skip = CometHeaderUpdate {
        header: skip_header.clone(),
        commit_round: 1,
        commit_block_id: skip_bid,
        validators: new_vals,
        commit_sigs: skip_sigs,
    };

    let verified = verify_comet_header_s11(&anchor, &skip, 1_780_000_600).expect("skip accepts");
    assert_eq!(verified.mode(), CometAdvanceMode::Skipping);

    let holding = verify_cosmos_bank_balance_envelope(&verified, &proof).expect("holding mints");
    assert_eq!(holding.chain_tag(), COSMOS_CHAIN_TAG);
    assert_eq!(holding.chain_id(), "cosmoshub-4");
    assert_eq!(holding.holder_len(), 20);
    assert_eq!(holding.holder_bytes(), &addr);
    assert_eq!(holding.snapshot_height(), 26_000_095);
    assert_eq!(holding.app_state_height(), 26_000_094);
    assert_eq!(holding.amount(), 331_305_561_223_899);
    assert_eq!(holding.asset(), cosmos_denom_asset_id("uatom"));
    assert!(holding.consensus_proven());

    // ICS-23 `ProofSpec` domain-separation refusals (`InvalidProofSpec`):
    let mut forged_inner_as_leaf = proof.clone();
    forged_inner_as_leaf.sub_proof.leaf.prefix = vec![0x02, 0x04, 0x20];
    assert_eq!(
        verify_cosmos_bank_balance_envelope(&verified, &forged_inner_as_leaf),
        Err(EnvelopeError::InvalidProofSpec)
    );
    let mut forged_no_prehash = proof.clone();
    forged_no_prehash.sub_proof.leaf.prehash_value = false;
    assert_eq!(
        verify_cosmos_bank_balance_envelope(&verified, &forged_no_prehash),
        Err(EnvelopeError::InvalidProofSpec)
    );
    let mut forged_leaf_as_inner = proof.clone();
    forged_leaf_as_inner.sub_proof.path[0].prefix = vec![0x00, 0x02, 0x02];
    assert_eq!(
        verify_cosmos_bank_balance_envelope(&verified, &forged_leaf_as_inner),
        Err(EnvelopeError::InvalidProofSpec)
    );
    let mut forged_tm_leaf = proof.clone();
    forged_tm_leaf.root_proof.leaf.prefix = vec![0x01];
    assert_eq!(
        verify_cosmos_bank_balance_envelope(&verified, &forged_tm_leaf),
        Err(EnvelopeError::InvalidProofSpec)
    );

    // ATTACK 1: 1-byte forged Ed25519 signature refused.
    let mut bad_sig = skip.clone();
    bad_sig.commit_sigs[1].signature[10] ^= 0x01;
    assert_eq!(
        verify_comet_header_s11(&anchor, &bad_sig, 1_780_000_600),
        Err(CometGateError::InvalidValidatorSignature { validator_index: 1 })
    );

    // ATTACK 2: Duplicate validator index padding (`[0, 0, 1]`) refused!
    let mut dup_sig = skip.clone();
    dup_sig.commit_sigs[2] = dup_sig.commit_sigs[0].clone();
    assert_eq!(
        verify_comet_header_s11(&anchor, &dup_sig, 1_780_000_600),
        Err(CometGateError::DuplicateValidatorSignature { validator_index: 0 })
    );

    // ATTACK 3: Exact 2/3 power (`200/300`) refused (strict `> 2/3` required).
    let (eq_seeds, eq_vals, eq_hash) = make_comet_validators(b"exact-2-3", &[101, 99, 100]);
    let mut eq_anchor = anchor.clone();
    eq_anchor.trusted_next_validators = eq_vals.clone();
    eq_anchor.trusted_next_validators_hash = eq_hash;
    let eq_hdr = CometHeader::new_standard(
        "cosmoshub-4",
        26_000_001,
        1_780_000_010,
        eq_hash,
        eq_hash,
        app_hash,
        proposer,
    );
    let (eq_bid, eq_sigs) = sign_comet_commit(&eq_seeds, &[0, 1], &eq_hdr, 0);
    assert_eq!(
        verify_comet_header_s11(
            &eq_anchor,
            &CometHeaderUpdate {
                header: eq_hdr,
                commit_round: 0,
                commit_block_id: eq_bid,
                validators: eq_vals,
                commit_sigs: eq_sigs,
            },
            1_780_000_020,
        ),
        Err(CometGateError::InsufficientVotingPower)
    );

    // ATTACK 4: Skipping without `> 1/3` trusted overlap refused!
    let (ov_seeds, mut ov_vals, _) = make_comet_validators(b"zero-overlap", &[50, 90, 90, 70]);
    ov_vals[0].pubkey = anchor.trusted_next_validators[0].pubkey;
    let ov_hash = compute_validator_set_hash(&ov_vals).unwrap();
    let ov_hdr = CometHeader {
        validators_hash: ov_hash,
        ..skip_header.clone()
    };
    let (ov_bid, ov_sigs) = sign_comet_commit(&ov_seeds, &[1, 2, 3], &ov_hdr, 0);
    assert_eq!(
        verify_comet_header_s11(
            &anchor,
            &CometHeaderUpdate {
                header: ov_hdr,
                commit_round: 0,
                commit_block_id: ov_bid,
                validators: ov_vals,
                commit_sigs: ov_sigs,
            },
            1_780_000_600,
        ),
        Err(CometGateError::InsufficientTrustOverlap)
    );

    // ATTACK 5: Byzantine untrusted power inflation on a single compromised small trusted validator!
    let (inf_seeds, mut inf_vals, _) = make_comet_validators(b"inflate-attack", &[900, 100]);
    inf_vals[0].pubkey = anchor.trusted_next_validators[3].pubkey;
    let mut inf_sign_seeds = inf_seeds;
    inf_sign_seeds[0] = trusted_seeds[3];
    let inf_hash = compute_validator_set_hash(&inf_vals).unwrap();
    let inf_hdr = CometHeader {
        validators_hash: inf_hash,
        ..skip_header
    };
    let (inf_bid, inf_sigs) = sign_comet_commit(&inf_sign_seeds, &[0], &inf_hdr, 0);
    assert_eq!(
        verify_comet_header_s11(
            &anchor,
            &CometHeaderUpdate {
                header: inf_hdr,
                commit_round: 0,
                commit_block_id: inf_bid,
                validators: inf_vals,
                commit_sigs: inf_sigs,
            },
            1_780_000_600,
        ),
        Err(CometGateError::InsufficientTrustOverlap)
    );

    // Cross-chain, expired trust period, tampered app_hash, and supply-key refusals.
    let mut tampered_app = skip.clone();
    tampered_app.header.app_hash[0] ^= 0xFF;
    assert_eq!(
        verify_comet_header_s11(&anchor, &tampered_app, 1_780_000_600),
        Err(CometGateError::BadCommitBinding)
    );

    let mut cross = skip.clone();
    cross.header.chain_id = "theta-testnet-001".into();
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
    assert_eq!(
        decode_bank_balance_kv(BANK_STORE_KEY, &[0x00, 5, b'u', b'a', b't', b'o', b'm'], b"10"),
        Err(EnvelopeError::NotBalanceKey)
    );
}
