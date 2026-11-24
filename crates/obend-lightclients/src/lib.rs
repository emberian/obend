#![forbid(unsafe_code)]
//! `S11`-hardened Electra & CometBFT light-client header admission gates, real pure-Rust
//! BLS12-381 `SyncAggregate` (`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`) & RFC 8032 Ed25519
//! `verify_strict` validator-quorum verification, SSZ Merkle branch verification, two-level
//! ICS-23 Cosmos `bank` membership envelope verification, and sealed `ProvenForeignHolding`
//! construction (closing `S8` and `S11` with zero external crate dependencies and zero boolean
//! signature shortcuts).
//!
//! Quarried cleanly from `breadstuffs/eth-lightclient/src/{lib.rs,ssz.rs,execution.rs,finality.rs}`
//! and `breadstuffs/cosmos-lightclient/src/{lib.rs,bank.rs,verified_gate.rs}`.

use std::collections::BTreeSet;

pub mod bigint;
pub mod bls12_381;
pub mod ed25519;
pub mod sha512;

// ---------------------------------------------------------------------------
// Pure-Rust FIPS 180-4 SHA-256 & Constant-Time Equality (zero external crates)
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Constant-time byte-slice equality.
pub fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Compute FIPS 180-4 SHA-256 of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = SHA256_H0;
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity((data.len() + 9 + 63) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.as_chunks::<64>().0 {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[4 * i],
                block[4 * i + 1],
                block[4 * i + 2],
                block[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// `SHA-256(a || b)` — SSZ Merkle internal node hash (`eth-lightclient/src/ssz.rs:18`).
pub fn sha256_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    sha256(&buf)
}

/// SSZ `is_valid_merkle_branch` (`eth-lightclient/src/ssz.rs:130`).
pub fn is_valid_merkle_branch(
    leaf: &[u8; 32],
    branch: &[[u8; 32]],
    index: u64,
    root: &[u8; 32],
) -> bool {
    if branch.len() >= 64 {
        return false;
    }
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = sha256_pair(node, &value);
        } else {
            value = sha256_pair(&value, node);
        }
    }
    ct_eq(&value, root)
}

// ---------------------------------------------------------------------------
// SSZ `hash_tree_root` Primitives & Containers (Altair..Electra)
// ---------------------------------------------------------------------------

/// Merkleize 32-byte SSZ chunks: pad up to next power of two with zero chunks and pairwise hash.
pub fn ssz_merkleize(mut chunks: Vec<[u8; 32]>) -> [u8; 32] {
    if chunks.is_empty() {
        return [0u8; 32];
    }
    let n = chunks.len().next_power_of_two();
    chunks.resize(n, [0u8; 32]);
    while chunks.len() > 1 {
        let mut next = Vec::with_capacity(chunks.len() / 2);
        for pair in chunks.as_chunks::<2>().0 {
            next.push(sha256_pair(&pair[0], &pair[1]));
        }
        chunks = next;
    }
    chunks[0]
}

/// SSZ `hash_tree_root` of `uint64` (little-endian right-padded to 32 bytes).
#[inline]
pub fn ssz_htr_u64(x: u64) -> [u8; 32] {
    let mut c = [0u8; 32];
    c[..8].copy_from_slice(&x.to_le_bytes());
    c
}

/// SSZ `hash_tree_root` of `BLSPubkey` (`Bytes48`): `SHA-256(pk[0..32] || (pk[32..48] || 0^16))`.
pub fn ssz_htr_bytes48(pk: &[u8; 48]) -> [u8; 32] {
    let mut c0 = [0u8; 32];
    c0.copy_from_slice(&pk[0..32]);
    let mut c1 = [0u8; 32];
    c1[..16].copy_from_slice(&pk[32..48]);
    sha256_pair(&c0, &c1)
}

/// SSZ `hash_tree_root` of `Bytes20` (`ExecutionAddress`).
#[inline]
pub fn ssz_htr_bytes20(b: &[u8; 20]) -> [u8; 32] {
    let mut c = [0u8; 32];
    c[..20].copy_from_slice(b);
    c
}

/// SSZ `hash_tree_root` of `Vector[byte, 256]` (`logs_bloom`).
pub fn ssz_htr_logs_bloom(bloom: &[u8; 256]) -> [u8; 32] {
    let chunks: Vec<[u8; 32]> = (0..8)
        .map(|i| {
            let mut c = [0u8; 32];
            c.copy_from_slice(&bloom[i * 32..i * 32 + 32]);
            c
        })
        .collect();
    ssz_merkleize(chunks)
}

/// SSZ `hash_tree_root` of `List[byte, 32]` (`extra_data`). Fails closed if `data.len() > 32`.
pub fn ssz_htr_bytelist_le32(data: &[u8]) -> Option<[u8; 32]> {
    if data.len() > 32 {
        return None;
    }
    let mut chunk = [0u8; 32];
    chunk[..data.len()].copy_from_slice(data);
    let mut len_chunk = [0u8; 32];
    len_chunk[..8].copy_from_slice(&(data.len() as u64).to_le_bytes());
    Some(sha256_pair(&chunk, &len_chunk))
}

/// Ethereum consensus `BeaconBlockHeader` (5-field SSZ container).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

impl BeaconBlockHeader {
    pub fn hash_tree_root(&self) -> [u8; 32] {
        ssz_merkleize(vec![
            ssz_htr_u64(self.slot),
            ssz_htr_u64(self.proposer_index),
            self.parent_root,
            self.state_root,
            self.body_root,
        ])
    }
}

/// Deneb / Electra 17-field `ExecutionPayloadHeader` SSZ container (`eth-lightclient/src/execution.rs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionPayloadHeader {
    pub parent_hash: [u8; 32],
    pub fee_recipient: [u8; 20],
    pub state_root: [u8; 32],
    pub receipts_root: [u8; 32],
    pub logs_bloom: [u8; 256],
    pub prev_randao: [u8; 32],
    pub block_number: u64,
    pub gas_limit: u64,
    pub gas_used: u64,
    pub timestamp: u64,
    pub extra_data: Vec<u8>,
    pub base_fee_per_gas: [u8; 32],
    pub block_hash: [u8; 32],
    pub transactions_root: [u8; 32],
    pub withdrawals_root: [u8; 32],
    pub blob_gas_used: u64,
    pub excess_blob_gas: u64,
}

impl ExecutionPayloadHeader {
    pub fn hash_tree_root(&self) -> Option<[u8; 32]> {
        let extra_root = ssz_htr_bytelist_le32(&self.extra_data)?;
        Some(ssz_merkleize(vec![
            self.parent_hash,
            ssz_htr_bytes20(&self.fee_recipient),
            self.state_root,
            self.receipts_root,
            ssz_htr_logs_bloom(&self.logs_bloom),
            self.prev_randao,
            ssz_htr_u64(self.block_number),
            ssz_htr_u64(self.gas_limit),
            ssz_htr_u64(self.gas_used),
            ssz_htr_u64(self.timestamp),
            extra_root,
            self.base_fee_per_gas,
            self.block_hash,
            self.transactions_root,
            self.withdrawals_root,
            ssz_htr_u64(self.blob_gas_used),
            ssz_htr_u64(self.excess_blob_gas),
        ]))
    }
}

// ---------------------------------------------------------------------------
// Electra S11-Hardened Light-Client Header Gate (Real BLS12-381 SyncAggregate)
// ---------------------------------------------------------------------------

pub const SYNC_COMMITTEE_SIZE: usize = 512;
pub const SYNC_COMMITTEE_BITS_BYTES: usize = SYNC_COMMITTEE_SIZE / 8;
pub const SLOTS_PER_SYNC_COMMITTEE_PERIOD: u64 = 8192;
pub const SECONDS_PER_SLOT: u64 = 12;
pub const FINALIZED_ROOT_DEPTH_ALTAIR: usize = 6;
pub const FINALIZED_ROOT_DEPTH_ELECTRA: usize = 7;
pub const FINALIZED_ROOT_SUBTREE_INDEX: u64 = 41;
pub const EXECUTION_PAYLOAD_DEPTH: usize = 4;
pub const EXECUTION_PAYLOAD_SUBTREE_INDEX: u64 = 9;

/// Ethereum consensus `DOMAIN_SYNC_COMMITTEE` (`0x07000000`).
pub const DOMAIN_SYNC_COMMITTEE: [u8; 4] = [0x07, 0x00, 0x00, 0x00];

/// Derive the Ethereum sync-committee period directly from the slot (closing `S11`).
pub fn period_of_slot(slot: u64) -> u64 {
    slot / SLOTS_PER_SYNC_COMMITTEE_PERIOD
}

/// Ethereum `compute_fork_data_root(fork_version, genesis_validators_root)`.
pub fn compute_fork_data_root(
    fork_version: [u8; 4],
    genesis_validators_root: &[u8; 32],
) -> [u8; 32] {
    let mut version_chunk = [0u8; 32];
    version_chunk[..4].copy_from_slice(&fork_version);
    sha256_pair(&version_chunk, genesis_validators_root)
}

/// Ethereum Consensus-Spec `compute_fork_digest(current_version, genesis_validators_root)`:
/// `ForkDigest` is the leading 4 bytes of `compute_fork_data_root(fork_version, genesis_validators_root)`.
pub fn compute_fork_digest(fork_version: [u8; 4], genesis_validators_root: &[u8; 32]) -> [u8; 4] {
    let fdr = compute_fork_data_root(fork_version, genesis_validators_root);
    [fdr[0], fdr[1], fdr[2], fdr[3]]
}

/// Ethereum `compute_domain(DOMAIN_SYNC_COMMITTEE, fork_version, genesis_validators_root)`.
pub fn compute_sync_committee_domain(
    fork_version: [u8; 4],
    genesis_validators_root: &[u8; 32],
) -> [u8; 32] {
    let fdr = compute_fork_data_root(fork_version, genesis_validators_root);
    let mut domain = [0u8; 32];
    domain[..4].copy_from_slice(&DOMAIN_SYNC_COMMITTEE);
    domain[4..].copy_from_slice(&fdr[..28]);
    domain
}

/// Ethereum `compute_signing_root(attested_header, domain)` for `DOMAIN_SYNC_COMMITTEE`.
pub fn compute_eth_signing_root(
    attested_header: &BeaconBlockHeader,
    fork_version: [u8; 4],
    genesis_validators_root: &[u8; 32],
) -> [u8; 32] {
    let domain = compute_sync_committee_domain(fork_version, genesis_validators_root);
    sha256_pair(&attested_header.hash_tree_root(), &domain)
}

fn validate_and_hash_sync_committee(
    pubkeys: &[[u8; 48]],
) -> Result<(Vec<bls12_381::G1Affine>, [u8; 32]), EthGateError> {
    if pubkeys.len() != SYNC_COMMITTEE_SIZE {
        return Err(EthGateError::WrongCommitteeSize);
    }
    let mut validated = Vec::with_capacity(SYNC_COMMITTEE_SIZE);
    let mut pubkey_roots = Vec::with_capacity(SYNC_COMMITTEE_SIZE);
    for pk in pubkeys {
        let p = bls12_381::key_validate(pk).map_err(|_| EthGateError::BadSyncCommitteePubkey)?;
        validated.push(p);
        pubkey_roots.push(ssz_htr_bytes48(pk));
    }
    let agg = bls12_381::aggregate_g1(&validated);
    if agg.is_identity() {
        return Err(EthGateError::BadSyncCommitteePubkey);
    }
    let pubkeys_root = ssz_merkleize(pubkey_roots);
    let agg_root = ssz_htr_bytes48(&agg.to_compressed());
    Ok((validated, ssz_merkleize(vec![pubkeys_root, agg_root])))
}

/// Compute the Ethereum SSZ `SyncCommittee` `hash_tree_root` (`Vector[BLSPubkey, 512]` +
/// `aggregate_pubkey`), validating every G1 pubkey (`KeyValidate`) and rejecting rogue cancellation.
pub fn compute_sync_committee_root(pubkeys: &[[u8; 48]]) -> Result<[u8; 32], EthGateError> {
    validate_and_hash_sync_committee(pubkeys).map(|(_, root)| root)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EthTrustAnchor {
    pub expected_chain_id: u64,
    pub fork_version: [u8; 4],
    pub genesis_validators_root: [u8; 32],
    pub expected_fork_digest: [u8; 4],
    pub genesis_time: u64,
    pub current_period: u64,
    /// Pinned SSZ `hash_tree_root` of the trusted 512-validator `SyncCommittee`.
    pub trusted_sync_committee_root: [u8; 32],
    pub trusted_attested_slot: u64,
    pub trusted_finalized_slot: u64,
    pub max_staleness: u64,
    pub max_clock_drift: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EthHeaderUpdate {
    pub chain_id: u64,
    pub fork_digest: [u8; 4],
    pub attested_header: BeaconBlockHeader,
    pub signature_slot: u64,
    pub attested_time: u64,
    pub sync_committee_pubkeys: Vec<[u8; 48]>,
    pub sync_committee_bits: [u8; SYNC_COMMITTEE_BITS_BYTES],
    pub signing_root: [u8; 32],
    pub sync_aggregate_signature: [u8; 96],
    pub finalized_header: BeaconBlockHeader,
    pub finality_branch: Vec<[u8; 32]>,
    pub execution_payload_header: ExecutionPayloadHeader,
    pub execution_branch: Vec<[u8; 32]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EthGateError {
    InvalidClock,
    ChainIdMismatch,
    ForkDigestMismatch,
    PeriodMismatch,
    FutureSlotSpoof,
    FinalizedAfterAttested,
    FinalizedHeightRollback,
    NonMonotonicAttestedSlot,
    AttestedTimeMismatch,
    StaleHeader,
    FutureTimestampSpoof,
    WrongCommitteeSize,
    BadSyncCommitteePubkey,
    SyncCommitteeRootMismatch,
    ZeroParticipants,
    InsufficientParticipation,
    SigningRootMismatch,
    BadBlsSignature,
    BadFinalityBranch,
    BadExecutionBranch,
}

/// Sealed, unforgeable verified Ethereum finalized header (private fields; only
/// [`verify_eth_header_s11`] can construct one — closing `S8`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedEthHeader {
    chain_id: u64,
    fork_digest: [u8; 4],
    attested_slot: u64,
    signature_slot: u64,
    finalized_slot: u64,
    finalized_beacon_root: [u8; 32],
    execution_block_number: u64,
    execution_block_hash: [u8; 32],
    execution_state_root: [u8; 32],
}

impl VerifiedEthHeader {
    pub fn chain_id(&self) -> u64 {
        self.chain_id
    }
    pub fn fork_digest(&self) -> [u8; 4] {
        self.fork_digest
    }
    pub fn attested_slot(&self) -> u64 {
        self.attested_slot
    }
    pub fn signature_slot(&self) -> u64 {
        self.signature_slot
    }
    pub fn finalized_slot(&self) -> u64 {
        self.finalized_slot
    }
    pub fn finalized_beacon_root(&self) -> [u8; 32] {
        self.finalized_beacon_root
    }
    pub fn execution_block_number(&self) -> u64 {
        self.execution_block_number
    }
    pub fn execution_block_hash(&self) -> [u8; 32] {
        self.execution_block_hash
    }
    pub fn execution_state_root(&self) -> [u8; 32] {
        self.execution_state_root
    }
}

/// `S11`-hardened Ethereum Electra light-client header admission gate with real pure-Rust
/// BLS12-381 `SyncAggregate` signature verification, SSZ `SyncCommittee` anchor binding,
/// `DOMAIN_SYNC_COMMITTEE` signing-root binding, and SSZ finality/execution Merkle branch checks.
pub fn verify_eth_header_s11(
    anchor: &EthTrustAnchor,
    u: &EthHeaderUpdate,
    host_now: u64,
) -> Result<VerifiedEthHeader, EthGateError> {
    if host_now == 0 {
        return Err(EthGateError::InvalidClock);
    }
    if u.chain_id != anchor.expected_chain_id {
        return Err(EthGateError::ChainIdMismatch);
    }
    let expected_fd = compute_fork_digest(anchor.fork_version, &anchor.genesis_validators_root);
    if !ct_eq(&anchor.expected_fork_digest, &expected_fd) || !ct_eq(&u.fork_digest, &expected_fd) {
        return Err(EthGateError::ForkDigestMismatch);
    }
    let attested_slot = u.attested_header.slot;
    let finalized_slot = u.finalized_header.slot;
    // Altair..Electra `process_light_client_update`: strict `signature_slot > attested_header.slot`.
    if u.signature_slot <= attested_slot {
        return Err(EthGateError::FutureSlotSpoof);
    }
    if period_of_slot(u.signature_slot) != anchor.current_period {
        return Err(EthGateError::PeriodMismatch);
    }
    if attested_slot < finalized_slot {
        return Err(EthGateError::FinalizedAfterAttested);
    }
    if finalized_slot < anchor.trusted_finalized_slot {
        return Err(EthGateError::FinalizedHeightRollback);
    }
    if attested_slot <= anchor.trusted_attested_slot {
        return Err(EthGateError::NonMonotonicAttestedSlot);
    }
    // Deterministically bind `attested_time` and `signature_slot` wall-clock time to `genesis_time`
    // + `slot * SECONDS_PER_SLOT` so an attacker cannot spoof `attested_time` on a stale header.
    let expected_attested_time = attested_slot
        .checked_mul(SECONDS_PER_SLOT)
        .and_then(|dt| anchor.genesis_time.checked_add(dt))
        .ok_or(EthGateError::FutureTimestampSpoof)?;
    if u.attested_time != expected_attested_time {
        return Err(EthGateError::AttestedTimeMismatch);
    }
    let signature_time = u
        .signature_slot
        .checked_mul(SECONDS_PER_SLOT)
        .and_then(|dt| anchor.genesis_time.checked_add(dt))
        .ok_or(EthGateError::FutureTimestampSpoof)?;
    if host_now > expected_attested_time.saturating_add(anchor.max_staleness) {
        return Err(EthGateError::StaleHeader);
    }
    if expected_attested_time > host_now.saturating_add(anchor.max_clock_drift)
        || signature_time > host_now.saturating_add(anchor.max_clock_drift)
    {
        return Err(EthGateError::FutureTimestampSpoof);
    }
    if u.execution_payload_header.timestamp > expected_attested_time {
        return Err(EthGateError::FutureTimestampSpoof);
    }

    // Check cheap participation counts before running pairing/subgroup arithmetic (anti-DoS).
    if u.sync_committee_pubkeys.len() != SYNC_COMMITTEE_SIZE {
        return Err(EthGateError::WrongCommitteeSize);
    }
    let participant_count: usize = u
        .sync_committee_bits
        .iter()
        .map(|b| b.count_ones() as usize)
        .sum();
    if participant_count == 0 {
        return Err(EthGateError::ZeroParticipants);
    }
    if participant_count.saturating_mul(3) < SYNC_COMMITTEE_SIZE * 2 {
        return Err(EthGateError::InsufficientParticipation);
    }

    // Bind `signing_root` strictly to `(attested_header, DOMAIN_SYNC_COMMITTEE, fork_version, gvr)`.
    let expected_signing_root = compute_eth_signing_root(
        &u.attested_header,
        anchor.fork_version,
        &anchor.genesis_validators_root,
    );
    if !ct_eq(&u.signing_root, &expected_signing_root) {
        return Err(EthGateError::SigningRootMismatch);
    }

    // Check SSZ `SyncCommittee` commitment against `anchor.trusted_sync_committee_root` BEFORE
    // paying for 255-bit `[r]P` subgroup checks on untrusted keys (anti-DoS), then run full IETF
    // `KeyValidate` subgroup checks on every participating key!
    let agg_compressed = bls12_381::aggregate_g1_compressed_unchecked(&u.sync_committee_pubkeys)
        .map_err(|_| EthGateError::BadSyncCommitteePubkey)?;
    let pubkey_roots: Vec<[u8; 32]> = u
        .sync_committee_pubkeys
        .iter()
        .map(ssz_htr_bytes48)
        .collect();
    let pubkeys_root = ssz_merkleize(pubkey_roots);
    let agg_root = ssz_htr_bytes48(&agg_compressed);
    let committee_root = ssz_merkleize(vec![pubkeys_root, agg_root]);
    if !ct_eq(&committee_root, &anchor.trusted_sync_committee_root) {
        return Err(EthGateError::SyncCommitteeRootMismatch);
    }

    let mut participating_pks = Vec::with_capacity(participant_count);
    for (i, pk_bytes) in u.sync_committee_pubkeys.iter().enumerate() {
        if (u.sync_committee_bits[i / 8] >> (i % 8)) & 1 == 1 {
            let pk = bls12_381::key_validate(pk_bytes)
                .map_err(|_| EthGateError::BadSyncCommitteePubkey)?;
            participating_pks.push(pk);
        }
    }

    if !bls12_381::fast_aggregate_verify(
        &participating_pks,
        &expected_signing_root,
        &u.sync_aggregate_signature,
    ) {
        return Err(EthGateError::BadBlsSignature);
    }

    let finalized_beacon_root = u.finalized_header.hash_tree_root();
    if u.finality_branch.len() != FINALIZED_ROOT_DEPTH_ELECTRA
        || !is_valid_merkle_branch(
            &finalized_beacon_root,
            &u.finality_branch,
            FINALIZED_ROOT_SUBTREE_INDEX,
            &u.attested_header.state_root,
        )
    {
        return Err(EthGateError::BadFinalityBranch);
    }

    let execution_payload_root = u
        .execution_payload_header
        .hash_tree_root()
        .ok_or(EthGateError::BadExecutionBranch)?;
    if u.execution_branch.len() != EXECUTION_PAYLOAD_DEPTH
        || !is_valid_merkle_branch(
            &execution_payload_root,
            &u.execution_branch,
            EXECUTION_PAYLOAD_SUBTREE_INDEX,
            &u.finalized_header.body_root,
        )
    {
        return Err(EthGateError::BadExecutionBranch);
    }

    Ok(VerifiedEthHeader {
        chain_id: u.chain_id,
        fork_digest: u.fork_digest,
        attested_slot,
        signature_slot: u.signature_slot,
        finalized_slot,
        finalized_beacon_root,
        execution_block_number: u.execution_payload_header.block_number,
        execution_block_hash: u.execution_payload_header.block_hash,
        execution_state_root: u.execution_payload_header.state_root,
    })
}

// ---------------------------------------------------------------------------
// CometBFT S11-Hardened Light-Client Gate (Real Ed25519 Quorum) + Two-Level ICS-23
// ---------------------------------------------------------------------------

pub const COSMOS_CHAIN_TAG: u8 = 2;
pub const EVM_CHAIN_TAG: u8 = 1;
pub const BANK_STORE_KEY: &[u8] = b"bank";
pub const BALANCES_PREFIX: u8 = 0x02;
/// CometBFT `SignedMsgType` for `PrecommitType` (`0x02`).
pub const COMET_PRECOMMIT_TYPE: u8 = 0x02;
/// Tendermint `MAX_TOTAL_VOTING_POWER` (`i64::MAX / 8`).
pub const MAX_TOTAL_VOTING_POWER: u64 = (i64::MAX as u64) / 8;
/// Maximum validator-set size admitted per CometBFT header update (anti-DoS bound).
pub const MAX_COMET_VALIDATORS: usize = 1024;

/// RFC 6962 / Tendermint `merkle.HashFromByteSlices`:
/// - `n == 0`: `SHA-256(b"")`
/// - `n == 1`: `SHA-256(0x00 || leaf)`
/// - `n > 1`: `SHA-256(0x01 || left || right)` split at largest power-of-two `k < n`.
pub fn merkle_hash_from_byte_slices(slices: &[Vec<u8>]) -> [u8; 32] {
    fn hash_range(items: &[Vec<u8>]) -> [u8; 32] {
        let n = items.len();
        if n == 0 {
            return sha256(&[]);
        }
        if n == 1 {
            let mut leaf = Vec::with_capacity(1 + items[0].len());
            leaf.push(0x00);
            leaf.extend_from_slice(&items[0]);
            return sha256(&leaf);
        }
        let k = 1usize << (usize::BITS - 1 - (n - 1).leading_zeros());
        let left = hash_range(&items[..k]);
        let right = hash_range(&items[k..]);
        let mut inner = [0u8; 65];
        inner[0] = 0x01;
        inner[1..33].copy_from_slice(&left);
        inner[33..65].copy_from_slice(&right);
        sha256(&inner)
    }
    hash_range(slices)
}

/// Encode CometBFT Protobuf `tendermint.types.SimpleValidator` (`pub_key` Ed25519 + `voting_power`).
pub fn encode_simple_validator_proto(pubkey: &[u8; 32], voting_power: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(48);
    // field 1 (0x0a, len 34): tendermint.crypto.PublicKey { field 1 (0x0a, len 32): ed25519 }
    out.extend_from_slice(&[0x0a, 0x22, 0x0a, 0x20]);
    out.extend_from_slice(pubkey);
    if voting_power != 0 {
        out.push(0x10);
        push_uvarint_u64(&mut out, voting_power);
    }
    out
}

/// One CometBFT validator entry (`Ed25519` public key + stake weight).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometValidator {
    pub pubkey: [u8; 32],
    pub voting_power: u64,
}

/// CometBFT `BlockID` (`hash` + `PartSetHeader { total, hash }`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometBlockId {
    pub hash: Vec<u8>,
    pub part_set_total: u32,
    pub part_set_hash: Vec<u8>,
}

impl CometBlockId {
    pub fn empty() -> Self {
        Self {
            hash: Vec::new(),
            part_set_total: 0,
            part_set_hash: Vec::new(),
        }
    }

    pub fn parts(hash: [u8; 32], part_set_total: u32, part_set_hash: [u8; 32]) -> Self {
        Self {
            hash: hash.to_vec(),
            part_set_total,
            part_set_hash: part_set_hash.to_vec(),
        }
    }
}

/// Full 14-field CometBFT `tendermint.types.Header` authenticated by `Header::Hash()`
/// (`merkle.HashFromByteSlices` over the 14 Protobuf-encoded header fields).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometHeader {
    pub version_block: u64,
    pub version_app: u64,
    pub chain_id: String,
    pub height: u64,
    pub header_time_secs: u64,
    pub header_time_nanos: u32,
    pub last_block_id: CometBlockId,
    pub last_commit_hash: Vec<u8>,
    pub data_hash: Vec<u8>,
    pub validators_hash: [u8; 32],
    pub next_validators_hash: [u8; 32],
    pub consensus_hash: [u8; 32],
    pub app_hash: [u8; 32],
    pub last_results_hash: Vec<u8>,
    pub evidence_hash: Vec<u8>,
    pub proposer_address: [u8; 20],
}

impl CometHeader {
    /// Construct a standard CometBFT v0.34+/v0.38 (`version.block = 11`) header.
    pub fn new_standard(
        chain_id: impl Into<String>,
        height: u64,
        header_time_secs: u64,
        validators_hash: [u8; 32],
        next_validators_hash: [u8; 32],
        app_hash: [u8; 32],
        proposer_address: [u8; 20],
    ) -> Self {
        let z = sha256(b"");
        Self {
            version_block: 11,
            version_app: 0,
            chain_id: chain_id.into(),
            height,
            header_time_secs,
            header_time_nanos: 0,
            last_block_id: CometBlockId::parts(z, 1, z),
            last_commit_hash: z.to_vec(),
            data_hash: z.to_vec(),
            validators_hash,
            next_validators_hash,
            consensus_hash: z,
            app_hash,
            last_results_hash: z.to_vec(),
            evidence_hash: z.to_vec(),
            proposer_address,
        }
    }
}

/// One validator's Ed25519 `Precommit` signature inside a CometBFT `Commit`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometCommitSig {
    pub validator_index: usize,
    pub timestamp_secs: u64,
    pub timestamp_nanos: u32,
    pub signature: [u8; 64],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometTrustAnchor {
    pub expected_chain_id: String,
    pub trusted_height: u64,
    pub trusted_header_time: u64,
    pub trusted_next_validators: Vec<CometValidator>,
    pub trusted_next_validators_hash: [u8; 32],
    pub trusting_period: u64,
    pub max_staleness: u64,
    pub max_clock_drift: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CometHeaderUpdate {
    pub header: CometHeader,
    pub commit_round: u32,
    pub commit_block_id: CometBlockId,
    pub validators: Vec<CometValidator>,
    pub commit_sigs: Vec<CometCommitSig>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CometAdvanceMode {
    Adjacent,
    Skipping,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CometGateError {
    InvalidClock,
    ChainIdMismatch,
    MalformedHeaderField,
    NonIncreasingHeight,
    TrustedStateExpired,
    StaleHeader,
    NonMonotonicTime,
    FutureTimestampSpoof,
    BadCommitBinding,
    BadSelfBinding,
    BadEpochBinding,
    TrustedValidatorSetMismatch,
    ZeroTotalPower,
    ZeroTrustedPower,
    TooManyValidators { count: usize },
    ZeroValidatorPower,
    VotingPowerOverflow,
    DuplicateValidatorKey,
    InvalidValidatorPubkey,
    OutOfBoundsValidatorIndex { validator_index: usize },
    DuplicateValidatorSignature { validator_index: usize },
    InvalidValidatorSignature { validator_index: usize },
    InsufficientVotingPower,
    InsufficientTrustOverlap,
}

/// Validate a CometBFT validator set (non-empty, bounded size, canonical non-torsion Ed25519 keys,
/// unique keys, positive bounded power) and return `(validator_set_hash, total_voting_power)`
/// using the exact Tendermint `merkle.HashFromByteSlices` over Protobuf `SimpleValidator` leaves.
pub fn validate_and_hash_validator_set(
    validators: &[CometValidator],
) -> Result<([u8; 32], u64), CometGateError> {
    if validators.is_empty() {
        return Err(CometGateError::ZeroTotalPower);
    }
    if validators.len() > MAX_COMET_VALIDATORS {
        return Err(CometGateError::TooManyValidators {
            count: validators.len(),
        });
    }
    let mut seen_pks = BTreeSet::new();
    let mut total_power = 0u64;
    let mut leaves = Vec::with_capacity(validators.len());
    for v in validators {
        if v.voting_power == 0 {
            return Err(CometGateError::ZeroValidatorPower);
        }
        if !ed25519::validate_public_key(&v.pubkey) {
            return Err(CometGateError::InvalidValidatorPubkey);
        }
        if !seen_pks.insert(v.pubkey) {
            return Err(CometGateError::DuplicateValidatorKey);
        }
        total_power = total_power
            .checked_add(v.voting_power)
            .ok_or(CometGateError::VotingPowerOverflow)?;
        if total_power > MAX_TOTAL_VOTING_POWER {
            return Err(CometGateError::VotingPowerOverflow);
        }
        leaves.push(encode_simple_validator_proto(&v.pubkey, v.voting_power));
    }
    Ok((merkle_hash_from_byte_slices(&leaves), total_power))
}

/// Convenience wrapper returning only the canonical CometBFT `ValidatorSet::Hash()`.
pub fn compute_validator_set_hash(
    validators: &[CometValidator],
) -> Result<[u8; 32], CometGateError> {
    validate_and_hash_validator_set(validators).map(|(h, _)| h)
}

fn pb_bytes_value(b: &[u8]) -> Vec<u8> {
    if b.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(2 + b.len());
    out.push(0x0a);
    push_uvarint(&mut out, b.len());
    out.extend_from_slice(b);
    out
}

fn pb_u64_value(n: u64) -> Vec<u8> {
    if n == 0 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(11);
    out.push(0x08);
    push_uvarint_u64(&mut out, n);
    out
}

fn pb_timestamp(secs: u64, nanos: u32) -> Vec<u8> {
    let mut out = Vec::with_capacity(18);
    if secs != 0 {
        out.push(0x08);
        push_uvarint_u64(&mut out, secs);
    }
    if nanos != 0 {
        out.push(0x10);
        push_uvarint_u64(&mut out, u64::from(nanos));
    }
    out
}

fn pb_block_id(bid: &CometBlockId) -> Vec<u8> {
    let mut ps = Vec::with_capacity(40);
    if bid.part_set_total != 0 {
        ps.push(0x08);
        push_uvarint_u64(&mut ps, u64::from(bid.part_set_total));
    }
    if !bid.part_set_hash.is_empty() {
        ps.push(0x12);
        push_uvarint(&mut ps, bid.part_set_hash.len());
        ps.extend_from_slice(&bid.part_set_hash);
    }
    let mut out = Vec::with_capacity(4 + bid.hash.len() + ps.len());
    if !bid.hash.is_empty() {
        out.push(0x0a);
        push_uvarint(&mut out, bid.hash.len());
        out.extend_from_slice(&bid.hash);
    }
    // In Tendermint `BlockID` / `CanonicalBlockID`, `part_set_header` (field 2 = 0x12) is a
    // message field and is emitted with its length prefix even when empty.
    out.push(0x12);
    push_uvarint(&mut out, ps.len());
    out.extend_from_slice(&ps);
    out
}

/// Compute the exact CometBFT `Header::Hash()` (`merkle.HashFromByteSlices` over the 14
/// Protobuf-encoded `tendermint.types.Header` fields).
pub fn compute_comet_block_id_hash(header: &CometHeader) -> [u8; 32] {
    let mut ver = Vec::with_capacity(20);
    if header.version_block != 0 {
        ver.push(0x08);
        push_uvarint_u64(&mut ver, header.version_block);
    }
    if header.version_app != 0 {
        ver.push(0x10);
        push_uvarint_u64(&mut ver, header.version_app);
    }
    let fields = [
        ver,
        pb_bytes_value(header.chain_id.as_bytes()),
        pb_u64_value(header.height),
        pb_timestamp(header.header_time_secs, header.header_time_nanos),
        pb_block_id(&header.last_block_id),
        pb_bytes_value(&header.last_commit_hash),
        pb_bytes_value(&header.data_hash),
        pb_bytes_value(&header.validators_hash),
        pb_bytes_value(&header.next_validators_hash),
        pb_bytes_value(&header.consensus_hash),
        pb_bytes_value(&header.app_hash),
        pb_bytes_value(&header.last_results_hash),
        pb_bytes_value(&header.evidence_hash),
        pb_bytes_value(&header.proposer_address),
    ];
    merkle_hash_from_byte_slices(&fields)
}

/// Encode exact CometBFT Protobuf length-delimited `CanonicalVote` (`PrecommitType = 0x02`)
/// sign-bytes (`type`, `height` sfixed64, `round` sfixed64, `block_id`, `timestamp`, `chain_id`).
pub fn encode_canonical_precommit_vote(
    chain_id: &str,
    height: u64,
    round: u32,
    block_id: &CometBlockId,
    timestamp_secs: u64,
    timestamp_nanos: u32,
) -> Vec<u8> {
    let mut msg = Vec::with_capacity(120 + chain_id.len());
    // field 1: SignedMsgType type = PrecommitType (2)
    msg.extend_from_slice(&[0x08, COMET_PRECOMMIT_TYPE]);
    // field 2: sfixed64 height (omitted only when 0 per Proto3)
    if height != 0 {
        msg.push(0x11);
        msg.extend_from_slice(&height.to_le_bytes());
    }
    // field 3: sfixed64 round (omitted only when 0 per Proto3)
    if round != 0 {
        msg.push(0x19);
        msg.extend_from_slice(&u64::from(round).to_le_bytes());
    }
    // field 4: CanonicalBlockID (omitted for nil precommit votes per CometBFT `CanonicalizeVote`)
    if !block_id.hash.is_empty()
        || block_id.part_set_total != 0
        || !block_id.part_set_hash.is_empty()
    {
        let cbid = pb_block_id(block_id);
        msg.push(0x22);
        push_uvarint(&mut msg, cbid.len());
        msg.extend_from_slice(&cbid);
    }
    // field 5: google.protobuf.Timestamp
    let ts = pb_timestamp(timestamp_secs, timestamp_nanos);
    msg.push(0x2a);
    push_uvarint(&mut msg, ts.len());
    msg.extend_from_slice(&ts);
    // field 6: string chain_id
    if !chain_id.is_empty() {
        msg.push(0x32);
        push_uvarint(&mut msg, chain_id.len());
        msg.extend_from_slice(chain_id.as_bytes());
    }

    let mut framed = Vec::with_capacity(5 + msg.len());
    push_uvarint(&mut framed, msg.len());
    framed.extend_from_slice(&msg);
    framed
}

/// Sealed, unforgeable verified CometBFT header (private fields; only
/// [`verify_comet_header_s11`] can construct one).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedCometHeader {
    chain_id: String,
    height: u64,
    header_time: u64,
    validators_hash: [u8; 32],
    next_validators_hash: [u8; 32],
    app_hash: [u8; 32],
    mode: CometAdvanceMode,
}

impl VerifiedCometHeader {
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    pub fn height(&self) -> u64 {
        self.height
    }
    pub fn header_time(&self) -> u64 {
        self.header_time
    }
    pub fn validators_hash(&self) -> [u8; 32] {
        self.validators_hash
    }
    pub fn next_validators_hash(&self) -> [u8; 32] {
        self.next_validators_hash
    }
    pub fn app_hash(&self) -> [u8; 32] {
        self.app_hash
    }
    pub fn mode(&self) -> CometAdvanceMode {
        self.mode
    }
}

fn opt_hash32_ok(b: &[u8]) -> bool {
    b.is_empty() || b.len() == 32
}

/// `S11`-hardened CometBFT adjacent & skipping header admission gate with real RFC 8032 Ed25519
/// `verify_strict` validator-signature verification over CometBFT Protobuf `CanonicalVote` bytes.
pub fn verify_comet_header_s11(
    anchor: &CometTrustAnchor,
    u: &CometHeaderUpdate,
    host_now: u64,
) -> Result<VerifiedCometHeader, CometGateError> {
    if host_now == 0 {
        return Err(CometGateError::InvalidClock);
    }
    if anchor.expected_chain_id.is_empty() || u.header.chain_id != anchor.expected_chain_id {
        return Err(CometGateError::ChainIdMismatch);
    }
    if u.header.header_time_nanos >= 1_000_000_000
        || !opt_hash32_ok(&u.header.last_block_id.hash)
        || !opt_hash32_ok(&u.header.last_block_id.part_set_hash)
        || !opt_hash32_ok(&u.header.last_commit_hash)
        || !opt_hash32_ok(&u.header.data_hash)
        || !opt_hash32_ok(&u.header.last_results_hash)
        || !opt_hash32_ok(&u.header.evidence_hash)
    {
        return Err(CometGateError::MalformedHeaderField);
    }
    if u.header.height <= anchor.trusted_height {
        return Err(CometGateError::NonIncreasingHeight);
    }
    if host_now
        >= anchor
            .trusted_header_time
            .saturating_add(anchor.trusting_period)
    {
        return Err(CometGateError::TrustedStateExpired);
    }
    if host_now
        > u.header
            .header_time_secs
            .saturating_add(anchor.max_staleness)
    {
        return Err(CometGateError::StaleHeader);
    }
    if u.header.header_time_secs < anchor.trusted_header_time
        || (u.header.header_time_secs == anchor.trusted_header_time
            && u.header.header_time_nanos == 0)
    {
        return Err(CometGateError::NonMonotonicTime);
    }
    if u.header.header_time_secs > host_now.saturating_add(anchor.max_clock_drift) {
        return Err(CometGateError::FutureTimestampSpoof);
    }

    // 1. Validate & pin the anchor's trusted next-validator set (`ValidatorSet::Hash()`).
    if anchor.trusted_next_validators.is_empty() {
        return Err(CometGateError::ZeroTrustedPower);
    }
    let (trusted_val_hash, trusted_total_power) =
        validate_and_hash_validator_set(&anchor.trusted_next_validators)?;
    if !ct_eq(&trusted_val_hash, &anchor.trusted_next_validators_hash) {
        return Err(CometGateError::TrustedValidatorSetMismatch);
    }

    // 2. Verify Commit -> Header binding (`commit_block_id.hash == Header::Hash()`).
    let expected_block_id = compute_comet_block_id_hash(&u.header);
    if !ct_eq(&u.commit_block_id.hash, &expected_block_id)
        || u.commit_block_id.part_set_total == 0
        || u.commit_block_id.part_set_hash.len() != 32
    {
        return Err(CometGateError::BadCommitBinding);
    }

    // 3. Verify ValidatorSet -> Header self-binding (`ValidatorSet::Hash() == header.validators_hash`).
    let (val_hash, total_power) = validate_and_hash_validator_set(&u.validators)?;
    if !ct_eq(&val_hash, &u.header.validators_hash) {
        return Err(CometGateError::BadSelfBinding);
    }

    // 4. Dispatch Adjacent (`height == trusted + 1`) vs Skipping (`height > trusted + 1`).
    let mode = if u.header.height == anchor.trusted_height.saturating_add(1) {
        if !ct_eq(&val_hash, &anchor.trusted_next_validators_hash) {
            return Err(CometGateError::BadEpochBinding);
        }
        CometAdvanceMode::Adjacent
    } else {
        CometAdvanceMode::Skipping
    };

    // 5. Verify every Ed25519 signature strictly over `CanonicalVote`, rejecting duplicates and
    //    any invalid signature, and summing both untrusted and trusted-overlap voting power.
    let mut seen_indices = BTreeSet::new();
    let mut signed_power = 0u64;
    let mut trusted_signed_power = 0u64;

    for cs in &u.commit_sigs {
        let Some(val) = u.validators.get(cs.validator_index) else {
            return Err(CometGateError::OutOfBoundsValidatorIndex {
                validator_index: cs.validator_index,
            });
        };
        if !seen_indices.insert(cs.validator_index) {
            return Err(CometGateError::DuplicateValidatorSignature {
                validator_index: cs.validator_index,
            });
        };
        if cs.timestamp_nanos >= 1_000_000_000 {
            return Err(CometGateError::InvalidValidatorSignature {
                validator_index: cs.validator_index,
            });
        }
        let vote_bytes = encode_canonical_precommit_vote(
            &u.header.chain_id,
            u.header.height,
            u.commit_round,
            &u.commit_block_id,
            cs.timestamp_secs,
            cs.timestamp_nanos,
        );
        if !ed25519::verify_strict(&val.pubkey, &vote_bytes, &cs.signature) {
            return Err(CometGateError::InvalidValidatorSignature {
                validator_index: cs.validator_index,
            });
        }
        signed_power = signed_power
            .checked_add(val.voting_power)
            .ok_or(CometGateError::VotingPowerOverflow)?;
        // IMPORTANT: In Skipping mode, credit the TRUSTED validator's voting_power from
        // `anchor.trusted_next_validators` (never the untrusted set's claimed power!).
        if let Some(trusted_val) = anchor
            .trusted_next_validators
            .iter()
            .find(|tv| ct_eq(&tv.pubkey, &val.pubkey))
        {
            trusted_signed_power = trusted_signed_power
                .checked_add(trusted_val.voting_power)
                .ok_or(CometGateError::VotingPowerOverflow)?;
        }
    }

    if (signed_power as u128) * 3 <= (total_power as u128) * 2 {
        return Err(CometGateError::InsufficientVotingPower);
    }
    if mode == CometAdvanceMode::Skipping
        && (trusted_signed_power as u128) * 3 <= (trusted_total_power as u128)
    {
        return Err(CometGateError::InsufficientTrustOverlap);
    }

    Ok(VerifiedCometHeader {
        chain_id: u.header.chain_id.clone(),
        height: u.header.height,
        header_time: u.header.header_time_secs,
        validators_hash: u.header.validators_hash,
        next_validators_hash: u.header.next_validators_hash,
        app_hash: u.header.app_hash,
        mode,
    })
}

// ---------------------------------------------------------------------------
// Two-Level ICS-23 Existence Proof Envelope & Sealed ProvenForeignHolding (S8)
// ---------------------------------------------------------------------------

/// ICS-23 leaf hashing operation (IAVL / Tendermint simple-merkle SHA-256 layout):
/// `SHA-256(prefix || varint(key.len()) || key || varint(val_bytes.len()) || val_bytes)`
/// where `val_bytes = SHA-256(value)` when `prehash_value` is true.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23LeafOp {
    pub prefix: Vec<u8>,
    pub prehash_value: bool,
}

/// ICS-23 inner-node hashing operation: `SHA-256(prefix || child_hash || suffix)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23InnerOp {
    pub prefix: Vec<u8>,
    pub suffix: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23ExistenceProof {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
    pub leaf: Ics23LeafOp,
    pub path: Vec<Ics23InnerOp>,
}

/// Two-level Cosmos multistore proof: `key -> value` inside `store_key` (`bank`) root,
/// and `store_key -> store_root` inside `header.app_hash`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ics23TwoLevelProof {
    pub store_key: Vec<u8>,
    pub store_root: [u8; 32],
    pub sub_proof: Ics23ExistenceProof,
    pub root_proof: Ics23ExistenceProof,
}

fn push_uvarint_u64(buf: &mut Vec<u8>, mut n: u64) {
    loop {
        let mut byte = (n & 0x7f) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if n == 0 {
            break;
        }
    }
}

fn push_uvarint(buf: &mut Vec<u8>, n: usize) {
    push_uvarint_u64(buf, n as u64);
}

pub fn compute_ics23_root(proof: &Ics23ExistenceProof) -> [u8; 32] {
    let mut leaf_preimage = Vec::with_capacity(proof.leaf.prefix.len() + proof.key.len() + 48);
    leaf_preimage.extend_from_slice(&proof.leaf.prefix);
    push_uvarint(&mut leaf_preimage, proof.key.len());
    leaf_preimage.extend_from_slice(&proof.key);
    if proof.leaf.prehash_value {
        let vh = sha256(&proof.value);
        push_uvarint(&mut leaf_preimage, vh.len());
        leaf_preimage.extend_from_slice(&vh);
    } else {
        push_uvarint(&mut leaf_preimage, proof.value.len());
        leaf_preimage.extend_from_slice(&proof.value);
    }
    let mut acc = sha256(&leaf_preimage);
    for inner in &proof.path {
        let mut buf = Vec::with_capacity(inner.prefix.len() + 32 + inner.suffix.len());
        buf.extend_from_slice(&inner.prefix);
        buf.extend_from_slice(&acc);
        buf.extend_from_slice(&inner.suffix);
        acc = sha256(&buf);
    }
    acc
}

pub const MAX_IAVL_PROOF_DEPTH: usize = 128;
pub const MAX_TENDERMINT_PROOF_DEPTH: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvelopeError {
    InvalidProofSpec,
    StoreKeyMismatch,
    SubProofRootMismatch,
    MultiStoreRootMismatch,
    NotBankStore,
    NotBalanceKey,
    MalformedKey,
    BadAddressLength(usize),
    BadDenom,
    MalformedAmount,
    AmountOverflow,
}

/// Enforce Cosmos SDK `ics23::iavl_spec()` invariants on an IAVL existence proof so a relayer
/// cannot forge leaf/inner domain prefixes (`0x00` leaf height vs `> 0` inner height), disable
/// `prehash_value`, or smuggle arbitrary sibling widths.
fn validate_iavl_proof_spec(proof: &Ics23ExistenceProof) -> Result<(), EnvelopeError> {
    if proof.key.is_empty() || proof.value.is_empty() || proof.path.len() > MAX_IAVL_PROOF_DEPTH {
        return Err(EnvelopeError::InvalidProofSpec);
    }
    if !proof.leaf.prehash_value {
        return Err(EnvelopeError::InvalidProofSpec);
    }
    // IAVL leaf prefix is `varint(height = 0) || varint(size = 1) || varint(version)`:
    // `0x00, 0x02, <1..=10 bytes version varint>`.
    if !(3..=12).contains(&proof.leaf.prefix.len())
        || proof.leaf.prefix[0] != 0x00
        || proof.leaf.prefix[1] != 0x02
    {
        return Err(EnvelopeError::InvalidProofSpec);
    }
    for inner in &proof.path {
        // Every IAVL inner node has `height >= 1`, so its signed-varint prefix NEVER starts with `0x00`.
        if inner.prefix.first().copied().unwrap_or(0x00) == 0x00 {
            return Err(EnvelopeError::InvalidProofSpec);
        }
        let left_branch_ok = (3..=16).contains(&inner.prefix.len())
            && (inner.suffix.len() == 32 || (inner.suffix.len() == 33 && inner.suffix[0] == 0x20));
        let right_branch_ok = (35..=49).contains(&inner.prefix.len()) && inner.suffix.is_empty();
        if !left_branch_ok && !right_branch_ok {
            return Err(EnvelopeError::InvalidProofSpec);
        }
    }
    Ok(())
}

/// Enforce Cosmos SDK `ics23::tendermint_spec()` (RFC 6962 `0x00` leaf / `0x01` inner) invariants
/// on the multistore root proof so leaf and inner nodes are strictly domain-separated.
fn validate_tendermint_proof_spec(proof: &Ics23ExistenceProof) -> Result<(), EnvelopeError> {
    if proof.key.is_empty()
        || proof.value.len() != 32
        || proof.path.len() > MAX_TENDERMINT_PROOF_DEPTH
    {
        return Err(EnvelopeError::InvalidProofSpec);
    }
    if !proof.leaf.prehash_value || proof.leaf.prefix.as_slice() != [0x00] {
        return Err(EnvelopeError::InvalidProofSpec);
    }
    for inner in &proof.path {
        if inner.prefix.first().copied() != Some(0x01) {
            return Err(EnvelopeError::InvalidProofSpec);
        }
        let left_branch_ok = (1..=2).contains(&inner.prefix.len())
            && (inner.suffix.len() == 32 || (inner.suffix.len() == 33 && inner.suffix[0] == 0x20));
        let right_branch_ok = (33..=35).contains(&inner.prefix.len()) && inner.suffix.is_empty();
        if !left_branch_ok && !right_branch_ok {
            return Err(EnvelopeError::InvalidProofSpec);
        }
    }
    Ok(())
}

/// Verify a two-level ICS-23 existence proof against an authenticated `app_hash`, strictly pinning
/// `IavlSpec` on `sub_proof` and `TendermintSpec` on `root_proof`.
pub fn verify_two_level_ics23(
    expected_app_hash: &[u8; 32],
    proof: &Ics23TwoLevelProof,
) -> Result<(), EnvelopeError> {
    validate_iavl_proof_spec(&proof.sub_proof)?;
    validate_tendermint_proof_spec(&proof.root_proof)?;
    if proof.root_proof.key != proof.store_key {
        return Err(EnvelopeError::StoreKeyMismatch);
    }
    if !ct_eq(&proof.root_proof.value, &proof.store_root) {
        return Err(EnvelopeError::SubProofRootMismatch);
    }
    if !ct_eq(&compute_ics23_root(&proof.sub_proof), &proof.store_root) {
        return Err(EnvelopeError::SubProofRootMismatch);
    }
    if !ct_eq(&compute_ics23_root(&proof.root_proof), expected_app_hash) {
        return Err(EnvelopeError::MultiStoreRootMismatch);
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBankBalance {
    pub address: Vec<u8>,
    pub denom: String,
    pub amount: u128,
}

/// Fail-closed Cosmos SDK `bank` balances-prefix (`0x02 || len || addr || denom`) decoder,
/// quarried from `breadstuffs/cosmos-lightclient/src/bank.rs`.
pub fn decode_bank_balance_kv(
    store_key: &[u8],
    key: &[u8],
    value: &[u8],
) -> Result<DecodedBankBalance, EnvelopeError> {
    if store_key != BANK_STORE_KEY {
        return Err(EnvelopeError::NotBankStore);
    }
    if key.len() < 3 {
        return Err(EnvelopeError::MalformedKey);
    }
    if key[0] != BALANCES_PREFIX {
        return Err(EnvelopeError::NotBalanceKey);
    }
    let addr_len = key[1] as usize;
    if addr_len == 0 || addr_len > 32 {
        return Err(EnvelopeError::BadAddressLength(addr_len));
    }
    if key.len() < 2 + addr_len + 3 {
        return Err(EnvelopeError::MalformedKey);
    }
    let address = key[2..2 + addr_len].to_vec();
    let denom_bytes = &key[2 + addr_len..];
    let denom = std::str::from_utf8(denom_bytes)
        .map_err(|_| EnvelopeError::BadDenom)?
        .to_owned();
    let mut chars = denom.chars();
    let first_valid = chars.next().is_some_and(|c| c.is_ascii_alphabetic());
    let rest_valid = denom.len() >= 3
        && denom.len() <= 128
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '/' | ':' | '.' | '_' | '-'));
    if !first_valid || !rest_valid {
        return Err(EnvelopeError::BadDenom);
    }
    if value.is_empty() || !value.iter().all(|b| b.is_ascii_digit()) {
        return Err(EnvelopeError::MalformedAmount);
    }
    if value.len() > 1 && value[0] == b'0' {
        return Err(EnvelopeError::MalformedAmount);
    }
    let s = std::str::from_utf8(value).map_err(|_| EnvelopeError::MalformedAmount)?;
    let amount = s
        .parse::<u128>()
        .map_err(|_| EnvelopeError::AmountOverflow)?;
    Ok(DecodedBankBalance {
        address,
        denom,
        amount,
    })
}

/// Domain-separated 32-byte asset ID (`cosmos-lightclient/src/bank.rs:160`).
pub fn cosmos_denom_asset_id(denom: &str) -> [u8; 32] {
    let mut buf = Vec::with_capacity(22 + denom.len());
    buf.extend_from_slice(b"dregg-cosmos-denom-v1:");
    buf.extend_from_slice(denom.as_bytes());
    sha256(&buf)
}

/// Sealed, light-client-proven foreign holding (`S8` closed: private fields, `chain_id` derived
/// strictly from the verified header rather than caller input, `holder_len` disambiguating 20-byte
/// `AccAddress` vs 32-byte module/Wasm accounts, and `consensus_proven` unconditionally `true`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenForeignHolding {
    chain_tag: u8,
    chain_id: String,
    holder: [u8; 32],
    holder_len: u8,
    asset: [u8; 32],
    amount: u128,
    snapshot_height: u64,
    consensus_proven: bool,
}

impl ProvenForeignHolding {
    pub fn chain_tag(&self) -> u8 {
        self.chain_tag
    }
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    pub fn holder(&self) -> [u8; 32] {
        self.holder
    }
    pub fn holder_len(&self) -> u8 {
        self.holder_len
    }
    /// Exact variable-length Cosmos account address bytes (`1..=32` bytes), preventing 20-byte vs
    /// leading-zero 32-byte address aliasing.
    pub fn holder_bytes(&self) -> &[u8] {
        &self.holder[32 - usize::from(self.holder_len)..]
    }
    pub fn asset(&self) -> [u8; 32] {
        self.asset
    }
    pub fn amount(&self) -> u128 {
        self.amount
    }
    /// Verified CometBFT header height whose `app_hash` authenticated this holding.
    pub fn snapshot_height(&self) -> u64 {
        self.snapshot_height
    }
    /// Post-execution application block height committed by CometBFT `header.app_hash` (`H - 1`).
    pub fn app_state_height(&self) -> u64 {
        self.snapshot_height.saturating_sub(1)
    }
    pub fn consensus_proven(&self) -> bool {
        self.consensus_proven
    }
}

/// Verify a two-level ICS-23 `bank` balance proof under a [`VerifiedCometHeader`] and mint a
/// sealed [`ProvenForeignHolding`] bound to the verified header's own `chain_id` and `height`.
pub fn verify_cosmos_bank_balance_envelope(
    header: &VerifiedCometHeader,
    proof: &Ics23TwoLevelProof,
) -> Result<ProvenForeignHolding, EnvelopeError> {
    verify_two_level_ics23(&header.app_hash(), proof)?;
    let bal = decode_bank_balance_kv(
        &proof.store_key,
        &proof.sub_proof.key,
        &proof.sub_proof.value,
    )?;
    let holder_len = bal.address.len() as u8;
    let mut holder = [0u8; 32];
    holder[32 - bal.address.len()..].copy_from_slice(&bal.address);
    Ok(ProvenForeignHolding {
        chain_tag: COSMOS_CHAIN_TAG,
        chain_id: header.chain_id().to_owned(),
        holder,
        holder_len,
        asset: cosmos_denom_asset_id(&bal.denom),
        amount: bal.amount,
        snapshot_height: header.height(),
        consensus_proven: true,
    })
}
