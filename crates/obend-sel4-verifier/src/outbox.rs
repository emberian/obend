//! Non-trivial `cSHAKE256` / `SHA-256` `Simplex` `FinCert` (`n - f` quorum, `3f + 1 <= n`)
//! and `IrreversibleOutbox` domain-separated `0x00/0x01` `effectsRoot` Merkle verifier (`CAP-30`).
//!
//! Aligns byte-for-byte with:
//! - `Obend.Consensus.SimplexProtocol` (`Protocol.quorum = n - f`, `3f + 1 <= n`, `Entry.encode`),
//! - `Obend.Consensus.SimplexLiveness` (`"OBEND-SIMPLEX-AUTH-V1"` `encodeSignablePreimage` and
//!   hash-based one-time slot commitment signatures `commitSlotSigScheme`),
//! - `Obend.Vault.IrreversibleOutbox` (`"OBEND-OUTBOX-EFFECT-V1"`, `"OBEND-OUTBOX-NULLIFIER-V1"`,
//!   3-class `OutboxEffectClass`, monotonic `high_water_nullifier`), and
//! - RFC 6962 / `Obend.Receipt.Merkle` `0x00` leaf vs `0x01` internal node domain separation.

use super::*;

/// Domain customization tag matching `Obend.Vault.IrreversibleOutbox.outboxEffectDomain`.
pub const OUTBOX_EFFECT_DOMAIN: &[u8] = b"OBEND-OUTBOX-EFFECT-V1";
/// Domain customization tag matching `Obend.Vault.IrreversibleOutbox.outboxNullifierDomain`.
pub const OUTBOX_NULLIFIER_DOMAIN: &[u8] = b"OBEND-OUTBOX-NULLIFIER-V1";
/// Domain customization tag matching `Obend.Consensus.SimplexLiveness.simplexAuthDomainBytes`.
pub const SIMPLEX_AUTH_DOMAIN: &[u8] = b"OBEND-SIMPLEX-AUTH-V1";
/// Domain customization tag matching `Obend.Consensus.Finality.simplexChainDomain`.
pub const SIMPLEX_CHAIN_DOMAIN: &[u8] = b"OBEND-SIMPLEX-CHAIN-V1";
/// Domain customization tag for `IrreversibleOutbox` `effectsRoot` `0x00/0x01` Merkle trees.
pub const OUTBOX_MERKLE_DOMAIN: &[u8] = b"OBEND-OUTBOX-MERKLE-V1";
/// Domain customization tag for `SimplexLiveness` slot-key commitment openings.
pub const SIMPLEX_SLOT_SIG_DOMAIN: &[u8] = b"OBEND-SIMPLEX-SLOT-SIG-V1";
/// Domain customization tag binding `(post_state_root, effects_root)` inside a finalized block payload.
pub const OUTBOX_BLOCK_PAYLOAD_DOMAIN: &[u8] = b"OBEND-OUTBOX-BLOCK-PAYLOAD-V1";
/// Domain customization tag binding the committee roster and per-validator slot public keys.
pub const SIMPLEX_COMMITTEE_DOMAIN: &[u8] = b"OBEND-SIMPLEX-COMMITTEE-V1";
/// Domain customization tag binding `(gatekeeper_pd, high_water_nullifier)` into `revoked_root`.
pub const OUTBOX_WINDOW_DOMAIN: &[u8] = b"OBEND-OUTBOX-WINDOW-V1";
/// Domain customization tag binding `(effect_commit, effects_root, leaf_index)` into `turn_hash`.
pub const OUTBOX_TURN_DOMAIN: &[u8] = b"OBEND-OUTBOX-TURN-V1";

/// Cryptographic hash suite used by `SimplexFinCert` and `IrreversibleOutbox` `effectsRoot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutboxHashAlg {
    Cshake256,
    Sha256,
}

/// Streaming domain-separated 256-bit hasher abstracting `cSHAKE256` and `SHA-256` without heap allocation.
enum DomainHasher {
    Cshake(Sponge),
    Sha(Sha256),
}
impl DomainHasher {
    fn new(alg: OutboxHashAlg, domain: &[u8]) -> Self {
        match alg {
            OutboxHashAlg::Cshake256 => Self::Cshake(customized(domain)),
            OutboxHashAlg::Sha256 => {
                let mut h = Sha256::new();
                h.update(&(domain.len() as u64).to_be_bytes());
                h.update(domain);
                Self::Sha(h)
            }
        }
    }
    fn update(&mut self, bytes: &[u8]) {
        match self {
            Self::Cshake(s) => s.absorb(bytes),
            Self::Sha(h) => h.update(bytes),
        }
    }
    fn finish(self) -> Digest {
        match self {
            Self::Cshake(s) => s.digest(),
            Self::Sha(h) => h.finalize(),
        }
    }
}

/// Three-class external effect taxonomy matching `Obend.Vault.IrreversibleOutbox.EffectClass`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum OutboxEffectClass {
    IdempotentRead = 0x01,
    CompensatableEscrow = 0x02,
    IrreversibleActuation = 0x03,
}
impl OutboxEffectClass {
    pub const fn tag_byte(self) -> u8 {
        self as u8
    }
}

/// Compute the 256-bit `IrreversibleOutbox` effect commitment over
/// `be8(nullifier_id) || [cls] || be8(payload.len()) || payload` (`IrreversibleOutbox.lean:95-126`).
pub fn effect_commit_digest(
    alg: OutboxHashAlg,
    nullifier_id: u64,
    cls: OutboxEffectClass,
    payload: &[u8],
) -> Digest {
    let mut h = DomainHasher::new(alg, OUTBOX_EFFECT_DOMAIN);
    h.update(&nullifier_id.to_be_bytes());
    h.update(&[cls.tag_byte()]);
    h.update(&(payload.len() as u64).to_be_bytes());
    h.update(payload);
    h.finish()
}

/// Derive the 256-bit domain-separated outbox nullifier digest (`IrreversibleOutbox.lean:133-136`).
pub fn outbox_nullifier_digest(alg: OutboxHashAlg, gatekeeper_pd: u64, nullifier_id: u64) -> Digest {
    let mut h = DomainHasher::new(alg, OUTBOX_NULLIFIER_DOMAIN);
    h.update(&gatekeeper_pd.to_be_bytes());
    h.update(&nullifier_id.to_be_bytes());
    h.finish()
}

/// Domain-separated **`0x00` leaf hash** for `IrreversibleOutbox` `effectsRoot`:
/// hashes `0x00 || be8(leaf_index) || effect_commit`.
/// In `Sha256` mode this uses raw RFC 6962 `SHA-256(0x00 || be8(leaf_index) || effect_commit)`;
/// in `Cshake256` mode it uses `cSHAKE256("OBEND-OUTBOX-MERKLE-V1", 0x00 || be8(leaf_index) || effect_commit)`.
pub fn effects_merkle_leaf(alg: OutboxHashAlg, leaf_index: u64, effect_commit: &Digest) -> Digest {
    let mut pre = [0u8; 41];
    pre[0] = 0x00;
    pre[1..9].copy_from_slice(&leaf_index.to_be_bytes());
    pre[9..41].copy_from_slice(effect_commit);
    match alg {
        OutboxHashAlg::Cshake256 => {
            let mut out = [0u8; 32];
            cshake256(OUTBOX_MERKLE_DOMAIN, &pre, &mut out);
            out
        }
        OutboxHashAlg::Sha256 => sha256(&pre),
    }
}

/// Domain-separated **`0x01` internal node hash** for `IrreversibleOutbox` `effectsRoot`:
/// hashes `0x01 || left(32) || right(32)`.
/// Disjoint tag byte `0x01 != 0x00` (and preimage width `65 != 41`) rules out 64-byte Merkle
/// second-preimage / internal-node-as-leaf confusion (`S4`).
pub fn effects_merkle_node(alg: OutboxHashAlg, left: &Digest, right: &Digest) -> Digest {
    let mut pre = [0u8; 65];
    pre[0] = 0x01;
    pre[1..33].copy_from_slice(left);
    pre[33..65].copy_from_slice(right);
    match alg {
        OutboxHashAlg::Cshake256 => {
            let mut out = [0u8; 32];
            cshake256(OUTBOX_MERKLE_DOMAIN, &pre, &mut out);
            out
        }
        OutboxHashAlg::Sha256 => sha256(&pre),
    }
}

/// Verify a `0x00/0x01` domain-separated binary Merkle inclusion proof opening `(leaf_index, effect_commit)`
/// against `expected_effects_root` at tree depth `depth` (`2^depth` leaves).
pub fn verify_effects_merkle_proof(
    alg: OutboxHashAlg,
    depth: u32,
    leaf_index: u64,
    effect_commit: &Digest,
    siblings: &[Digest],
    expected_effects_root: &Digest,
) -> bool {
    if depth >= 64
        || siblings.len() != depth as usize
        || leaf_index >= (1u64 << depth)
        || ct_eq_digest(expected_effects_root, &[0u8; 32])
        || ct_eq_digest(effect_commit, &[0u8; 32])
    {
        return false;
    }
    let mut cur = effects_merkle_leaf(alg, leaf_index, effect_commit);
    for (lvl, sibling) in siblings.iter().enumerate() {
        let bit = (leaf_index >> lvl) & 1;
        cur = if bit == 0 {
            effects_merkle_node(alg, &cur, sibling)
        } else {
            effects_merkle_node(alg, sibling, &cur)
        };
    }
    ct_eq_digest(&cur, expected_effects_root)
}

/// Stack-resident `0x00/0x01` Merkle tree over `LEAVES` (`2^D`) outbox effect commitments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EffectsMerkleTree<const LEAVES: usize> {
    commits: [Digest; LEAVES],
}
impl<const LEAVES: usize> EffectsMerkleTree<LEAVES> {
    pub fn from_commits(commits: [Digest; LEAVES]) -> Option<Self> {
        if LEAVES == 0 || !LEAVES.is_power_of_two() {
            return None;
        }
        Some(Self { commits })
    }
    pub const fn depth() -> u32 {
        LEAVES.trailing_zeros()
    }
    pub fn root(&self, alg: OutboxHashAlg) -> Digest {
        let mut nodes: [Digest; LEAVES] =
            core::array::from_fn(|i| effects_merkle_leaf(alg, i as u64, &self.commits[i]));
        let mut width = LEAVES;
        while width > 1 {
            let half = width / 2;
            for i in 0..half {
                nodes[i] = effects_merkle_node(alg, &nodes[2 * i], &nodes[2 * i + 1]);
            }
            width = half;
        }
        nodes[0]
    }
    pub fn open<const DEPTH: usize>(&self, alg: OutboxHashAlg, index: usize) -> Option<[Digest; DEPTH]> {
        if index >= LEAVES || (1usize << DEPTH) != LEAVES {
            return None;
        }
        let mut nodes: [Digest; LEAVES] =
            core::array::from_fn(|i| effects_merkle_leaf(alg, i as u64, &self.commits[i]));
        let mut path = [[0u8; 32]; DEPTH];
        let mut idx = index;
        let mut width = LEAVES;
        for slot in &mut path {
            *slot = nodes[idx ^ 1];
            let half = width / 2;
            for i in 0..half {
                nodes[i] = effects_merkle_node(alg, &nodes[2 * i], &nodes[2 * i + 1]);
            }
            idx >>= 1;
            width = half;
        }
        Some(path)
    }
}

/// Bind `(post_state_root, effects_root)` into the 256-bit block payload committed by `Simplex`.
pub fn block_effects_payload(
    alg: OutboxHashAlg,
    post_state_root: &Digest,
    effects_root: &Digest,
) -> Digest {
    let mut h = DomainHasher::new(alg, OUTBOX_BLOCK_PAYLOAD_DOMAIN);
    h.update(post_state_root);
    h.update(effects_root);
    h.finish()
}

/// Canonical entry of a `SimplexProtocol.Chain` (`SimplexProtocol.lean:98-100, 856-858`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SimplexChainEntry {
    Block { view: u64, payload: Digest },
    EmptyView { view: u64 },
}
impl SimplexChainEntry {
    pub const ZERO: Self = Self::EmptyView { view: 0 };

    pub const fn view(&self) -> u64 {
        match self {
            Self::Block { view, .. } | Self::EmptyView { view } => *view,
        }
    }
    /// Canonical 41-byte wire form matching `SimplexProtocol.Entry.encode`.
    pub fn encode(&self) -> [u8; 41] {
        let mut out = [0u8; 41];
        match self {
            Self::Block { view, payload } => {
                out[0] = 0x01;
                out[1..9].copy_from_slice(&view.to_be_bytes());
                out[9..41].copy_from_slice(payload);
            }
            Self::EmptyView { view } => {
                out[0] = 0x00;
                out[1..9].copy_from_slice(&view.to_be_bytes());
            }
        }
        out
    }
}

/// Compute `Obend.Consensus.Finality.chainDigest` over finalized blocks (`EmptyView` filtered out).
pub fn simplex_chain_digest(alg: OutboxHashAlg, chain: &[SimplexChainEntry]) -> Digest {
    let mut h = DomainHasher::new(alg, SIMPLEX_CHAIN_DOMAIN);
    for entry in chain {
        if matches!(entry, SimplexChainEntry::Block { .. }) {
            h.update(&entry.encode());
        }
    }
    h.finish()
}

/// Stream `SimplexLiveness.slotSigPreimage` for a `Kind::Finalize` (`0x03`) vote on `(view, chain)`
/// by `signer_id` with 32-byte commitment opening `sig_salt`, returning the derived 256-bit slot public key.
///
/// Exact byte layout (`SimplexLiveness.lean:69-176, 491-518`):
/// `be8(content_len) || 0x01 || be8(21) || "OBEND-SIMPLEX-AUTH-V1" || be8(signer_id) || be8(view) || 0x03 || 0x01 || encodeChainBytes(chain) || sig_salt`.
pub fn derive_finalize_slot_pubkey(
    alg: OutboxHashAlg,
    signer_id: u64,
    view: u64,
    chain: &[SimplexChainEntry],
    sig_salt: &Digest,
) -> Option<Digest> {
    let k = u64::try_from(chain.len()).ok()?;
    let chain_bytes_len = k.checked_mul(42)?.checked_add(1)?;
    let target_bytes_len = chain_bytes_len.checked_add(1)?;
    let signable_len = (8u64 + SIMPLEX_AUTH_DOMAIN.len() as u64 + 8 + 8 + 1)
        .checked_add(target_bytes_len)?;
    let content_len = signable_len.checked_add(1)?;

    let mut h = DomainHasher::new(alg, SIMPLEX_SLOT_SIG_DOMAIN);
    h.update(&content_len.to_be_bytes());
    // slotContent(Some(msg)) prefix `0x01`
    h.update(&[0x01]);
    // frameBytes64(simplexAuthDomainBytes)
    h.update(&(SIMPLEX_AUTH_DOMAIN.len() as u64).to_be_bytes());
    h.update(SIMPLEX_AUTH_DOMAIN);
    h.update(&signer_id.to_be_bytes());
    h.update(&view.to_be_bytes());
    // encodeKindByte(.finalize) = 0x03, encodeTargetBytes(.block c) = 0x01 :: encodeChainBytes(c)
    h.update(&[0x03, 0x01]);
    for entry in chain {
        h.update(&[0x01]);
        h.update(&entry.encode());
    }
    h.update(&[0x00]);
    h.update(sig_salt);
    Some(h.finish())
}

/// One validator's authenticated `finalize` vote inside a `SimplexFinCert`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct ValidatorFinalizeVote {
    pub signer_id: u64,
    pub sig_salt: Digest,
}
impl ValidatorFinalizeVote {
    pub const ZERO: Self = Self {
        signer_id: 0,
        sig_salt: [0u8; 32],
    };
}

/// Pinned BFT committee directory enforcing `3f + 1 <= n` and VOTE/FINALIZE quorum `n - f` (`G5`),
/// holding one-time `SimplexLiveness` slot public keys across `active_views` views starting at `base_view`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimplexCommittee<const MAX_N: usize, const MAX_VIEWS: usize = 4> {
    pub n: usize,
    pub f: usize,
    pub base_view: u64,
    pub active_views: usize,
    pub hash_alg: OutboxHashAlg,
    pub slot_pubkeys: [[Digest; MAX_N]; MAX_VIEWS],
}
impl<const MAX_N: usize, const MAX_VIEWS: usize> SimplexCommittee<MAX_N, MAX_VIEWS> {
    /// Returns `Some(n - f)` iff `1 <= n <= MAX_N`, `3 * f + 1 <= n`, `1 <= active_views <= MAX_VIEWS`,
    /// `base_view >= 1`, and every active `(view, validator)` slot key is non-zero.
    pub fn quorum(&self) -> Option<usize> {
        if self.n == 0
            || self.n > MAX_N
            || self.base_view == 0
            || self.active_views == 0
            || self.active_views > MAX_VIEWS
        {
            return None;
        }
        let min_n = self.f.checked_mul(3)?.checked_add(1)?;
        if self.n < min_n {
            return None;
        }
        for v in 0..self.active_views {
            for pk in &self.slot_pubkeys[v][..self.n] {
                if ct_eq_digest(pk, &[0u8; 32]) {
                    return None;
                }
            }
        }
        self.n.checked_sub(self.f)
    }

    pub fn slot_pubkey(&self, view: u64, signer_idx: usize) -> Option<&Digest> {
        if signer_idx >= self.n || view < self.base_view {
            return None;
        }
        let v_off = usize::try_from(view - self.base_view).ok()?;
        if v_off >= self.active_views || v_off >= MAX_VIEWS {
            return None;
        }
        Some(&self.slot_pubkeys[v_off][signer_idx])
    }

    pub fn directory_digest(&self) -> Digest {
        let mut h = DomainHasher::new(self.hash_alg, SIMPLEX_COMMITTEE_DOMAIN);
        h.update(&(self.n as u64).to_be_bytes());
        h.update(&(self.f as u64).to_be_bytes());
        h.update(&self.base_view.to_be_bytes());
        h.update(&(self.active_views as u64).to_be_bytes());
        for v in 0..self.active_views.min(MAX_VIEWS) {
            for pk in &self.slot_pubkeys[v][..self.n.min(MAX_N)] {
                h.update(pk);
            }
        }
        h.finish()
    }
}

/// Fixed-capacity `Simplex` finalization certificate (`FinCert`) carrying `vote_count` signed finalize votes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimplexFinCert<const MAX_CHAIN: usize, const MAX_SIGNERS: usize> {
    pub view: u64,
    pub chain_len: usize,
    pub chain: [SimplexChainEntry; MAX_CHAIN],
    pub vote_count: usize,
    pub votes: [ValidatorFinalizeVote; MAX_SIGNERS],
}
impl<const MAX_CHAIN: usize, const MAX_SIGNERS: usize> SimplexFinCert<MAX_CHAIN, MAX_SIGNERS> {
    pub fn chain_slice(&self) -> Option<&[SimplexChainEntry]> {
        if self.chain_len == 0 || self.chain_len > MAX_CHAIN {
            return None;
        }
        self.chain.get(..self.chain_len)
    }
    pub fn votes_slice(&self) -> Option<&[ValidatorFinalizeVote]> {
        if self.vote_count > MAX_SIGNERS {
            return None;
        }
        self.votes.get(..self.vote_count)
    }
    pub fn tip_block(&self) -> Option<(u64, Digest)> {
        match self.chain_slice()?.last()? {
            SimplexChainEntry::Block { view, payload } => Some((*view, *payload)),
            SimplexChainEntry::EmptyView { .. } => None,
        }
    }
}

/// Named constructive refusal clauses for `FinCert` and `IrreversibleOutbox` verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutboxRefusal {
    InvalidCommitteeBounds,
    MalformedChain,
    UnfinalizedTip,
    UnderQuorum { got: usize, required: usize },
    UnknownCommitteeSigner { signer_id: u64 },
    DuplicateSigner { signer_id: u64 },
    InvalidFinalizeSignature { signer_id: u64 },
    InstanceMismatch,
    UnboundTranscript,
    PayloadLengthOutOfBounds,
    StaleOrReplayedNullifier,
    EffectsMerkleMismatch,
    BlockEffectsPayloadMismatch,
}

/// Verify a `SimplexFinCert` against `committee`:
/// - Enforces `3f + 1 <= n` and `vote_count >= n - f` (rejecting `2f + 1` when `n > 3f + 1`!),
/// - Enforces strictly increasing positive chain entry views ending in `Block { view == cert.view, payload }`,
/// - Enforces pairwise-distinct in-range `signer_id < n`, and
/// - Verifies every signer's `cSHAKE256` / `SHA-256` slot commitment signature over `encodeSignablePreimage`.
pub fn verify_fin_cert<
    const MAX_N: usize,
    const MAX_VIEWS: usize,
    const MAX_CHAIN: usize,
    const MAX_SIGNERS: usize,
>(
    committee: &SimplexCommittee<MAX_N, MAX_VIEWS>,
    cert: &SimplexFinCert<MAX_CHAIN, MAX_SIGNERS>,
) -> Result<Digest, OutboxRefusal> {
    let required = committee.quorum().ok_or(OutboxRefusal::InvalidCommitteeBounds)?;
    if cert.view == 0 {
        return Err(OutboxRefusal::MalformedChain);
    }
    let chain = cert.chain_slice().ok_or(OutboxRefusal::MalformedChain)?;
    let mut prev_view = 0u64;
    for entry in chain {
        let v = entry.view();
        if v == 0 || v <= prev_view {
            return Err(OutboxRefusal::MalformedChain);
        }
        prev_view = v;
    }
    let (tip_view, tip_payload) = cert.tip_block().ok_or(OutboxRefusal::UnfinalizedTip)?;
    if tip_view != cert.view || ct_eq_digest(&tip_payload, &[0u8; 32]) {
        return Err(OutboxRefusal::UnfinalizedTip);
    }
    let votes = cert.votes_slice().ok_or(OutboxRefusal::MalformedChain)?;
    if votes.len() < required {
        return Err(OutboxRefusal::UnderQuorum {
            got: votes.len(),
            required,
        });
    }
    for (i, vote) in votes.iter().enumerate() {
        let Ok(signer_idx) = usize::try_from(vote.signer_id) else {
            return Err(OutboxRefusal::UnknownCommitteeSigner {
                signer_id: vote.signer_id,
            });
        };
        if signer_idx >= committee.n {
            return Err(OutboxRefusal::UnknownCommitteeSigner {
                signer_id: vote.signer_id,
            });
        }
        for later in &votes[i + 1..] {
            if vote.signer_id == later.signer_id {
                return Err(OutboxRefusal::DuplicateSigner {
                    signer_id: vote.signer_id,
                });
            }
        }
        if ct_eq_digest(&vote.sig_salt, &[0u8; 32]) {
            return Err(OutboxRefusal::InvalidFinalizeSignature {
                signer_id: vote.signer_id,
            });
        }
        let Some(expected_pk) = committee.slot_pubkey(cert.view, signer_idx) else {
            return Err(OutboxRefusal::UnfinalizedTip);
        };
        let derived_pk =
            derive_finalize_slot_pubkey(committee.hash_alg, vote.signer_id, cert.view, chain, &vote.sig_salt)
                .ok_or(OutboxRefusal::MalformedChain)?;
        if !ct_eq_digest(&derived_pk, expected_pk) {
            return Err(OutboxRefusal::InvalidFinalizeSignature {
                signer_id: vote.signer_id,
            });
        }
    }
    Ok(tip_payload)
}

/// Pin `(gatekeeper_pd, high_water_nullifier)` into `FullPinnedPublicInputs::revoked_root`.
pub fn outbox_window_digest(alg: OutboxHashAlg, gatekeeper_pd: u64, high_water_nullifier: u64) -> Digest {
    let mut h = DomainHasher::new(alg, OUTBOX_WINDOW_DOMAIN);
    h.update(&gatekeeper_pd.to_be_bytes());
    h.update(&high_water_nullifier.to_be_bytes());
    h.finish()
}

/// Pin `(effect_commit, effects_root, leaf_index)` into `FullPinnedPublicInputs::turn_hash`.
pub fn outbox_turn_digest(
    alg: OutboxHashAlg,
    effect_commit: &Digest,
    effects_root: &Digest,
    leaf_index: u64,
) -> Digest {
    let mut h = DomainHasher::new(alg, OUTBOX_TURN_DOMAIN);
    h.update(effect_commit);
    h.update(effects_root);
    h.update(&leaf_index.to_be_bytes());
    h.finish()
}

/// Stack/`IpcRing`-storable receipt for a finalized `IrreversibleOutbox` actuation turn (`CAP-30` closed).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutboxTurnReceipt<
    const MAX_CHAIN: usize,
    const MAX_SIGNERS: usize,
    const DEPTH: usize,
    const MAX_PAYLOAD: usize,
> {
    pub nullifier_id: u64,
    pub leaf_index: u64,
    pub effects_root: Digest,
    pub merkle_siblings: [Digest; DEPTH],
    pub payload_len: usize,
    pub payload: [u8; MAX_PAYLOAD],
    pub fin_cert: SimplexFinCert<MAX_CHAIN, MAX_SIGNERS>,
}

/// Concrete `RelationVerifier` replacing the 51-line zero-check `verifier-stark` stub (`CAP-30`):
/// verifies `3f + 1 <= n` `Simplex` `FinCert` (`n - f` cryptographic quorum), `0x00/0x01`
/// domain-separated `IrreversibleOutbox` `effectsRoot` inclusion, block-tip `(post_state_root, effects_root)`
/// binding, and strictly monotonic nullifier advancement.
#[derive(Clone, Copy, Debug)]
pub struct OutboxFinalityVerifier<const MAX_N: usize, const MAX_VIEWS: usize = 4> {
    pub circuit_digest: Digest,
    pub authorized_cap_root: Digest,
    pub gatekeeper_pd: u64,
    pub high_water_nullifier: u64,
    pub committee: SimplexCommittee<MAX_N, MAX_VIEWS>,
}
impl<const MAX_N: usize, const MAX_VIEWS: usize> OutboxFinalityVerifier<MAX_N, MAX_VIEWS> {
    pub fn check<
        const MAX_CHAIN: usize,
        const MAX_SIGNERS: usize,
        const DEPTH: usize,
        const MAX_PAYLOAD: usize,
    >(
        &self,
        pi: &FullPinnedPublicInputs,
        challenge0: &Digest,
        r: &OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>,
    ) -> Result<Digest, OutboxRefusal> {
        let alg = self.committee.hash_alg;
        if !ct_eq_digest(&pi.circuit_desc_digest, &self.circuit_digest)
            || !ct_eq_digest(&pi.actor_vk_digest, &self.committee.directory_digest())
            || !ct_eq_digest(&pi.cap_root, &self.authorized_cap_root)
            || !ct_eq_digest(
                &pi.revoked_root,
                &outbox_window_digest(alg, self.gatekeeper_pd, self.high_water_nullifier),
            )
            || DEPTH >= 64
        {
            return Err(OutboxRefusal::InstanceMismatch);
        }
        let expected_challenge = pi.transcript().squeeze();
        if !ct_eq_digest(&expected_challenge, challenge0) {
            return Err(OutboxRefusal::UnboundTranscript);
        }
        if r.payload_len == 0 || r.payload_len > MAX_PAYLOAD {
            return Err(OutboxRefusal::PayloadLengthOutOfBounds);
        }
        if r.nullifier_id <= self.high_water_nullifier {
            return Err(OutboxRefusal::StaleOrReplayedNullifier);
        }
        let payload_slice = &r.payload[..r.payload_len];
        let eff_commit = effect_commit_digest(
            alg,
            r.nullifier_id,
            OutboxEffectClass::IrreversibleActuation,
            payload_slice,
        );
        let expected_turn_hash = outbox_turn_digest(alg, &eff_commit, &r.effects_root, r.leaf_index);
        if !ct_eq_digest(&pi.turn_hash, &expected_turn_hash) {
            return Err(OutboxRefusal::InstanceMismatch);
        }
        if !verify_effects_merkle_proof(
            alg,
            DEPTH as u32,
            r.leaf_index,
            &eff_commit,
            &r.merkle_siblings,
            &r.effects_root,
        ) {
            return Err(OutboxRefusal::EffectsMerkleMismatch);
        }
        let tip_payload = verify_fin_cert(&self.committee, &r.fin_cert)?;
        if r.fin_cert.view < pi.height {
            return Err(OutboxRefusal::UnfinalizedTip);
        }
        let expected_block_payload =
            block_effects_payload(alg, &pi.post_state_root, &r.effects_root);
        if !ct_eq_digest(&tip_payload, &expected_block_payload) {
            return Err(OutboxRefusal::BlockEffectsPayloadMismatch);
        }
        Ok(eff_commit)
    }
}

impl<
        const MAX_N: usize,
        const MAX_VIEWS: usize,
        const MAX_CHAIN: usize,
        const MAX_SIGNERS: usize,
        const DEPTH: usize,
        const MAX_PAYLOAD: usize,
    > RelationVerifier<OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>>
    for OutboxFinalityVerifier<MAX_N, MAX_VIEWS>
{
    fn commit_turn(
        &mut self,
        _pi: &FullPinnedPublicInputs,
        r: &OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>,
    ) -> bool {
        if r.nullifier_id <= self.high_water_nullifier {
            return false;
        }
        self.high_water_nullifier = r.nullifier_id;
        true
    }

    fn verify_relation(
        &self,
        pi: &FullPinnedPublicInputs,
        challenge0: &Digest,
        r: &OutboxTurnReceipt<MAX_CHAIN, MAX_SIGNERS, DEPTH, MAX_PAYLOAD>,
    ) -> bool {
        self.check(pi, challenge0, r).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestReceipt = OutboxTurnReceipt<4, 5, 2, 64>;

    fn make_salt(signer: usize, tag: u8) -> Digest {
        let mut s = [tag; 32];
        s[0] = (signer as u8).wrapping_add(1);
        s[31] = tag ^ 0x5a;
        s
    }

    #[allow(clippy::too_many_arguments)]
    fn build_honest_outbox_fixture(
        alg: OutboxHashAlg,
        n: usize,
        f: usize,
        signers: &[usize],
        nullifier_id: u64,
        high_water: u64,
        height: u64,
        view: u64,
    ) -> (OutboxFinalityVerifier<6>, SovereignTurnBundle<TestReceipt>) {
        let pre_state_root = [0x21; 32];
        let post_state_root = [0x42; 32];
        let payload_bytes = b"tx-release:vault-settle-400";
        let mut payload = [0u8; 64];
        payload[..payload_bytes.len()].copy_from_slice(payload_bytes);

        let leaf_index = 2u64;
        let eff_commit = effect_commit_digest(
            alg,
            nullifier_id,
            OutboxEffectClass::IrreversibleActuation,
            payload_bytes,
        );
        let other0 = effect_commit_digest(alg, 900, OutboxEffectClass::IdempotentRead, b"r0");
        let other1 = effect_commit_digest(alg, 901, OutboxEffectClass::CompensatableEscrow, b"e1");
        let other3 = effect_commit_digest(
            alg,
            902,
            OutboxEffectClass::IrreversibleActuation,
            b"sibling-actuation",
        );
        let tree = EffectsMerkleTree::from_commits([other0, other1, eff_commit, other3]).unwrap();
        let effects_root = tree.root(alg);
        let merkle_siblings: [Digest; 2] = tree.open(alg, leaf_index as usize).unwrap();

        let tip_payload = block_effects_payload(alg, &post_state_root, &effects_root);
        let mut chain = [SimplexChainEntry::ZERO; 4];
        chain[0] = SimplexChainEntry::EmptyView { view: 1 };
        chain[1] = SimplexChainEntry::Block {
            view,
            payload: tip_payload,
        };
        let chain_len = 2usize;

        let mut slot_pubkeys = [[[0x44u8; 32]; 6]; 4];
        for (i, pk) in slot_pubkeys[0].iter_mut().enumerate().take(n) {
            let salt = make_salt(i, 0x77);
            *pk =
                derive_finalize_slot_pubkey(alg, i as u64, view, &chain[..chain_len], &salt)
                    .unwrap();
        }
        let mut votes = [ValidatorFinalizeVote::ZERO; 5];
        for (idx, &s) in signers.iter().enumerate() {
            votes[idx] = ValidatorFinalizeVote {
                signer_id: s as u64,
                sig_salt: make_salt(s, 0x77),
            };
        }
        let fin_cert = SimplexFinCert {
            view,
            chain_len,
            chain,
            vote_count: signers.len(),
            votes,
        };
        let committee = SimplexCommittee {
            n,
            f,
            base_view: view,
            active_views: 1,
            hash_alg: alg,
            slot_pubkeys,
        };
        let circuit_digest = [0x99; 32];
        let authorized_cap_root = [0x88; 32];
        let gatekeeper_pd = 1u64;
        let verifier = OutboxFinalityVerifier {
            circuit_digest,
            authorized_cap_root,
            gatekeeper_pd,
            high_water_nullifier: high_water,
            committee,
        };
        let pi = FullPinnedPublicInputs {
            circuit_desc_digest: circuit_digest,
            actor_vk_digest: committee.directory_digest(),
            pre_state_root,
            post_state_root,
            cap_root: authorized_cap_root,
            revoked_root: outbox_window_digest(alg, gatekeeper_pd, high_water),
            height,
            turn_hash: outbox_turn_digest(alg, &eff_commit, &effects_root, leaf_index),
        };
        let challenge0 = pi.transcript().squeeze();
        let receipt = OutboxTurnReceipt {
            nullifier_id,
            leaf_index,
            effects_root,
            merkle_siblings,
            payload_len: payload_bytes.len(),
            payload,
            fin_cert,
        };
        let bundle = SovereignTurnBundle {
            public_inputs: pi,
            challenge0,
            effect_vk_digest: pi.actor_vk_digest,
            last_row_gate_ok: true,
            receipt,
        };
        (verifier, bundle)
    }

    #[test]
    fn cap30_cshake256_and_sha256_fincert_and_effects_root_settle_through_verifier_pd() {
        for alg in [OutboxHashAlg::Cshake256, OutboxHashAlg::Sha256] {
            let (v, b) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 3, 4], 10, 0, 1, 2);
            assert!(v.check(&b.public_inputs, &b.challenge0, &b.receipt).is_ok());
            assert!(verify_cipherclerk(&v, &b));

            let mut inbound = IpcRing::<_, 2>::new();
            let mut outbound = IpcRing::<SettlementVerdict, 2>::new();
            let (mut tx, mut rx) = inbound.split();
            let (mut otx, mut orx) = outbound.split();
            assert!(tx.push(b).is_ok());
            let mut pd = VerifierPd::new(v, b.public_inputs.pre_state_root, 0);
            assert_eq!(pd.drain(&mut rx, &mut otx), 1);
            let verdict = orx.pop().unwrap();
            assert!(verdict.accepted);
            assert_eq!(verdict.committed_root, b.public_inputs.post_state_root);
            assert_eq!(pd.verifier.high_water_nullifier, 10);
        }
    }

    #[test]
    fn cap30_two_f_plus_one_at_n5_f1_and_invalid_quorums_are_rejected() {
        // At n = 5, f = 1: legacy `2f + 1 = 3` MUST be rejected because two 3-of-5 quorums
        // intersect in `3 + 3 - 5 = 1 <= f` potentially faulty validator; `n - f = 4` is required!
        for alg in [OutboxHashAlg::Cshake256, OutboxHashAlg::Sha256] {
            let (v_under, b_under) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 2], 10, 0, 1, 2);
            assert_eq!(
                v_under.check(&b_under.public_inputs, &b_under.challenge0, &b_under.receipt),
                Err(OutboxRefusal::UnderQuorum {
                    got: 3,
                    required: 4
                })
            );
            assert!(!verify_cipherclerk(&v_under, &b_under));

            // Duplicate signer padding 3 distinct signers to 4 entries (`[0, 1, 2, 1]`) is rejected!
            let (v_dup, b_dup) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 2, 1], 10, 0, 1, 2);
            assert_eq!(
                v_dup.check(&b_dup.public_inputs, &b_dup.challenge0, &b_dup.receipt),
                Err(OutboxRefusal::DuplicateSigner { signer_id: 1 })
            );

            // Invalid BFT committee ratio `n = 3, f = 1` (`3f + 1 = 4 > 3`) is rejected!
            let (v_bad_bft, b_bad_bft) =
                build_honest_outbox_fixture(alg, 3, 1, &[0, 1, 2], 10, 0, 1, 2);
            assert_eq!(
                v_bad_bft.check(
                    &b_bad_bft.public_inputs,
                    &b_bad_bft.challenge0,
                    &b_bad_bft.receipt
                ),
                Err(OutboxRefusal::InvalidCommitteeBounds)
            );

            // Out-of-range signer (`signer_id = 5` at `n = 5`) is rejected!
            let (v_oob, mut b_oob) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 2, 3], 10, 0, 1, 2);
            b_oob.receipt.fin_cert.votes[3].signer_id = 5;
            assert_eq!(
                v_oob.check(&b_oob.public_inputs, &b_oob.challenge0, &b_oob.receipt),
                Err(OutboxRefusal::UnknownCommitteeSigner { signer_id: 5 })
            );

            // Tampered signature salt (forged finalize vote) is rejected!
            let (v_sig, mut b_sig) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 2, 3], 10, 0, 1, 2);
            b_sig.receipt.fin_cert.votes[2].sig_salt[0] ^= 0x01;
            assert_eq!(
                v_sig.check(&b_sig.public_inputs, &b_sig.challenge0, &b_sig.receipt),
                Err(OutboxRefusal::InvalidFinalizeSignature { signer_id: 2 })
            );
        }
    }

    #[test]
    fn cap30_merkle_0x00_0x01_domain_separation_defeats_second_preimage_and_tampering() {
        for alg in [OutboxHashAlg::Cshake256, OutboxHashAlg::Sha256] {
            let c0 = effect_commit_digest(alg, 1, OutboxEffectClass::IrreversibleActuation, b"a");
            let c1 = effect_commit_digest(alg, 2, OutboxEffectClass::IrreversibleActuation, b"b");
            let l0 = effects_merkle_leaf(alg, 0, &c0);
            let l1 = effects_merkle_leaf(alg, 1, &c1);
            let root = effects_merkle_node(alg, &l0, &l1);

            // Honest 2-leaf openings succeed:
            assert!(verify_effects_merkle_proof(alg, 1, 0, &c0, &[l1], &root));
            assert!(verify_effects_merkle_proof(alg, 1, 1, &c1, &[l0], &root));

            // Swapping leaf_index (0 vs 1) with same siblings is refused:
            assert!(!verify_effects_merkle_proof(alg, 1, 1, &c0, &[l1], &root));

            // S4 second-preimage attempt: presenting internal node `root` at depth 0 as a leaf
            // fails because depth-0 `effects_merkle_leaf` prefixes `0x00 || be8(0)`, never `0x01`!
            assert!(!verify_effects_merkle_proof(alg, 0, 0, &root, &[], &root));
            assert_ne!(effects_merkle_leaf(alg, 0, &l0), effects_merkle_node(alg, &l0, &l1));

            // Zero-check / empty-payload / replayed-nullifier attempts are refused:
            let (v, mut b) =
                build_honest_outbox_fixture(alg, 4, 1, &[0, 1, 2], 5, 5, 1, 2);
            assert_eq!(
                v.check(&b.public_inputs, &b.challenge0, &b.receipt),
                Err(OutboxRefusal::StaleOrReplayedNullifier)
            );
            b.receipt.payload_len = 0;
            assert_eq!(
                v.check(&b.public_inputs, &b.challenge0, &b.receipt),
                Err(OutboxRefusal::PayloadLengthOutOfBounds)
            );
        }
    }

    #[test]
    fn cap30_cross_view_slot_signature_replay_is_rejected() {
        for alg in [OutboxHashAlg::Cshake256, OutboxHashAlg::Sha256] {
            let (mut v, mut b) =
                build_honest_outbox_fixture(alg, 5, 1, &[0, 1, 2, 3], 10, 0, 1, 2);
            // Populate active_views = 2 (`view = 2` in slot 0, distinct keys for `view = 3` in slot 1)
            v.committee.active_views = 2;
            let chain_v3 = [
                SimplexChainEntry::EmptyView { view: 1 },
                SimplexChainEntry::Block {
                    view: 3,
                    payload: b.receipt.fin_cert.tip_block().unwrap().1,
                },
            ];
            for (i, pk) in v.committee.slot_pubkeys[1].iter_mut().enumerate().take(5) {
                let salt_v3 = make_salt(i, 0x99);
                *pk =
                    derive_finalize_slot_pubkey(alg, i as u64, 3, &chain_v3, &salt_v3).unwrap();
            }
            // Re-pin actor_vk_digest & challenge0 to the 2-view committee, then try presenting
            // `view = 2` sig_salts against `view = 3`:
            b.public_inputs.actor_vk_digest = v.committee.directory_digest();
            b.effect_vk_digest = b.public_inputs.actor_vk_digest;
            b.challenge0 = b.public_inputs.transcript().squeeze();
            b.receipt.fin_cert.view = 3;
            b.receipt.fin_cert.chain[1] = chain_v3[1];
            assert_eq!(
                v.check(&b.public_inputs, &b.challenge0, &b.receipt),
                Err(OutboxRefusal::InvalidFinalizeSignature { signer_id: 0 })
            );
        }
    }
}
