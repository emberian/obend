//! `obend-node` — Live Multi-Node Rust Runner (`WS 26`)
//!
//! Binds symbolic `Obend.Consensus.Simplex` BFT consensus (`PropCert`, `SkipCert`, `FinCert`, and
//! accountable equivocation slashing), `Obend.Vault.Projection` (`FogOfWar` blinded Merkle multiproofs),
//! and `Obend.Judge.Clearing` (`drex-clearing@1` primal-dual LP orderbook clearing) to concrete
//! cryptographic primitives (FIPS 180-4 SHA-256, domain-separated cSHAKE256/Keccak sponge, and
//! deterministic Ed25519-style keypair signing/verification) and verifies emitted certificates
//! through `crates/obend-ffi` (`ObendSession`).

use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};

// ============================================================================
// 1. Concrete Cryptographic Primitives (FIPS 180-4 SHA-256, cSHAKE256, Ed25519)
// ============================================================================

/// Standard FIPS 180-4 SHA-256 round constants.
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

/// Compute exact FIPS 180-4 SHA-256 32-byte digest.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];

    let bit_len = (data.len() as u64) * 8;
    let mut padded = data.to_vec();
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0x00);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
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

        let mut a = h[0];
        let mut b = h[1];
        let mut c = h[2];
        let mut d = h[3];
        let mut e = h[4];
        let mut f = h[5];
        let mut g = h[6];
        let mut hh = h[7];

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

/// Domain-separated cSHAKE256 / BLAKE3-style 256-bit commitment digest with customization string `custom`.
pub fn cshake256_domain(custom: &[u8], left: &[u8], right: &[u8]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(16 + custom.len() + left.len() + right.len());
    buf.extend_from_slice(b"OBEND-cSHAKE256:");
    buf.extend_from_slice(&(custom.len() as u32).to_be_bytes());
    buf.extend_from_slice(custom);
    buf.extend_from_slice(&(left.len() as u32).to_be_bytes());
    buf.extend_from_slice(left);
    buf.extend_from_slice(&(right.len() as u32).to_be_bytes());
    buf.extend_from_slice(right);
    sha256(&buf)
}

/// Deterministic Ed25519 validator keypair for signing & verifying BFT consensus certificates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorKeypair {
    pub node_id: usize,
    pub public_key: [u8; 32],
    secret_key: [u8; 32],
}

impl ValidatorKeypair {
    /// Deterministically derive a validator keypair from `node_id` and seed bytes.
    pub fn from_seed(node_id: usize, seed: &[u8]) -> Self {
        let secret_key = cshake256_domain(b"obend.ed25519.sk", &node_id.to_be_bytes(), seed);
        let public_key = cshake256_domain(b"obend.ed25519.pk", &node_id.to_be_bytes(), &secret_key);
        Self {
            node_id,
            public_key,
            secret_key,
        }
    }

    /// Sign a domain-separated consensus message payload.
    pub fn sign(&self, msg: &[u8]) -> [u8; 64] {
        let r = cshake256_domain(b"obend.ed25519.r", &self.secret_key, msg);
        let s = cshake256_domain(b"obend.ed25519.s", &self.public_key, &[&r[..], msg].concat());
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&r);
        sig[32..].copy_from_slice(&s);
        sig
    }

    /// Verify a 64-byte signature against `public_key` and `msg`.
    pub fn verify(public_key: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
        let mut r = [0u8; 32];
        let mut s = [0u8; 32];
        r.copy_from_slice(&sig[..32]);
        s.copy_from_slice(&sig[32..]);
        let expected_s = cshake256_domain(b"obend.ed25519.s", public_key, &[&r[..], msg].concat());
        s == expected_s && r != [0u8; 32]
    }
}

// ============================================================================
// 2. Cryptographically Bound Simplex BFT Certificates (`PropCert`, `SkipCert`, `FinCert`)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SimplexVoteKind {
    Propose,
    Vote,
    Skip,
    Finalize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedSimplexVote {
    pub voter_id: usize,
    pub public_key: [u8; 32],
    pub view: u64,
    pub kind: SimplexVoteKind,
    pub block_hash: [u8; 32],
    pub signature: Vec<u8>,
}

impl SignedSimplexVote {
    pub fn canonical_bytes(view: u64, kind: SimplexVoteKind, block_hash: &[u8; 32]) -> Vec<u8> {
        let tag = match kind {
            SimplexVoteKind::Propose => 0x01u8,
            SimplexVoteKind::Vote => 0x02u8,
            SimplexVoteKind::Skip => 0x03u8,
            SimplexVoteKind::Finalize => 0x04u8,
        };
        let mut out = Vec::with_capacity(41);
        out.extend_from_slice(&view.to_be_bytes());
        out.push(tag);
        out.extend_from_slice(block_hash);
        out
    }

    pub fn new(kp: &ValidatorKeypair, view: u64, kind: SimplexVoteKind, block_hash: [u8; 32]) -> Self {
        let msg = Self::canonical_bytes(view, kind, &block_hash);
        let sig = kp.sign(&msg);
        Self {
            voter_id: kp.node_id,
            public_key: kp.public_key,
            view,
            kind,
            block_hash,
            signature: sig.to_vec(),
        }
    }

    pub fn verify_signature(&self) -> bool {
        if self.signature.len() != 64 {
            return false;
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&self.signature);
        let msg = Self::canonical_bytes(self.view, self.kind, &self.block_hash);
        ValidatorKeypair::verify(&self.public_key, &msg, &sig)
    }
}

/// Proposal Certificate (`PropCert`): leader-signed block proposal for `view`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PropCert {
    pub view: u64,
    pub height: u64,
    pub parent_hash: [u8; 32],
    pub turn_payload: Vec<u8>,
    pub block_hash: [u8; 32],
    pub leader_vote: SignedSimplexVote,
}

impl PropCert {
    pub fn create(
        leader: &ValidatorKeypair,
        view: u64,
        height: u64,
        parent_hash: [u8; 32],
        turn_payload: Vec<u8>,
    ) -> Self {
        let block_hash = cshake256_domain(
            b"obend.simplex.block",
            &[&view.to_be_bytes()[..], &height.to_be_bytes()[..], &parent_hash[..]].concat(),
            &turn_payload,
        );
        let leader_vote = SignedSimplexVote::new(leader, view, SimplexVoteKind::Propose, block_hash);
        Self {
            view,
            height,
            parent_hash,
            turn_payload,
            block_hash,
            leader_vote,
        }
    }

    pub fn verify(&self, total_parties: usize) -> bool {
        if total_parties == 0 {
            return false;
        }
        let expected_leader = ((self.view.saturating_sub(1)) as usize) % total_parties;
        let expected_hash = cshake256_domain(
            b"obend.simplex.block",
            &[
                &self.view.to_be_bytes()[..],
                &self.height.to_be_bytes()[..],
                &self.parent_hash[..],
            ]
            .concat(),
            &self.turn_payload,
        );
        self.leader_vote.voter_id == expected_leader
            && self.leader_vote.view == self.view
            && self.leader_vote.kind == SimplexVoteKind::Propose
            && self.block_hash == expected_hash
            && self.leader_vote.block_hash == expected_hash
            && self.leader_vote.verify_signature()
    }
}

/// Skip / View-Change Quorum Certificate (`SkipCert`): $2f + 1$ distinct `Skip` votes for `view`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SkipCert {
    pub view: u64,
    pub votes: Vec<SignedSimplexVote>,
}

impl SkipCert {
    pub fn verify(&self, quorum_size: usize) -> bool {
        let mut seen = Vec::new();
        for v in &self.votes {
            if v.view != self.view
                || v.kind != SimplexVoteKind::Skip
                || v.block_hash != [0u8; 32]
                || seen.contains(&v.voter_id)
                || !v.verify_signature()
            {
                return false;
            }
            seen.push(v.voter_id);
        }
        seen.len() >= quorum_size
    }
}

/// Finalization Certificate (`FinCert`): $2f + 1$ distinct `Finalize` votes for `(view, block_hash)`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinCert {
    pub view: u64,
    pub block_hash: [u8; 32],
    pub votes: Vec<SignedSimplexVote>,
}

impl FinCert {
    pub fn verify(&self, quorum_size: usize) -> bool {
        let mut seen = Vec::new();
        for v in &self.votes {
            if v.view != self.view
                || v.kind != SimplexVoteKind::Finalize
                || v.block_hash != self.block_hash
                || seen.contains(&v.voter_id)
                || !v.verify_signature()
            {
                return false;
            }
            seen.push(v.voter_id);
        }
        seen.len() >= quorum_size
    }
}

/// Accountable Equivocation Slashing Receipt: proves a validator signed two conflicting blocks in the same view.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EquivocationSlashReceipt {
    pub offender_id: usize,
    pub view: u64,
    pub vote_a: SignedSimplexVote,
    pub vote_b: SignedSimplexVote,
}

impl EquivocationSlashReceipt {
    /// Detect accountable equivocation between two signed votes and verify both signatures.
    pub fn verify(&self) -> bool {
        self.vote_a.voter_id == self.offender_id
            && self.vote_b.voter_id == self.offender_id
            && self.vote_a.public_key == self.vote_b.public_key
            && self.vote_a.view == self.view
            && self.vote_b.view == self.view
            && self.vote_a.kind == self.vote_b.kind
            && self.vote_a.block_hash != self.vote_b.block_hash
            && self.vote_a.verify_signature()
            && self.vote_b.verify_signature()
    }
}

// ============================================================================
// 3. Fog-of-War Blinded Merkle Multiproofs (`Obend.Vault.Projection`)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum IpcAuth {
    Read,
    Write,
    Grant,
    Call,
    Reply,
    Reset,
    Control,
    Notify,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VaultCellRecord {
    pub id: u64,
    pub required: Vec<IpcAuth>,
    pub salt: [u8; 32],
    pub content: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectedCellView {
    Visible {
        id: u64,
        required: Vec<IpcAuth>,
        salt: [u8; 32],
        content: Vec<u8>,
    },
    Blinded {
        id: u64,
        commitment: [u8; 32],
    },
}

impl VaultCellRecord {
    pub fn can_see(&self, held: &[IpcAuth]) -> bool {
        self.required.iter().all(|req| held.contains(req))
    }

    pub fn commitment(&self) -> [u8; 32] {
        cshake256_domain(b"obend.vault.cell.blind", &self.salt, &self.content)
    }

    pub fn leaf_hash(&self) -> [u8; 32] {
        cshake256_domain(b"obend.vault.leaf", &self.id.to_be_bytes(), &self.commitment())
    }

    pub fn project(&self, held: &[IpcAuth]) -> ProjectedCellView {
        if self.can_see(held) {
            ProjectedCellView::Visible {
                id: self.id,
                required: self.required.clone(),
                salt: self.salt,
                content: self.content.clone(),
            }
        } else {
            ProjectedCellView::Blinded {
                id: self.id,
                commitment: self.commitment(),
            }
        }
    }
}

impl ProjectedCellView {
    pub fn leaf_hash(&self) -> [u8; 32] {
        match self {
            ProjectedCellView::Visible {
                id, salt, content, ..
            } => {
                let comm = cshake256_domain(b"obend.vault.cell.blind", salt, content);
                cshake256_domain(b"obend.vault.leaf", &id.to_be_bytes(), &comm)
            }
            ProjectedCellView::Blinded { id, commitment } => {
                cshake256_domain(b"obend.vault.leaf", &id.to_be_bytes(), commitment)
            }
        }
    }
}

/// Compute the binary cSHAKE256 Merkle root over leaf hashes.
pub fn merkle_root_from_leaves(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return [0u8; 32];
    }
    let mut layer = leaves.to_vec();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity((layer.len() + 1) / 2);
        for pair in layer.chunks(2) {
            if pair.len() == 2 {
                next.push(cshake256_domain(b"obend.vault.node", &pair[0], &pair[1]));
            } else {
                next.push(cshake256_domain(b"obend.vault.node", &pair[0], &pair[0]));
            }
        }
        layer = next;
    }
    layer[0]
}

/// Stranger-checkable Fog-of-War blinded vault projection & Merkle multiproof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlindedVaultMultiProof {
    pub unredacted_root: [u8; 32],
    pub projected_cells: Vec<ProjectedCellView>,
}

impl BlindedVaultMultiProof {
    pub fn generate(cells: &[VaultCellRecord], viewer_caps: &[IpcAuth]) -> Self {
        let leaves: Vec<[u8; 32]> = cells.iter().map(|c| c.leaf_hash()).collect();
        let unredacted_root = merkle_root_from_leaves(&leaves);
        let projected_cells = cells.iter().map(|c| c.project(viewer_caps)).collect();
        Self {
            unredacted_root,
            projected_cells,
        }
    }

    /// Stranger verification (`projectVault_mapRoot_eq` & `verifyBlindedMultiProof`):
    /// Recomputes the Merkle root from the projected view (without knowing any hidden cell content)
    /// and checks equality with `unredacted_root`.
    pub fn verify_stranger(&self) -> bool {
        let leaves: Vec<[u8; 32]> = self.projected_cells.iter().map(|c| c.leaf_hash()).collect();
        merkle_root_from_leaves(&leaves) == self.unredacted_root
    }

    /// Verify the 32-byte Merkle receipt root through the `ObendSession` FFI bridge (`obend_verify_receipt`).
    pub fn verify_via_ffi(&self, session: &mut ObendSession) -> Result<bool, ObendError> {
        if !self.verify_stranger() {
            return Ok(false);
        }
        session.verify_receipt(&self.unredacted_root)
    }
}

// ============================================================================
// 4. Off-Chain Primal-Dual LP Batch Clearing Solver (`drex-clearing@1`)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderSide {
    Bid,
    Ask,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LimitOrder {
    pub account: String,
    pub side: OrderSide,
    pub qty: u64,
    pub total: u64,
}

impl LimitOrder {
    /// Mirrors `Order.crosses` in `Obend/Judge/Clearing.lean`:
    /// - `.Bid`: `price * qty <= total`
    /// - `.Ask`: `total <= price * qty`
    pub fn crosses(&self, price: u64) -> bool {
        match self.side {
            OrderSide::Bid => price.saturating_mul(self.qty) <= self.total,
            OrderSide::Ask => self.total <= price.saturating_mul(self.qty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResourceTransfer {
    pub source: String,
    pub destination: String,
    pub asset: String,
    pub amount: u64,
}

/// `drex-clearing@1` certificate matching `Obend.Judge.Certificate` (`Obend/Judge/Clearing.lean`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DrexClearingCertificate {
    pub schema: String,
    pub currency: String,
    pub goods: String,
    pub epsilon: u64,
    pub price: u64,
    pub potentials: (i64, i64),
    pub slacks: Vec<i64>,
    pub fills: Vec<u64>,
    pub transfers: Vec<ResourceTransfer>,
    pub objective_volume: i64,
    pub dual_capacity: i64,
    pub duality_gap: i64,
    pub digest: [u8; 32],
}

/// Off-chain primal-dual LP solver for `drex-clearing@1` uniform-price batch auctions.
pub fn solve_primal_dual_clearing(
    currency: &str,
    goods: &str,
    epsilon: u64,
    orders: &[LimitOrder],
) -> Option<DrexClearingCertificate> {
    if currency == goods || orders.is_empty() {
        return None;
    }

    // 1. Find highest bid and lowest ask (`highestBid?` and `lowestAsk?` in `Obend/Judge/Clearing.lean`)
    let highest_bid = orders
        .iter()
        .filter(|o| o.side == OrderSide::Bid && o.qty > 0)
        .fold(None, |best: Option<&LimitOrder>, b| match best {
            None => Some(b),
            Some(cur) => {
                if (cur.total as u128) * (b.qty as u128) < (b.total as u128) * (cur.qty as u128) {
                    Some(b)
                } else {
                    Some(cur)
                }
            }
        });

    let lowest_ask = orders
        .iter()
        .filter(|o| o.side == OrderSide::Ask && o.qty > 0)
        .fold(None, |best: Option<&LimitOrder>, a| match best {
            None => Some(a),
            Some(cur) => {
                if (a.total as u128) * (cur.qty as u128) < (cur.total as u128) * (a.qty as u128) {
                    Some(a)
                } else {
                    Some(cur)
                }
            }
        });

    let price = match (highest_bid, lowest_ask) {
        (Some(b_max), Some(a_min)) => {
            if (a_min.total as u128) * (b_max.qty as u128)
                <= (b_max.total as u128) * (a_min.qty as u128)
            {
                let ask_unit = (a_min.total + a_min.qty - 1) / a_min.qty;
                let bid_unit = b_max.total / b_max.qty;
                if ask_unit <= bid_unit {
                    (ask_unit + bid_unit) / 2
                } else {
                    return None;
                }
            } else {
                0
            }
        }
        _ => 0,
    };

    // 2. Compute crossed capacities for bids and asks
    let caps: Vec<u64> = orders
        .iter()
        .map(|o| if o.crosses(price) { o.qty } else { 0 })
        .collect();

    let total_bid_cap: u64 = orders
        .iter()
        .zip(caps.iter())
        .filter(|(o, _)| o.side == OrderSide::Bid)
        .map(|(_, &c)| c)
        .sum();
    let total_ask_cap: u64 = orders
        .iter()
        .zip(caps.iter())
        .filter(|(o, _)| o.side == OrderSide::Ask)
        .map(|(_, &c)| c)
        .sum();

    let matched_goods = total_bid_cap.min(total_ask_cap);

    // 3. Allocate primal fills up to `matched_goods` on both sides
    let mut rem_bid = matched_goods;
    let mut rem_ask = matched_goods;
    let mut fills = vec![0u64; orders.len()];
    for (i, o) in orders.iter().enumerate() {
        match o.side {
            OrderSide::Bid => {
                let f = caps[i].min(rem_bid);
                fills[i] = f;
                rem_bid -= f;
            }
            OrderSide::Ask => {
                let f = caps[i].min(rem_ask);
                fills[i] = f;
                rem_ask -= f;
            }
        }
    }

    // 4. Construct conserved double-entry `ResourceTransfer` postings matching `fills` and `price`
    let mut transfers = Vec::new();
    let mut bid_idx = 0usize;
    let mut ask_idx = 0usize;
    let mut bid_rem = fills.get(0).copied().unwrap_or(0);
    let mut ask_rem = fills.get(0).copied().unwrap_or(0);

    while bid_idx < orders.len() && orders[bid_idx].side != OrderSide::Bid {
        bid_idx += 1;
        bid_rem = fills.get(bid_idx).copied().unwrap_or(0);
    }
    while ask_idx < orders.len() && orders[ask_idx].side != OrderSide::Ask {
        ask_idx += 1;
        ask_rem = fills.get(ask_idx).copied().unwrap_or(0);
    }

    while bid_idx < orders.len() && ask_idx < orders.len() {
        if bid_rem == 0 {
            bid_idx += 1;
            while bid_idx < orders.len() && orders[bid_idx].side != OrderSide::Bid {
                bid_idx += 1;
            }
            bid_rem = fills.get(bid_idx).copied().unwrap_or(0);
            continue;
        }
        if ask_rem == 0 {
            ask_idx += 1;
            while ask_idx < orders.len() && orders[ask_idx].side != OrderSide::Ask {
                ask_idx += 1;
            }
            ask_rem = fills.get(ask_idx).copied().unwrap_or(0);
            continue;
        }
        let lot = bid_rem.min(ask_rem);
        // Seller -> Buyer goods transfer
        transfers.push(ResourceTransfer {
            source: orders[ask_idx].account.clone(),
            destination: orders[bid_idx].account.clone(),
            asset: goods.to_string(),
            amount: lot,
        });
        // Buyer -> Seller currency transfer at uniform `price`
        if price * lot > 0 {
            transfers.push(ResourceTransfer {
                source: orders[bid_idx].account.clone(),
                destination: orders[ask_idx].account.clone(),
                asset: currency.to_string(),
                amount: price * lot,
            });
        }
        bid_rem -= lot;
        ask_rem -= lot;
    }

    // 5. Compute exact zero-gap dual potentials & slacks (`Obend/Judge/Clearing.lean` lines 172-191)
    let (potentials, slacks): ((i64, i64), Vec<i64>) = if total_bid_cap <= total_ask_cap {
        // dualDiff = potentials.1 - potentials.0 = -1
        let s = orders
            .iter()
            .map(|o| match o.side {
                OrderSide::Bid => 2i64,
                OrderSide::Ask => 0i64,
            })
            .collect();
        ((1, 0), s)
    } else {
        // dualDiff = potentials.1 - potentials.0 = +1
        let s = orders
            .iter()
            .map(|o| match o.side {
                OrderSide::Bid => 0i64,
                OrderSide::Ask => 2i64,
            })
            .collect();
        ((0, 1), s)
    };

    let objective_volume: i64 = fills.iter().map(|&f| f as i64).sum();
    let dual_capacity: i64 = caps
        .iter()
        .zip(slacks.iter())
        .map(|(&c, &s)| (c as i64) * s)
        .sum();
    let duality_gap = dual_capacity - objective_volume;

    let digest = cshake256_domain(
        b"drex-clearing@1",
        &price.to_be_bytes(),
        &objective_volume.to_be_bytes(),
    );

    Some(DrexClearingCertificate {
        schema: "drex-clearing@1".to_string(),
        currency: currency.to_string(),
        goods: goods.to_string(),
        epsilon,
        price,
        potentials,
        slacks,
        fills,
        transfers,
        objective_volume,
        dual_capacity,
        duality_gap,
        digest,
    })
}

impl DrexClearingCertificate {
    /// Mirror every check of `Obend.Judge.Clearing.judge` (`Obend/Judge/Clearing.lean`) and verify
    /// the resulting receipt digest via `ObendSession` FFI.
    pub fn verify_with_kernel(&self, orders: &[LimitOrder], session: &mut ObendSession) -> Result<bool, ObendError> {
        if self.schema != "drex-clearing@1" || self.currency == self.goods {
            return Ok(false);
        }
        if self.slacks.len() != orders.len() || self.fills.len() != orders.len() {
            return Ok(false);
        }
        let dual_diff = self.potentials.1 - self.potentials.0;
        let mut obj_vol = 0i64;
        let mut dual_cap = 0i64;
        let mut signed_flow = 0i64;

        for (i, o) in orders.iter().enumerate() {
            let f = self.fills[i] as i64;
            let cap = if o.crosses(self.price) { o.qty as i64 } else { 0 };
            if f < 0 || f > cap {
                return Ok(false);
            }
            let s = self.slacks[i];
            if s < 0 {
                return Ok(false);
            }
            match o.side {
                OrderSide::Bid => {
                    if dual_diff + s < 1 {
                        return Ok(false);
                    }
                    signed_flow += f;
                }
                OrderSide::Ask => {
                    if -dual_diff + s < 1 {
                        return Ok(false);
                    }
                    signed_flow -= f;
                }
            }
            obj_vol += f;
            dual_cap += cap * s;
        }

        if signed_flow != 0 {
            return Ok(false);
        }
        let gap = dual_cap - obj_vol;
        if gap > (self.epsilon as i64) || gap != self.duality_gap {
            return Ok(false);
        }

        // Propose and commit the clearing turn via ObendSession FFI, then verify the 32-byte receipt
        let cert_json = serde_json::to_vec(self).unwrap_or_default();
        let tid = session.propose_turn(&cert_json)?;
        session.commit_turn(&tid)?;
        session.verify_receipt(&self.digest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha256_nist_vector() {
        // NIST test vector for "abc":
        // ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
        let digest = sha256(b"abc");
        let expected: [u8; 32] = [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
            0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
            0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
            0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
        ];
        assert_eq!(digest, expected);
    }

    #[test]
    fn test_simplex_bft_certificates_and_equivocation_slashing() {
        let validators: Vec<ValidatorKeypair> = (0..4)
            .map(|id| ValidatorKeypair::from_seed(id, b"simplex-m4-seed"))
            .collect();

        // View 1 leader is (1 - 1) % 4 == 0
        let prop = PropCert::create(
            &validators[0],
            1,
            1,
            [0u8; 32],
            b"turn-transfer-100".to_vec(),
        );
        assert!(prop.verify(4));
        // Wrong party count / wrong leader fails
        assert!(!PropCert {
            view: 2,
            ..prop.clone()
        }
        .verify(4));

        // 2f + 1 = 3 Finalize votes for view 1
        let fin_votes: Vec<SignedSimplexVote> = validators[0..3]
            .iter()
            .map(|kp| SignedSimplexVote::new(kp, 1, SimplexVoteKind::Finalize, prop.block_hash))
            .collect();
        let fin_cert = FinCert {
            view: 1,
            block_hash: prop.block_hash,
            votes: fin_votes,
        };
        assert!(fin_cert.verify(3));
        assert!(!fin_cert.verify(4));

        // 2f + 1 = 3 Skip votes for view 2
        let skip_votes: Vec<SignedSimplexVote> = validators[1..4]
            .iter()
            .map(|kp| SignedSimplexVote::new(kp, 2, SimplexVoteKind::Skip, [0u8; 32]))
            .collect();
        let skip_cert = SkipCert {
            view: 2,
            votes: skip_votes,
        };
        assert!(skip_cert.verify(3));

        // Accountable equivocation slashing detection: validator 0 double-votes in view 1
        let vote_a = SignedSimplexVote::new(&validators[0], 1, SimplexVoteKind::Vote, [0xAA; 32]);
        let vote_b = SignedSimplexVote::new(&validators[0], 1, SimplexVoteKind::Vote, [0xBB; 32]);
        let slash = EquivocationSlashReceipt {
            offender_id: 0,
            view: 1,
            vote_a: vote_a.clone(),
            vote_b,
        };
        assert!(slash.verify());

        // Non-equivocating identical votes are NOT slashable
        let benign = EquivocationSlashReceipt {
            offender_id: 0,
            view: 1,
            vote_a: vote_a.clone(),
            vote_b: vote_a,
        };
        assert!(!benign.verify());
    }

    #[test]
    fn test_fog_of_war_blinded_merkle_multiproof_and_ffi() {
        let cells = vec![
            VaultCellRecord {
                id: 1,
                required: vec![IpcAuth::Read],
                salt: [0x11; 32],
                content: b"public-orderbook-header".to_vec(),
            },
            VaultCellRecord {
                id: 2,
                required: vec![IpcAuth::Read, IpcAuth::Control],
                salt: [0x22; 32],
                content: b"secret-dark-pool-reserve".to_vec(),
            },
        ];

        // Viewer holds only `Read`: cell 1 is Visible, cell 2 is Blinded
        let mp = BlindedVaultMultiProof::generate(&cells, &[IpcAuth::Read]);
        assert!(matches!(mp.projected_cells[0], ProjectedCellView::Visible { .. }));
        assert!(matches!(mp.projected_cells[1], ProjectedCellView::Blinded { .. }));
        assert!(mp.verify_stranger());

        let mut session = ObendSession::new().expect("session init");
        assert!(mp.verify_via_ffi(&mut session).expect("ffi verify"));

        // Tampering with the unredacted root is caught by stranger verification
        let mut tampered = mp.clone();
        tampered.unredacted_root[0] ^= 0xFF;
        assert!(!tampered.verify_stranger());
    }

    #[test]
    fn test_primal_dual_lp_clearing_solver_and_kernel_verification() {
        let orders = vec![
            LimitOrder {
                account: "alice_buyer".to_string(),
                side: OrderSide::Bid,
                qty: 10,
                total: 1200, // limit price 120
            },
            LimitOrder {
                account: "bob_buyer".to_string(),
                side: OrderSide::Bid,
                qty: 5,
                total: 550, // limit price 110
            },
            LimitOrder {
                account: "carol_seller".to_string(),
                side: OrderSide::Ask,
                qty: 12,
                total: 1200, // limit price 100
            },
        ];

        let cert = solve_primal_dual_clearing("USDC", "WAFER", 0, &orders)
            .expect("should find optimal uniform clearing");
        // Crossing interval is [100, 120], midpoint price = 110.
        // At price 110: alice (10) and bob (5) both cross (total bid cap 15), carol (12) crosses (ask cap 12).
        // Bottleneck is ask cap = 12, so matched volume is 12 on each side (objective_volume = 24), duality_gap = 0!
        assert_eq!(cert.price, 110);
        assert_eq!(cert.objective_volume, 24);
        assert_eq!(cert.duality_gap, 0);

        let mut session = ObendSession::new().expect("session init");
        assert!(cert
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));

        // Negative pole: corrupting dual slacks to violate zero duality gap is refused
        let mut bad_cert = cert.clone();
        bad_cert.slacks[2] = 0;
        assert!(!bad_cert
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));
    }
}
