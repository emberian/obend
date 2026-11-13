//! 2-Round post-quantum commit-and-open dealerless DKG (`Π_deg`, `"OBEND.PQ.DKG.COMMIT/v1"`),
//! constant-PK proactive share refresh (`Π_deg0`, preserving `PK = (pk_seed, pk_root)` bit-for-bit),
//! and Simplex monotonic persist-before-sign `EpochLatch` (`2 t_latch - n > f` anti-double-sign safety).
//!
//! Matches `Obend.Crypto.ThresholdHashMpc` §4–§5 byte-for-byte.

#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

use alloc::vec;
use alloc::vec::Vec;

use obend_crypto_exec::goldilocks::{Goldilocks, GoldilocksExt2};
use obend_crypto_exec::transcript::FenziTranscript;

use crate::adrs_tsw::{cshake256_hash32, encode_multi_frame};
use crate::keccak_mpc::{MpcCsprng, ShamirSeedShare256, TowerGf256, eval_poly_gf256};
use crate::poseidon2_mpc::{
    ShamirPoseidonSeedShare, eval_poly_goldilocks, lagrange_weights_zero_goldilocks,
};

/// Canonical domain customization tag matching `Obend.Crypto.ThresholdHashMpc.tagDkgCommit`.
pub const TAG_DKG_COMMIT: &[u8] = b"OBEND.PQ.DKG.COMMIT/v1";

/// Round-1 PQ share commitment `cSHAKE256("OBEND.PQ.DKG.COMMIT/v1", encodeMultiFrame [be4(dealer), be4(recv), salt, share_bytes])`,
/// matching `ThresholdHashMpc.dkgCommitShare` byte-for-byte!
#[inline]
pub fn dkg_commit_share(dealer: u32, recv: u32, salt: &[u8], share_bytes: &[u8]) -> [u8; 32] {
    let d_be = dealer.to_be_bytes();
    let r_be = recv.to_be_bytes();
    let frame = encode_multi_frame(&[&d_be, &r_be, salt, share_bytes]);
    cshake256_hash32(TAG_DKG_COMMIT, &frame)
}

/// Public `Π_deg` Reed–Solomon degree-`< t` consistency check over `Goldilocks`
/// (`ThresholdHashMpc.checkReedSolomonDegLtT`).
pub fn check_reed_solomon_deg_lt_t_goldilocks(
    t: usize,
    pts: &[Goldilocks],
    coeffs: &[Goldilocks],
    evals: &[Goldilocks],
) -> bool {
    if coeffs.len() > t || pts.len() != evals.len() {
        return false;
    }
    pts.iter()
        .zip(evals.iter())
        .all(|(&x, &y)| eval_poly_goldilocks(coeffs, x) == y)
}

/// Public `Π_deg` Reed–Solomon degree-`< t` consistency check over `TowerGf256` ($\mathcal{T}_3$).
pub fn check_reed_solomon_deg_lt_t_gf256(
    t: usize,
    pts: &[TowerGf256],
    coeffs: &[TowerGf256],
    evals: &[TowerGf256],
) -> bool {
    if coeffs.len() > t || pts.len() != evals.len() {
        return false;
    }
    pts.iter()
        .zip(evals.iter())
        .all(|(&x, &y)| eval_poly_gf256(coeffs, x) == y)
}

/// Public `Π_deg0` zero-constant proactive refresh check over `Goldilocks` (`p(0) == 0`).
pub fn check_zero_constant_refresh_goldilocks(
    t: usize,
    pts: &[Goldilocks],
    refresh_coeffs: &[Goldilocks],
    refresh_shares: &[Goldilocks],
) -> bool {
    check_reed_solomon_deg_lt_t_goldilocks(t, pts, refresh_coeffs, refresh_shares)
        && eval_poly_goldilocks(refresh_coeffs, Goldilocks::ZERO) == Goldilocks::ZERO
}

/// Public `Π_deg0` zero-constant proactive refresh check over `TowerGf256` (`p(0) == 0`).
pub fn check_zero_constant_refresh_gf256(
    t: usize,
    pts: &[TowerGf256],
    refresh_coeffs: &[TowerGf256],
    refresh_shares: &[TowerGf256],
) -> bool {
    check_reed_solomon_deg_lt_t_gf256(t, pts, refresh_coeffs, refresh_shares)
        && eval_poly_gf256(refresh_coeffs, TowerGf256::ZERO) == TowerGf256::ZERO
}

/// Evaluate polynomial `coeffs[0] + coeffs[1] * x + ...` over 128-bit `GoldilocksExt2` at base-field point `x`.
#[inline]
pub fn eval_poly_ext2_at_base(coeffs: &[GoldilocksExt2], x: Goldilocks) -> GoldilocksExt2 {
    let xb = GoldilocksExt2::from_base(x);
    let mut acc = GoldilocksExt2::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc * xb + c;
    }
    acc
}

/// Public complaint filed by recipient `recv_idx` against dealer `dealer_idx` in Round 1 of PQ DKG.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgShareComplaint {
    pub recv_idx: usize,
    pub committed_digest: [u8; 32],
    pub dealer_opened_salt: Vec<u8>,
    /// 24-byte canonical opening `f_j (8 B) || m_j.c0 (8 B) || m_j.c1 (8 B)`.
    pub dealer_opened_share_bytes: Vec<u8>,
}

/// Point-to-point private share packet sent exclusively from `dealer_idx` to `recv_idx` in Round 1
/// (NEVER included in the public broadcast struct!).
#[derive(Clone, PartialEq, Eq)]
pub struct DkgPrivateSharePacket {
    pub recv_idx: usize,
    pub f_share: Goldilocks,
    pub m_share: GoldilocksExt2,
    pub salt: [u8; 32],
}

impl core::fmt::Debug for DkgPrivateSharePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DkgPrivateSharePacket")
            .field("recv_idx", &self.recv_idx)
            .field("f_share", &"<redacted>")
            .field("m_share", &"<redacted>")
            .field("salt", &"<redacted>")
            .finish()
    }
}

impl Drop for DkgPrivateSharePacket {
    fn drop(&mut self) {
        self.f_share = Goldilocks::ZERO;
        self.m_share = GoldilocksExt2::ZERO;
        self.salt.fill(0);
        core::hint::black_box(&self.f_share);
        core::hint::black_box(&self.m_share);
        core::hint::black_box(&self.salt);
    }
}

impl DkgPrivateSharePacket {
    #[inline]
    pub fn encode_share_bytes(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[0..8].copy_from_slice(&self.f_share.to_be_bytes());
        out[8..16].copy_from_slice(&self.m_share.c0.to_be_bytes());
        out[16..24].copy_from_slice(&self.m_share.c1.to_be_bytes());
        out
    }
}

/// Public broadcast by dealer `dealer_idx` in 2-round PQ dealerless DKG (`Π_deg`) over `GoldilocksExt2` (128-bit soundness):
/// - Round 1 commits `share_commitments[0..n]` AND `pk_seed_commitment` (eliminating rushing-dealer `pk_seed` bias);
/// - Round 2 opens `masked_poly_coeffs` (`P(X) = chal * f(X) + m(X)` over `GoldilocksExt2`) and `(pk_seed_contrib, pk_seed_salt)`.
/// - Private share packets `DkgPrivateSharePacket` travel strictly on authenticated point-to-point channels!
#[derive(Clone, Debug)]
pub struct GoldilocksDealerBroadcast {
    pub dealer_idx: usize,
    pub share_commitments: Vec<[u8; 32]>,
    pub pk_seed_commitment: [u8; 32],
    /// Masked polynomial `P(X) = chal * f(X) + m(X)` of degree `< t` over 128-bit `GoldilocksExt2`.
    pub masked_poly_coeffs: Vec<GoldilocksExt2>,
    /// Round-2 opening of `(pk_seed_contrib, pk_seed_salt)` matching Round-1 `pk_seed_commitment`.
    pub pk_seed_contrib: [u8; 32],
    pub pk_seed_salt: [u8; 32],
}

impl GoldilocksDealerBroadcast {
    /// Construct an honest `Π_deg` dealing returning `(public_broadcast, private_p2p_packets)`.
    pub fn generate_honest(
        dealer_idx: usize,
        t: usize,
        pts: &[Goldilocks],
        f_coeffs: &[Goldilocks],
        m_coeffs: &[GoldilocksExt2],
        salts: &[[u8; 32]],
        pk_seed_contrib: [u8; 32],
        pk_seed_salt: [u8; 32],
    ) -> (Self, Vec<DkgPrivateSharePacket>) {
        assert!(
            t > 0
                && f_coeffs.len() <= t
                && m_coeffs.len() <= t
                && pts.len() >= t
                && pts.len() == salts.len()
        );
        let n = pts.len();
        let pk_seed_commitment =
            dkg_commit_share(dealer_idx as u32, u32::MAX, &pk_seed_salt, &pk_seed_contrib);
        let mut share_commitments = Vec::with_capacity(n);
        let mut private_packets = Vec::with_capacity(n);

        for j in 0..n {
            let fj = eval_poly_goldilocks(f_coeffs, pts[j]);
            let mj = eval_poly_ext2_at_base(m_coeffs, pts[j]);
            let pkt = DkgPrivateSharePacket {
                recv_idx: j,
                f_share: fj,
                m_share: mj,
                salt: salts[j],
            };
            let pkt_bytes = pkt.encode_share_bytes();
            let comm = dkg_commit_share(dealer_idx as u32, j as u32, &salts[j], &pkt_bytes);
            share_commitments.push(comm);
            private_packets.push(pkt);
        }

        let chal =
            derive_dkg_transcript_challenge(dealer_idx, &pk_seed_commitment, &share_commitments);
        let deg_len = f_coeffs.len().max(m_coeffs.len());
        let mut masked_poly_coeffs = Vec::with_capacity(deg_len);
        for k in 0..deg_len {
            let fk = f_coeffs.get(k).copied().unwrap_or(Goldilocks::ZERO);
            let mk = m_coeffs.get(k).copied().unwrap_or(GoldilocksExt2::ZERO);
            masked_poly_coeffs.push(chal * GoldilocksExt2::from_base(fk) + mk);
        }

        (
            Self {
                dealer_idx,
                share_commitments,
                pk_seed_commitment,
                masked_poly_coeffs,
                pk_seed_contrib,
                pk_seed_salt,
            },
            private_packets,
        )
    }
}

/// Squeeze full 128-bit `GoldilocksExt2` `FenziTranscript` challenge bound to `(dealer_idx, pk_seed_commitment, share_commitments)`.
pub fn derive_dkg_transcript_challenge(
    dealer_idx: usize,
    pk_seed_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
) -> GoldilocksExt2 {
    let mut flat = Vec::with_capacity(40 + 32 * share_commitments.len());
    flat.extend_from_slice(&(dealer_idx as u64).to_be_bytes());
    flat.extend_from_slice(pk_seed_commitment);
    for c in share_commitments {
        flat.extend_from_slice(c);
    }
    let seed_digest = cshake256_hash32(TAG_DKG_COMMIT, &flat);
    let mut tr = FenziTranscript::new(TAG_DKG_COMMIT)
        .bind_relation(
            "OBEND.PQ.DKG.COMMIT/v1",
            &seed_digest,
            &(dealer_idx as u64).to_be_bytes(),
        )
        .bind_instance(&flat, GoldilocksExt2::ZERO, &[]);
    tr.squeeze_ext2()
}

/// Recipient-side local verification of private `DkgPrivateSharePacket` against the public `GoldilocksDealerBroadcast`.
/// If this returns `false`, recipient broadcasts a `DkgShareComplaint` forcing public dealer opening or disqualification!
pub fn verify_dkg_private_packet_goldilocks(
    pts: &[Goldilocks],
    dealing: &GoldilocksDealerBroadcast,
    packet: &DkgPrivateSharePacket,
) -> bool {
    if packet.recv_idx >= pts.len() || dealing.share_commitments.len() != pts.len() {
        return false;
    }
    let pkt_bytes = packet.encode_share_bytes();
    let comm = dkg_commit_share(
        dealing.dealer_idx as u32,
        packet.recv_idx as u32,
        &packet.salt,
        &pkt_bytes,
    );
    if comm != dealing.share_commitments[packet.recv_idx] {
        return false;
    }
    let chal = derive_dkg_transcript_challenge(
        dealing.dealer_idx,
        &dealing.pk_seed_commitment,
        &dealing.share_commitments,
    );
    let expected = eval_poly_ext2_at_base(&dealing.masked_poly_coeffs, pts[packet.recv_idx]);
    chal * GoldilocksExt2::from_base(packet.f_share) + packet.m_share == expected
}

/// Publicly qualify or disqualify a dealer in 2-round PQ dealerless DKG (`Π_deg`), verifying:
/// 1. `0 < t <= pts.len()` and `pts` are non-zero & pairwise distinct (`lagrange_weights_zero_goldilocks(pts).is_some()`);
/// 2. Round-2 `(pk_seed_contrib, pk_seed_salt)` matches Round-1 `pk_seed_commitment`;
/// 3. `masked_poly_coeffs` has degree `< t` across both `GoldilocksExt2` limbs (`c0, c1`);
/// 4. Every filed `DkgShareComplaint` has a valid 24-byte canonical opening consistent with `C_{i,j}` and `P_i(x_j)`.
pub fn verify_and_qualify_dkg_dealer_goldilocks(
    t: usize,
    pts: &[Goldilocks],
    dealing: &GoldilocksDealerBroadcast,
    complaints: &[DkgShareComplaint],
) -> bool {
    let n = pts.len();
    if t == 0
        || t > n
        || dealing.share_commitments.len() != n
        || dealing.masked_poly_coeffs.len() > t
        || lagrange_weights_zero_goldilocks(pts).is_none()
    {
        return false;
    }
    let expected_pk_comm = dkg_commit_share(
        dealing.dealer_idx as u32,
        u32::MAX,
        &dealing.pk_seed_salt,
        &dealing.pk_seed_contrib,
    );
    if expected_pk_comm != dealing.pk_seed_commitment {
        return false;
    }

    let c0_coeffs: Vec<Goldilocks> = dealing.masked_poly_coeffs.iter().map(|c| c.c0).collect();
    let c1_coeffs: Vec<Goldilocks> = dealing.masked_poly_coeffs.iter().map(|c| c.c1).collect();
    let c0_evals: Vec<Goldilocks> = pts
        .iter()
        .map(|&x| eval_poly_goldilocks(&c0_coeffs, x))
        .collect();
    let c1_evals: Vec<Goldilocks> = pts
        .iter()
        .map(|&x| eval_poly_goldilocks(&c1_coeffs, x))
        .collect();
    if !check_reed_solomon_deg_lt_t_goldilocks(t, pts, &c0_coeffs, &c0_evals)
        || !check_reed_solomon_deg_lt_t_goldilocks(t, pts, &c1_coeffs, &c1_evals)
    {
        return false;
    }

    let chal = derive_dkg_transcript_challenge(
        dealing.dealer_idx,
        &dealing.pk_seed_commitment,
        &dealing.share_commitments,
    );

    for comp in complaints {
        if comp.recv_idx >= n || comp.dealer_opened_share_bytes.len() != 24 {
            return false;
        }
        let comm = dkg_commit_share(
            dealing.dealer_idx as u32,
            comp.recv_idx as u32,
            &comp.dealer_opened_salt,
            &comp.dealer_opened_share_bytes,
        );
        if comm != comp.committed_digest || comm != dealing.share_commitments[comp.recv_idx] {
            return false;
        }
        let Ok(f_open) = Goldilocks::from_be_bytes_canonical(
            comp.dealer_opened_share_bytes[0..8].try_into().unwrap(),
        ) else {
            return false;
        };
        let Ok(m0_open) = Goldilocks::from_be_bytes_canonical(
            comp.dealer_opened_share_bytes[8..16].try_into().unwrap(),
        ) else {
            return false;
        };
        let Ok(m1_open) = Goldilocks::from_be_bytes_canonical(
            comp.dealer_opened_share_bytes[16..24].try_into().unwrap(),
        ) else {
            return false;
        };
        let m_open = GoldilocksExt2::new(m0_open, m1_open);
        let expected_eval = GoldilocksExt2::new(c0_evals[comp.recv_idx], c1_evals[comp.recv_idx]);
        if chal * GoldilocksExt2::from_base(f_open) + m_open != expected_eval {
            return false;
        }
    }

    true
}

/// Apply `Π_deg0` proactive share refresh (`f_delta(0) == 0`) to 32-byte `ShamirSeedShare256` shares over `TowerGf256`.
/// Leaves the underlying 32-byte secret and derived `PqPublicKey` bit-for-bit invariant!
pub fn proactive_refresh_seed32_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    current_shares: &mut [ShamirSeedShare256],
    rng: &mut MpcCsprng,
) -> bool {
    let n = eval_points.len();
    if t == 0 || t > n || current_shares.len() != n {
        return false;
    }
    let mut coeffs = vec![TowerGf256::ZERO; t];
    for bit_idx in 0..256 {
        coeffs[0] = TowerGf256::ZERO; // Enforced zero constant term!
        for c in coeffs.iter_mut().skip(1) {
            *c = TowerGf256(rng.next_u8());
        }
        let mut delta_evals: Vec<TowerGf256> = eval_points
            .iter()
            .map(|&pt| eval_poly_gf256(&coeffs, pt))
            .collect();
        if !check_zero_constant_refresh_gf256(t, eval_points, &coeffs, &delta_evals) {
            coeffs.fill(TowerGf256::ZERO);
            delta_evals.fill(TowerGf256::ZERO);
            core::hint::black_box((coeffs.as_slice(), delta_evals.as_slice()));
            return false;
        }
        for p in 0..n {
            current_shares[p].bit_shares[bit_idx] =
                current_shares[p].bit_shares[bit_idx].add(delta_evals[p]);
        }
        delta_evals.fill(TowerGf256::ZERO);
        core::hint::black_box(delta_evals.as_slice());
    }
    coeffs.fill(TowerGf256::ZERO);
    core::hint::black_box(coeffs.as_slice());
    true
}

/// Apply `Π_deg0` proactive share refresh (`f_delta(0) == 0`) to 32-byte `ShamirPoseidonSeedShare` shares over `Goldilocks`.
pub fn proactive_refresh_seed32_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    current_shares: &mut [ShamirPoseidonSeedShare],
    rng: &mut MpcCsprng,
) -> bool {
    let n = eval_points.len();
    if t == 0 || t > n || current_shares.len() != n {
        return false;
    }
    let mut coeffs = vec![Goldilocks::ZERO; t];
    for b_idx in 0..32 {
        coeffs[0] = Goldilocks::ZERO; // Enforced zero constant term!
        for c in coeffs.iter_mut().skip(1) {
            *c = rng.next_goldilocks();
        }
        let mut delta_evals: Vec<Goldilocks> = eval_points
            .iter()
            .map(|&pt| eval_poly_goldilocks(&coeffs, pt))
            .collect();
        if !check_zero_constant_refresh_goldilocks(t, eval_points, &coeffs, &delta_evals) {
            coeffs.fill(Goldilocks::ZERO);
            delta_evals.fill(Goldilocks::ZERO);
            core::hint::black_box((coeffs.as_slice(), delta_evals.as_slice()));
            return false;
        }
        for p in 0..n {
            current_shares[p].byte_shares[b_idx] =
                current_shares[p].byte_shares[b_idx].const_add(delta_evals[p]);
        }
        delta_evals.fill(Goldilocks::ZERO);
        core::hint::black_box(delta_evals.as_slice());
    }
    coeffs.fill(Goldilocks::ZERO);
    core::hint::black_box(coeffs.as_slice());
    true
}

// ============================================================================
// Simplex Monotonic Persist-Before-Sign `EpochLatch` (`leanSig` Anti-Double-Sign)
// ============================================================================

/// Wire magic & format version for persisted `EpochLatchState` WAL records (`78` bytes with 256-bit checksum).
pub const EPOCH_LATCH_MAGIC: [u8; 5] = *b"OBEL\x01";
const TAG_LATCH_WAL: &[u8] = b"OBEND.PQ.LATCH.WAL/v1";

/// Error returned when a signing request violates the monotonic anti-double-sign `EpochLatch`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochLatchError {
    InvalidParticipant {
        party: usize,
        committee_size: usize,
    },
    DuplicateParticipant {
        party: usize,
    },
    StaleEpochReplay {
        requested_epoch: u64,
        high_water: u64,
    },
    EquivocationRefused {
        epoch: u64,
    },
    QuorumInsufficient {
        accepted: usize,
        required_latch_quorum: usize,
    },
    CorruptPersistence,
    IoFailure,
}

/// Non-cloneable persist-before-sign authorization token binding `(epoch, mu)` before stateful signing runs.
#[derive(Debug, PartialEq, Eq)]
pub struct EpochLatchPermit {
    epoch: u64,
    mu: [u8; 32],
}

impl EpochLatchPermit {
    #[inline]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    #[inline]
    pub const fn mu(&self) -> &[u8; 32] {
        &self.mu
    }
}

/// Abstract quorum persist-before-sign latch backend (implemented by `QuorumEpochLatchCluster` and
/// `fsync`-backed `DurableQuorumEpochLatchCluster`).
pub trait EpochLatchQuorumBackend {
    fn acquire_quorum_permit(
        &mut self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<EpochLatchPermit, EpochLatchError>;
}

/// Durable per-signer monotonic epoch latch state (`ThresholdHashMpc.EpochLatchState`).
/// Intentionally non-`Copy` with private `high_water` so callers cannot snapshot & roll back in-memory state.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EpochLatchState {
    high_water: Option<(u64, [u8; 32])>,
}

impl Drop for EpochLatchState {
    fn drop(&mut self) {
        if let Some((ref mut ep, ref mut bound_mu)) = self.high_water {
            *ep = 0;
            bound_mu.fill(0);
            core::hint::black_box((*ep, &*bound_mu));
        }
        self.high_water = None;
    }
}

impl EpochLatchState {
    pub const fn new() -> Self {
        Self { high_water: None }
    }

    #[inline]
    pub const fn high_water(&self) -> Option<(u64, [u8; 32])> {
        self.high_water
    }

    /// Encode into a fixed 78-byte integrity-checked WAL record:
    /// `magic(5) || tag(1) || epoch_be(8) || mu(32) || cshake256_mac(32)`.
    pub fn to_durable_bytes(&self) -> [u8; 78] {
        let mut out = [0u8; 78];
        out[0..5].copy_from_slice(&EPOCH_LATCH_MAGIC);
        match self.high_water {
            None => {
                out[5] = 0;
            }
            Some((ep, bound_mu)) => {
                out[5] = 1;
                out[6..14].copy_from_slice(&ep.to_be_bytes());
                out[14..46].copy_from_slice(&bound_mu);
            }
        }
        let checksum = cshake256_hash32(TAG_LATCH_WAL, &out[0..46]);
        out[46..78].copy_from_slice(&checksum);
        out
    }

    /// Decode and verify a 78-byte WAL record, rejecting truncated, magic-mismatched, or bit-rotted records.
    pub fn from_durable_bytes(bytes: &[u8]) -> Result<Self, EpochLatchError> {
        if bytes.len() != 78 || bytes[0..5] != EPOCH_LATCH_MAGIC {
            return Err(EpochLatchError::CorruptPersistence);
        }
        let expected_checksum = cshake256_hash32(TAG_LATCH_WAL, &bytes[0..46]);
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= expected_checksum[i] ^ bytes[46 + i];
        }
        if diff != 0 {
            return Err(EpochLatchError::CorruptPersistence);
        }
        match bytes[5] {
            0 => {
                if bytes[6..46].iter().any(|&b| b != 0) {
                    return Err(EpochLatchError::CorruptPersistence);
                }
                Ok(Self { high_water: None })
            }
            1 => {
                let mut ep_bytes = [0u8; 8];
                ep_bytes.copy_from_slice(&bytes[6..14]);
                let mut bound_mu = [0u8; 32];
                bound_mu.copy_from_slice(&bytes[14..46]);
                Ok(Self {
                    high_water: Some((u64::from_be_bytes(ep_bytes), bound_mu)),
                })
            }
            _ => Err(EpochLatchError::CorruptPersistence),
        }
    }

    /// Atomic persist-before-sign state transition matching `ThresholdHashMpc.stepEpochLatch`:
    /// - `None` -> `Some((epoch, mu))`
    /// - `epoch > hw` -> advances to `Some((epoch, mu))`
    /// - `epoch == hw` -> idempotent retry succeeds **iff** `bound_mu == mu` (`EquivocationRefused` if `mu' != mu`)!
    /// - `epoch < hw` -> `StaleEpochReplay`!
    pub fn step_epoch_latch(&mut self, epoch: u64, mu: [u8; 32]) -> Result<(), EpochLatchError> {
        match self.high_water {
            None => {
                self.high_water = Some((epoch, mu));
                Ok(())
            }
            Some((hw, bound_mu)) => {
                if epoch > hw {
                    self.high_water = Some((epoch, mu));
                    Ok(())
                } else if epoch == hw {
                    let mut diff = 0u8;
                    for i in 0..32 {
                        diff |= bound_mu[i] ^ mu[i];
                    }
                    if diff == 0 {
                        Ok(())
                    } else {
                        Err(EpochLatchError::EquivocationRefused { epoch })
                    }
                } else {
                    Err(EpochLatchError::StaleEpochReplay {
                        requested_epoch: epoch,
                        high_water: hw,
                    })
                }
            }
        }
    }
}

/// Committee-wide Simplex epoch-latch cluster enforcing quorum intersection `2 * t_latch > n + f`.
pub struct QuorumEpochLatchCluster {
    pub n: usize,
    pub max_faulty: usize,
    pub latch_quorum: usize,
    signer_latches: Vec<EpochLatchState>,
}

impl QuorumEpochLatchCluster {
    /// Construct a `QuorumEpochLatchCluster` with optimal Simplex latch quorum `floor((n + f)/2) + 1`.
    pub fn new(n: usize, max_faulty: usize) -> Option<Self> {
        let sum = n.checked_add(max_faulty)?;
        let latch_quorum = (sum / 2).checked_add(1)?;
        if latch_quorum > n || latch_quorum.checked_mul(2)? <= sum {
            return None;
        }
        Some(Self {
            n,
            max_faulty,
            latch_quorum,
            signer_latches: vec![EpochLatchState::new(); n],
        })
    }

    /// Read-only inspection of signer `party`'s monotonic `(epoch, mu)` high-water mark.
    #[inline]
    pub fn signer_high_water(&self, party: usize) -> Option<(u64, [u8; 32])> {
        self.signer_latches
            .get(party)
            .and_then(EpochLatchState::high_water)
    }

    fn stage_quorum_transition(
        &self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<Vec<EpochLatchState>, EpochLatchError> {
        let mut seen = vec![false; self.n];
        for &p in participating_signers {
            if p >= self.n {
                return Err(EpochLatchError::InvalidParticipant {
                    party: p,
                    committee_size: self.n,
                });
            }
            if seen[p] {
                return Err(EpochLatchError::DuplicateParticipant { party: p });
            }
            seen[p] = true;
        }

        let mut staged = self.signer_latches.clone();
        let mut accepted = 0usize;
        let mut first_err: Option<EpochLatchError> = None;
        for &p in participating_signers {
            match staged[p].step_epoch_latch(epoch, mu) {
                Ok(()) => accepted += 1,
                Err(e) => {
                    if first_err.is_none() {
                        first_err = Some(e);
                    }
                }
            }
        }
        if accepted >= self.latch_quorum {
            Ok(staged)
        } else if let Some(err) = first_err {
            Err(err)
        } else {
            Err(EpochLatchError::QuorumInsufficient {
                accepted,
                required_latch_quorum: self.latch_quorum,
            })
        }
    }

    /// Atomically acquire a persist-before-sign latch quorum across **distinct, in-range** `participating_signers`:
    /// - Strictly rejects out-of-range (`InvalidParticipant`) or duplicate (`DuplicateParticipant`) IDs (blocking Sybil `&[0, 0, 0]` bypasses);
    /// - Stages all per-node latch transitions on a copy and commits `self.signer_latches` **ONLY** if `accepted >= self.latch_quorum`!
    pub fn acquire_latch_quorum(
        &mut self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<EpochLatchPermit, EpochLatchError> {
        let staged = self.stage_quorum_transition(participating_signers, epoch, mu)?;
        self.signer_latches = staged;
        Ok(EpochLatchPermit { epoch, mu })
    }
}

impl EpochLatchQuorumBackend for QuorumEpochLatchCluster {
    #[inline]
    fn acquire_quorum_permit(
        &mut self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<EpochLatchPermit, EpochLatchError> {
        self.acquire_latch_quorum(participating_signers, epoch, mu)
    }
}

/// Durable `fsync`-backed committee epoch-latch cluster (`std` / crash-safe WAL persistence).
/// Persists every signer's 78-byte integrity-checked WAL record via atomic `write_all` + `File::sync_all` +
/// `fs::rename` + parent-directory `sync_all` BEFORE issuing an `EpochLatchPermit`!
#[cfg(any(test, feature = "std"))]
pub struct DurableQuorumEpochLatchCluster {
    dir: std::path::PathBuf,
    cluster: QuorumEpochLatchCluster,
}

#[cfg(any(test, feature = "std"))]
impl DurableQuorumEpochLatchCluster {
    fn lock(dir: &std::path::Path) -> Result<std::fs::File, EpochLatchError> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(dir.join("cluster.lock"))
            .map_err(|_| EpochLatchError::IoFailure)?;
        file.lock().map_err(|_| EpochLatchError::IoFailure)?;
        Ok(file)
    }

    fn manifest(cluster: &QuorumEpochLatchCluster) -> Vec<u8> {
        let mut bytes = b"OBEND.LATCH.CLUSTER/v1".to_vec();
        for value in [cluster.n, cluster.max_faulty, cluster.latch_quorum] {
            bytes.extend_from_slice(&(value as u64).to_be_bytes());
        }
        bytes
    }

    fn reload(
        dir: &std::path::Path,
        cluster: &mut QuorumEpochLatchCluster,
    ) -> Result<(), EpochLatchError> {
        let expected = Self::manifest(cluster);
        if std::fs::read(dir.join("cluster.manifest"))
            .map_err(|_| EpochLatchError::CorruptPersistence)?
            != expected
        {
            return Err(EpochLatchError::CorruptPersistence);
        }
        let mut states = Vec::with_capacity(cluster.n);
        for p in 0..cluster.n {
            let raw = std::fs::read(Self::signer_path(dir, p))
                .map_err(|_| EpochLatchError::CorruptPersistence)?;
            if !raw.starts_with(&expected) {
                return Err(EpochLatchError::CorruptPersistence);
            }
            states.push(EpochLatchState::from_durable_bytes(&raw[expected.len()..])?);
        }
        cluster.signer_latches = states;
        Ok(())
    }

    fn signer_path(dir: &std::path::Path, party: usize) -> std::path::PathBuf {
        dir.join(alloc::format!("signer_{party}.latch"))
    }

    fn write_signer_atomic(
        dir: &std::path::Path,
        party: usize,
        state: &EpochLatchState,
    ) -> Result<(), EpochLatchError> {
        use std::io::Write;
        let final_path = Self::signer_path(dir, party);
        let tmp_path = dir.join(alloc::format!("signer_{party}.latch.tmp"));
        let bytes = state.to_durable_bytes();
        let mut f = std::fs::File::create(&tmp_path).map_err(|_| EpochLatchError::IoFailure)?;
        let manifest =
            std::fs::read(dir.join("cluster.manifest")).map_err(|_| EpochLatchError::IoFailure)?;
        f.write_all(&manifest)
            .map_err(|_| EpochLatchError::IoFailure)?;
        f.write_all(&bytes)
            .map_err(|_| EpochLatchError::IoFailure)?;
        f.sync_all().map_err(|_| EpochLatchError::IoFailure)?;
        drop(f);
        std::fs::rename(&tmp_path, &final_path).map_err(|_| EpochLatchError::IoFailure)?;
        let dir_fd = std::fs::File::open(dir).map_err(|_| EpochLatchError::IoFailure)?;
        dir_fd.sync_all().map_err(|_| EpochLatchError::IoFailure)?;
        Ok(())
    }

    /// Open an existing durable latch directory (verifying every persisted WAL record's 256-bit checksum)
    /// or initialize fresh durable latch records for all `n` committee members.
    pub fn open_or_init(
        dir: impl Into<std::path::PathBuf>,
        n: usize,
        max_faulty: usize,
    ) -> Result<Self, EpochLatchError> {
        let dir = dir.into();
        let mut cluster =
            QuorumEpochLatchCluster::new(n, max_faulty).ok_or(EpochLatchError::IoFailure)?;
        std::fs::create_dir_all(&dir).map_err(|_| EpochLatchError::IoFailure)?;
        let _lock = Self::lock(&dir)?;
        let existing = dir.join("cluster.manifest").exists()
            || std::fs::read_dir(&dir)
                .map_err(|_| EpochLatchError::IoFailure)?
                .try_fold(false, |found, entry| {
                    entry.map(|e| found || e.path().extension().is_some_and(|ext| ext == "latch"))
                })
                .map_err(|_| EpochLatchError::IoFailure)?;
        if existing {
            Self::reload(&dir, &mut cluster)?;
        } else {
            use std::io::Write;
            let mut manifest = std::fs::File::create(dir.join("cluster.manifest"))
                .map_err(|_| EpochLatchError::IoFailure)?;
            manifest
                .write_all(&Self::manifest(&cluster))
                .map_err(|_| EpochLatchError::IoFailure)?;
            manifest
                .sync_all()
                .map_err(|_| EpochLatchError::IoFailure)?;
            for p in 0..n {
                Self::write_signer_atomic(&dir, p, &cluster.signer_latches[p])?;
            }
        }
        Ok(Self { dir, cluster })
    }

    #[inline]
    pub const fn latch_quorum(&self) -> usize {
        self.cluster.latch_quorum
    }

    #[inline]
    pub fn signer_high_water(&self, party: usize) -> Option<(u64, [u8; 32])> {
        self.cluster.signer_high_water(party)
    }

    /// Stage quorum transition, `fsync` every updated signer WAL record + parent directory to disk,
    /// and ONLY then commit in-memory state and return `EpochLatchPermit`.
    pub fn acquire_latch_quorum(
        &mut self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<EpochLatchPermit, EpochLatchError> {
        let _lock = Self::lock(&self.dir)?;
        Self::reload(&self.dir, &mut self.cluster)?;
        let staged = self
            .cluster
            .stage_quorum_transition(participating_signers, epoch, mu)?;
        for &p in participating_signers {
            if staged[p] != self.cluster.signer_latches[p] {
                Self::write_signer_atomic(&self.dir, p, &staged[p])?;
            }
        }
        self.cluster.signer_latches = staged;
        Ok(EpochLatchPermit { epoch, mu })
    }
}

#[cfg(any(test, feature = "std"))]
impl EpochLatchQuorumBackend for DurableQuorumEpochLatchCluster {
    #[inline]
    fn acquire_quorum_permit(
        &mut self,
        participating_signers: &[usize],
        epoch: u64,
        mu: [u8; 32],
    ) -> Result<EpochLatchPermit, EpochLatchError> {
        self.acquire_latch_quorum(participating_signers, epoch, mu)
    }
}

#[cfg(test)]
mod durable_regression_tests {
    use super::*;
    #[test]
    fn cross_instance_reload_and_partial_rollback_fail_closed() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "latch-lock-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let mut a = DurableQuorumEpochLatchCluster::open_or_init(&dir, 5, 1).unwrap();
        let mut b = DurableQuorumEpochLatchCluster::open_or_init(&dir, 5, 1).unwrap();
        a.acquire_latch_quorum(&[0, 1, 2, 3], 8, [1; 32]).unwrap();
        assert!(matches!(
            b.acquire_latch_quorum(&[0, 1, 2, 3], 8, [2; 32]),
            Err(EpochLatchError::EquivocationRefused { .. })
        ));
        assert!(DurableQuorumEpochLatchCluster::open_or_init(&dir, 4, 1).is_err());
        std::fs::remove_file(dir.join("signer_0.latch")).unwrap();
        assert!(DurableQuorumEpochLatchCluster::open_or_init(&dir, 5, 1).is_err());
        assert!(b.acquire_latch_quorum(&[0, 1, 2, 3], 9, [1; 32]).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
