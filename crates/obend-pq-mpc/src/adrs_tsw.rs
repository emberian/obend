//! Pre-locked 32-byte `HashAdrs`, polymorphic `TweakableHashSuite` (`Cshake256Suite` &
//! `Poseidon2Suite`), Target-Sum Winternitz (`TSW` / `WOTS+C`), FORS, XMSS, stateless
//! `leanSPHINCS` / `SLH-DSA`, stateful `leanSig`, committed-identity `HybridPinnedSig`,
//! and tri-state `VerifyReply`.
//!
//! Matches `Obend.Crypto.PqHashSignatures` byte-for-byte across all domain tags,
//! `encodeAdrs`, `encodeMultiFrame`, `cshake256Suite`, and `poseidon2Suite`.

#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

use alloc::vec::Vec;

use obend_crypto_exec::goldilocks::Goldilocks;
use obend_crypto_exec::transcript::Cshake256Xof;

use crate::poseidon2_mpc::poseidon2_hash32;

/// Canonical domain customization strings matching `Obend.Crypto.PqHashSignatures`.
pub const PQ_CSHAKE_SUITE_CUSTOM: &[u8] = b"OBEND.PQ.SUITE.CSHAKE256/v1";
pub const PQ_POSEIDON2_SUITE_ID: &[u8] = b"OBEND.PQ.SUITE.POSEIDON2/v1";

pub const TAG_PRF_MSG: &[u8] = b"OBEND.PQ.PRFMSG/v1";
pub const TAG_H_MSG: &[u8] = b"OBEND.PQ.HMSG/v1";
pub const TAG_PRF: &[u8] = b"OBEND.PQ.PRF/v1";
pub const TAG_TH_F: &[u8] = b"OBEND.PQ.TH_F/v1";
pub const TAG_TH_H: &[u8] = b"OBEND.PQ.TH_H/v1";
pub const TAG_TH_TL: &[u8] = b"OBEND.PQ.TH_TL/v1";
pub const TAG_H_PRE: &[u8] = b"OBEND.PQ.PRE/v1";
pub const HYBRID_ID_CUSTOM: &[u8] = b"OBEND.PQ.HYBRID.ID/v1";

/// Canonical 5-byte wire header magic `"OBPQ\x01"`.
pub const PQ_WIRE_MAGIC: [u8; 5] = [0x4F, 0x42, 0x50, 0x51, 0x01];

/// Domain-separation role of a 32-byte hash address inside the hypertree / FORS / WOTS+C hierarchy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AdrsKind {
    WotsHash = 0,
    WotsPk = 1,
    Tree = 2,
    ForsTree = 3,
    ForsRoots = 4,
    WotsPrf = 5,
    ForsPrf = 6,
}

impl AdrsKind {
    #[inline]
    pub const fn to_code(self) -> u32 {
        self as u32
    }

    #[inline]
    pub const fn from_code(code: u32) -> Option<Self> {
        match code {
            0 => Some(Self::WotsHash),
            1 => Some(Self::WotsPk),
            2 => Some(Self::Tree),
            3 => Some(Self::ForsTree),
            4 => Some(Self::ForsRoots),
            5 => Some(Self::WotsPrf),
            6 => Some(Self::ForsPrf),
            _ => None,
        }
    }
}

/// Canonical 32-byte tweakable hash address (`ADRS`):
/// `[0..4) layer || [4..8) 0 || [8..16) tree || [16..20) kind || [20..24) key_pair || [24..28) chain_idx || [28..32) hash_step`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HashAdrs {
    pub layer: u32,
    pub tree: u64,
    pub kind: AdrsKind,
    pub key_pair: u32,
    pub chain_idx: u32,
    pub hash_step: u32,
}

impl HashAdrs {
    pub const ZERO: Self = Self {
        layer: 0,
        tree: 0,
        kind: AdrsKind::WotsHash,
        key_pair: 0,
        chain_idx: 0,
        hash_step: 0,
    };
}

/// Pre-locked 32-byte big-endian `ADRS` frame matching `Obend.Crypto.PqHashSignatures.encodeAdrs`.
#[inline]
pub fn encode_adrs(a: &HashAdrs) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&a.layer.to_be_bytes());
    // out[4..8] = 0u32
    out[8..16].copy_from_slice(&a.tree.to_be_bytes());
    out[16..20].copy_from_slice(&a.kind.to_code().to_be_bytes());
    out[20..24].copy_from_slice(&a.key_pair.to_be_bytes());
    out[24..28].copy_from_slice(&a.chain_idx.to_be_bytes());
    out[28..32].copy_from_slice(&a.hash_step.to_be_bytes());
    out
}

/// Decode a canonical 32-byte `ADRS` frame (`None` if reserved `[4..8)` != 0 or unknown `AdrsKind`).
pub fn decode_adrs(bytes: &[u8; 32]) -> Option<HashAdrs> {
    if bytes[4..8] != [0, 0, 0, 0] {
        return None;
    }
    let layer = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    let tree = u64::from_be_bytes([
        bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
    ]);
    let kind_code = u32::from_be_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]);
    let kind = AdrsKind::from_code(kind_code)?;
    let key_pair = u32::from_be_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]);
    let chain_idx = u32::from_be_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]);
    let hash_step = u32::from_be_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]);
    Some(HashAdrs {
        layer,
        tree,
        kind,
        key_pair,
        chain_idx,
        hash_step,
    })
}

/// Canonical unsigned LEB128 natural encoding matching `Obend.Crypto.leb128`.
#[inline]
pub fn push_leb128(out: &mut Vec<u8>, mut n: usize) {
    while n >= 128 {
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out.push(n as u8);
}

#[inline]
pub fn leb128(n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(4);
    push_leb128(&mut out, n);
    out
}

/// Self-delimiting multi-field byte frame `leb128(count) || leb128(|f_0|) || f_0 || ...`,
/// matching `Obend.Crypto.PqHashSignatures.encodeMultiFrame`.
pub fn encode_multi_frame(fields: &[&[u8]]) -> Vec<u8> {
    let total_payload: usize = fields.iter().map(|f| f.len() + 2).sum();
    let mut out = Vec::with_capacity(2 + total_payload);
    push_leb128(&mut out, fields.len());
    for f in fields {
        push_leb128(&mut out, f.len());
        out.extend_from_slice(f);
    }
    out
}

/// Evaluate `cSHAKE256(custom, msg)` returning 32 bytes, matching `Obend.Digest.Cshake256.cshake256Bytes`.
#[inline]
pub fn cshake256_hash32(custom: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(custom);
    xof.absorb(msg);
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Polymorphic 256-bit tweakable hash suite abstracting `cSHAKE256` and `Poseidon2Goldilocks`.
pub trait TweakableHashSuite: Copy + Sync {
    fn suite_id(&self) -> &'static [u8];
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32];
}

/// NIST SP 800-185 `cSHAKE256` instantiation (`SLH-DSA` / `leanSPHINCS-cSHAKE256`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Cshake256Suite;

impl TweakableHashSuite for Cshake256Suite {
    #[inline]
    fn suite_id(&self) -> &'static [u8] {
        PQ_CSHAKE_SUITE_CUSTOM
    }

    #[inline]
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32] {
        cshake256_hash32(PQ_CSHAKE_SUITE_CUSTOM, preimage)
    }
}

/// Width-12 `Poseidon2Goldilocks` algebraic instantiation (`leanSig` / `leanSPHINCS-Poseidon2`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Poseidon2Suite;

impl TweakableHashSuite for Poseidon2Suite {
    #[inline]
    fn suite_id(&self) -> &'static [u8] {
        PQ_POSEIDON2_SUITE_ID
    }

    #[inline]
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32] {
        poseidon2_hash32(preimage)
    }
}

/// Build the exact self-delimiting preimage `encodeMultiFrame([role_tag, pk_seed, encodeAdrs(adrs)] ++ args)`.
pub fn th_preimage(role_tag: &[u8], pk_seed: &[u8], adrs: &HashAdrs, args: &[&[u8]]) -> Vec<u8> {
    let adrs_bytes = encode_adrs(adrs);
    let count = 3 + args.len();
    let payload_cap: usize = role_tag.len()
        + pk_seed.len()
        + 32
        + args.iter().map(|a| a.len() + 2).sum::<usize>()
        + 8;
    let mut out = Vec::with_capacity(payload_cap);
    push_leb128(&mut out, count);
    push_leb128(&mut out, role_tag.len());
    out.extend_from_slice(role_tag);
    push_leb128(&mut out, pk_seed.len());
    out.extend_from_slice(pk_seed);
    push_leb128(&mut out, 32);
    out.extend_from_slice(&adrs_bytes);
    for a in args {
        push_leb128(&mut out, a.len());
        out.extend_from_slice(a);
    }
    out
}

#[inline]
pub fn th_call<S: TweakableHashSuite>(
    suite: S,
    role_tag: &[u8],
    pk_seed: &[u8],
    adrs: &HashAdrs,
    args: &[&[u8]],
) -> [u8; 32] {
    let pre = th_preimage(role_tag, pk_seed, adrs, args);
    suite.raw_hash(&pre)
}

#[inline]
pub fn th_chain_f<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    x: &[u8; 32],
) -> [u8; 32] {
    th_call(suite, TAG_TH_F, pk_seed, adrs, &[x])
}

#[inline]
pub fn th_node_h<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    left: &[u8; 32],
    right: &[u8; 32],
) -> [u8; 32] {
    th_call(suite, TAG_TH_H, pk_seed, adrs, &[left, right])
}

pub fn th_tweak_tl<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    limbs: &[[u8; 32]],
) -> [u8; 32] {
    let refs: Vec<&[u8]> = limbs.iter().map(|l| l.as_slice()).collect();
    th_call(suite, TAG_TH_TL, pk_seed, adrs, &refs)
}

#[inline]
pub fn th_secret_prf<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    sk_seed: &[u8],
    adrs: &HashAdrs,
) -> [u8; 32] {
    th_call(suite, TAG_PRF, pk_seed, adrs, &[sk_seed])
}

#[inline]
pub fn th_prf_msg<S: TweakableHashSuite>(
    suite: S,
    sk_prf: &[u8],
    opt_rand: &[u8],
    mu: &[u8; 32],
) -> [u8; 32] {
    th_call(suite, TAG_PRF_MSG, &[], &HashAdrs::ZERO, &[sk_prf, opt_rand, mu])
}

#[inline]
pub fn th_pre_hash<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    pk_root: &[u8],
    msg: &[u8],
) -> [u8; 32] {
    th_call(suite, TAG_H_PRE, pk_seed, &HashAdrs::ZERO, &[pk_root, msg])
}

#[inline]
pub fn th_hash_msg<S: TweakableHashSuite>(
    suite: S,
    r_rand: &[u8; 32],
    pk_seed: &[u8],
    pk_root: &[u8],
    mu: &[u8; 32],
    layer_idx: u32,
    tree_idx: u64,
    ctr: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: layer_idx,
        tree: tree_idx,
        kind: AdrsKind::WotsHash,
        key_pair: 0,
        chain_idx: 0,
        hash_step: ctr,
    };
    let ctr_be = ctr.to_be_bytes();
    th_call(
        suite,
        TAG_H_MSG,
        pk_seed,
        &adrs,
        &[r_rand, pk_root, mu, &ctr_be],
    )
}

/// Canonical `TSW` target sum `floor(ell1 * (w - 1) / 2)`.
#[inline]
pub const fn canonical_target_sum(w: usize, ell1: usize) -> usize {
    (ell1 * w.saturating_sub(1)) / 2
}

/// Load-bearing Target-Sum Winternitz (`TSW`) checker matching `checkTargetSum`.
#[inline]
pub fn check_target_sum(w: usize, ell1: usize, target: usize, digits: &[usize]) -> bool {
    if digits.len() != ell1 {
        return false;
    }
    let mut sum = 0usize;
    for &d in digits {
        if d >= w {
            return false;
        }
        sum += d;
    }
    sum == target
}

/// Unpack bytes into `ell1` base-`w` digits matching `extractBaseWDigits` in `PqHashSignatures.lean`.
pub fn extract_base_w_digits(w: usize, ell1: usize, digest_bytes: &[u8]) -> Vec<usize> {
    let w_safe = if w < 2 { 4 } else { w };
    let denom = if digest_bytes.is_empty() {
        1
    } else {
        digest_bytes.len()
    };
    let mut out = Vec::with_capacity(ell1);
    for idx in 0..ell1 {
        if w_safe == 4 {
            let byte_idx = (idx / 4) % denom;
            let shift = (3 - (idx % 4)) * 2;
            let b = digest_bytes.get(byte_idx).copied().unwrap_or(0) as usize;
            out.push((b >> shift) & 3);
        } else {
            let byte_idx = idx % denom;
            let b = digest_bytes.get(byte_idx).copied().unwrap_or(0) as usize;
            out.push(b % w_safe);
        }
    }
    out
}

/// Local plaintext CPU `TSW` counter grinder (`0` MPC gates, `0` network rounds).
pub fn grind_tsw_counter<S: TweakableHashSuite>(
    suite: S,
    w: usize,
    ell1: usize,
    target: usize,
    r_rand: &[u8; 32],
    pk_seed: &[u8],
    pk_root: &[u8],
    mu: &[u8; 32],
    layer_idx: u32,
    tree_idx: u64,
    max_grind: u32,
) -> Option<(u32, Vec<usize>, [u8; 32])> {
    for ctr in 0..max_grind {
        let hmsg = th_hash_msg(suite, r_rand, pk_seed, pk_root, mu, layer_idx, tree_idx, ctr);
        let digits = extract_base_w_digits(w, ell1, &hmsg);
        if check_target_sum(w, ell1, target, &digits) {
            return Some((ctr, digits, hmsg));
        }
    }
    None
}

/// Unified parameter profile covering `THINCS-Custody-128`, `leanSPHINCS-128f`, and stateful `leanSig`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PqHashParams {
    pub w: usize,
    pub ell1: usize,
    pub subtree_height: usize,
    pub num_layers: usize,
    pub fors_trees: usize,
    pub fors_height: usize,
    pub max_sigs_log2: usize,
    pub stateful_lean_sig: bool,
}

impl PqHashParams {
    #[inline]
    pub const fn target_sum(&self) -> usize {
        canonical_target_sum(self.w, self.ell1)
    }

    /// Structural non-degeneracy check matching `Obend.Crypto.PqHashSignatures.PqHashParams.wellFormed`.
    #[inline]
    pub const fn is_well_formed(&self) -> bool {
        self.num_layers > 0
            && self.w >= 2
            && self.w <= 256
            && self.ell1 > 0
            && (self.stateful_lean_sig || self.fors_trees > 0)
            && self.subtree_height <= 30
            && self.fors_height <= 30
            && self.num_layers.saturating_mul(self.subtree_height) <= 62
    }

    /// Checked leaf index range test `leaf_global_idx < 2^(num_layers * subtree_height)`.
    #[inline]
    pub const fn leaf_idx_in_range(&self, leaf_global_idx: usize) -> bool {
        let total_bits = self.num_layers.saturating_mul(self.subtree_height);
        if total_bits >= (usize::BITS as usize) {
            true
        } else {
            leaf_global_idx < (1usize << total_bits)
        }
    }

    /// Regime A: `THINCS-Custody-128` (`Q_max = 2^12 = 4,096`, `h = 12, d = 2, h' = 6, w = 4, ell1 = 64, k = 18, a = 8`).
    pub const THINCS_CUSTODY_128: Self = Self {
        w: 4,
        ell1: 64,
        subtree_height: 6,
        num_layers: 2,
        fors_trees: 18,
        fors_height: 8,
        max_sigs_log2: 12,
        stateful_lean_sig: false,
    };

    /// Regime B: `leanSPHINCS-128f` (`Q_max = 2^16 = 65,536`, `h = 20, d = 10, h' = 2, w = 4, ell1 = 64, k = 18, a = 8`).
    pub const LEAN_SPHINCS_128F: Self = Self {
        w: 4,
        ell1: 64,
        subtree_height: 2,
        num_layers: 10,
        fors_trees: 18,
        fors_height: 8,
        max_sigs_log2: 16,
        stateful_lean_sig: false,
    };

    /// Regime C: Stateful algebraic `leanSig-Poseidon2` (`Q_max = 2^16`, `h = 16, d = 1, w = 4, ell1 = 64`).
    pub const LEAN_SIG_POSEIDON2: Self = Self {
        w: 4,
        ell1: 64,
        subtree_height: 16,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 16,
        stateful_lean_sig: true,
    };

    /// Compact fast-test / golden-vector profile (`w = 4, ell1 = 8, d = 2, h' = 2, k = 4, a = 2`).
    pub const COMPACT_GOLDEN: Self = Self {
        w: 4,
        ell1: 8,
        subtree_height: 2,
        num_layers: 2,
        fors_trees: 4,
        fors_height: 2,
        max_sigs_log2: 4,
        stateful_lean_sig: false,
    };

    /// Compact stateful `leanSig` profile (`w = 4, ell1 = 8, d = 1, h' = 2`).
    pub const COMPACT_LEAN_SIG: Self = Self {
        w: 4,
        ell1: 8,
        subtree_height: 2,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 2,
        stateful_lean_sig: true,
    };

    /// Benchmark stateful `leanSig-Poseidon2` profile (`h = 8, d = 1, w = 4, ell1 = 64`, 256 leaves cached at DKG,
    /// online active-leaf path = exact `1 + 64 * 2 + 1 = 130`–`257` permutations matching `LEAN_SIG_POSEIDON2` online path!).
    pub const LEAN_SIG_BENCH_CACHED: Self = Self {
        w: 4,
        ell1: 64,
        subtree_height: 8,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 8,
        stateful_lean_sig: true,
    };
}

/// Secret key `(sk_seed, sk_prf, pk_seed)` with zeroize-on-drop hygiene.
#[derive(Clone, PartialEq, Eq)]
pub struct PqSecretKey {
    pub sk_seed: [u8; 32],
    pub sk_prf: [u8; 32],
    pub pk_seed: [u8; 32],
}

impl Drop for PqSecretKey {
    fn drop(&mut self) {
        self.sk_seed.fill(0);
        self.sk_prf.fill(0);
        core::hint::black_box(&self.sk_seed);
        core::hint::black_box(&self.sk_prf);
    }
}

impl core::fmt::Debug for PqSecretKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PqSecretKey")
            .field("sk_seed", &"<redacted>")
            .field("sk_prf", &"<redacted>")
            .field("pk_seed", &self.pk_seed)
            .finish()
    }
}

/// Public key `(pk_seed, pk_root)` (`64` bytes canonical wire encoding).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PqPublicKey {
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

impl PqPublicKey {
    #[inline]
    pub fn to_wire_bytes(&self) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[0..32].copy_from_slice(&self.pk_seed);
        out[32..64].copy_from_slice(&self.pk_root);
        out
    }

    #[inline]
    pub fn from_wire_bytes(raw: &[u8]) -> Result<Self, FaultStage> {
        if raw.len() != 64 {
            return Err(FaultStage::PublicKeyLength);
        }
        let mut pk_seed = [0u8; 32];
        let mut pk_root = [0u8; 32];
        pk_seed.copy_from_slice(&raw[0..32]);
        pk_root.copy_from_slice(&raw[32..64]);
        Ok(Self { pk_seed, pk_root })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerXmssSig {
    pub tsw_ctr: u32,
    pub wots_chains: Vec<[u8; 32]>,
    pub auth_path: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub secret_val: [u8; 32],
    pub auth_path: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqHashSig {
    pub r_rand: [u8; 32],
    pub msg_tsw_ctr: u32,
    pub leaf_global_idx: usize,
    pub fors_openings: Vec<ForsTreeOpening>,
    pub layer_sigs: Vec<LayerXmssSig>,
}

/// Advance a WOTS+C chain `steps` iterations starting from `start_step`.
pub fn wots_chain_steps<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kp: u32,
    chain: u32,
    start_step: u32,
    steps: usize,
    cur: [u8; 32],
) -> [u8; 32] {
    let mut val = cur;
    for s in 0..steps {
        let adrs = HashAdrs {
            layer,
            tree,
            kind: AdrsKind::WotsHash,
            key_pair: kp,
            chain_idx: chain,
            hash_step: start_step.wrapping_add(s as u32),
        };
        val = th_chain_f(suite, pk_seed, &adrs, &val);
    }
    val
}

#[inline]
pub fn wots_secret_base<S: TweakableHashSuite>(
    suite: S,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    kp: u32,
    chain: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPrf,
        key_pair: kp,
        chain_idx: chain,
        hash_step: 0,
    };
    th_secret_prf(suite, &sk.pk_seed, &sk.sk_seed, &adrs)
}

pub fn compute_wots_pk<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    kp: u32,
) -> [u8; 32] {
    let mut endpoints = Vec::with_capacity(params.ell1);
    for r in 0..params.ell1 {
        let base = wots_secret_base(suite, sk, layer, tree, kp, r as u32);
        endpoints.push(wots_chain_steps(
            suite,
            &sk.pk_seed,
            layer,
            tree,
            kp,
            r as u32,
            0,
            params.w - 1,
            base,
        ));
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(suite, &sk.pk_seed, &adrs, &endpoints)
}

pub fn recover_wots_pk_from_sig<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kp: u32,
    digits: &[usize],
    sig_chains: &[[u8; 32]],
) -> [u8; 32] {
    let mut endpoints = Vec::with_capacity(params.ell1);
    for r in 0..params.ell1 {
        let dr = digits.get(r).copied().unwrap_or(0);
        let sig_val = sig_chains.get(r).copied().unwrap_or([0u8; 32]);
        let rem = (params.w - 1).saturating_sub(dr);
        endpoints.push(wots_chain_steps(
            suite,
            pk_seed,
            layer,
            tree,
            kp,
            r as u32,
            dr as u32,
            rem,
            sig_val,
        ));
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(suite, pk_seed, &adrs, &endpoints)
}

pub fn compute_merkle_node<S: TweakableHashSuite, F: Fn(usize) -> [u8; 32]>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    leaf_fn: &F,
    height: usize,
    node_idx: usize,
) -> [u8; 32] {
    if height == 0 {
        leaf_fn(node_idx)
    } else {
        let left = compute_merkle_node(
            suite,
            pk_seed,
            layer,
            tree,
            node_kind,
            leaf_fn,
            height - 1,
            2 * node_idx,
        );
        let right = compute_merkle_node(
            suite,
            pk_seed,
            layer,
            tree,
            node_kind,
            leaf_fn,
            height - 1,
            2 * node_idx + 1,
        );
        let adrs = HashAdrs {
            layer,
            tree,
            kind: node_kind,
            key_pair: 0,
            chain_idx: height as u32,
            hash_step: node_idx as u32,
        };
        th_node_h(suite, pk_seed, &adrs, &left, &right)
    }
}

/// Build Merkle authentication path from pre-evaluated leaf slice `leaves[0..2^height]` (`0` redundant leaf evaluations!).
pub fn build_merkle_auth_path_from_leaves<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    leaves: &[[u8; 32]],
    height: usize,
    base_node_idx: usize,
    local_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    let count = 1usize << height;
    debug_assert_eq!(leaves.len(), count);
    let mut cur_level = leaves.to_vec();
    let mut path = Vec::with_capacity(height);
    let mut idx_in_sub = local_idx;
    for h_step in 1..=height {
        let sib_idx = idx_in_sub ^ 1;
        path.push(cur_level[sib_idx]);
        let next_len = cur_level.len() / 2;
        let level_node_offset = base_node_idx << (height - h_step);
        let mut next_level = Vec::with_capacity(next_len);
        for pair_idx in 0..next_len {
            let adrs = HashAdrs {
                layer,
                tree,
                kind: node_kind,
                key_pair: 0,
                chain_idx: h_step as u32,
                hash_step: (level_node_offset + pair_idx) as u32,
            };
            next_level.push(th_node_h(
                suite,
                pk_seed,
                &adrs,
                &cur_level[2 * pair_idx],
                &cur_level[2 * pair_idx + 1],
            ));
        }
        cur_level = next_level;
        idx_in_sub >>= 1;
    }
    (cur_level[0], path)
}

pub fn walk_merkle_auth_path<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    height: usize,
    node_idx: usize,
    local_idx: usize,
    leaf_hash: [u8; 32],
    auth_path: &[[u8; 32]],
) -> Option<[u8; 32]> {
    if height == 0 {
        if auth_path.is_empty() {
            Some(leaf_hash)
        } else {
            None
        }
    } else {
        if auth_path.is_empty() {
            return None;
        }
        // Note: in `PqHashSignatures.lean`, `buildMerkleAuthPath` pushes the TOP sibling first (`sib :: buildMerkleAuthPath ... h-1`)!
        // Let's match `walkMerkleAuthPath` recursive top-down order identically!
        let sib = auth_path[0];
        let rest = &auth_path[1..];
        let half = 1usize << (height - 1);
        let adrs = HashAdrs {
            layer,
            tree,
            kind: node_kind,
            key_pair: 0,
            chain_idx: height as u32,
            hash_step: node_idx as u32,
        };
        if local_idx < half {
            let sub = walk_merkle_auth_path(
                suite,
                pk_seed,
                layer,
                tree,
                node_kind,
                height - 1,
                2 * node_idx,
                local_idx,
                leaf_hash,
                rest,
            )?;
            Some(th_node_h(suite, pk_seed, &adrs, &sub, &sib))
        } else {
            let sub = walk_merkle_auth_path(
                suite,
                pk_seed,
                layer,
                tree,
                node_kind,
                height - 1,
                2 * node_idx + 1,
                local_idx - half,
                leaf_hash,
                rest,
            )?;
            Some(th_node_h(suite, pk_seed, &adrs, &sib, &sub))
        }
    }
}

/// Top-down `build_merkle_auth_path_topdown` matching `PqHashSignatures.buildMerkleAuthPath` (`sib_top` at index `0`, leaf sibling at `height - 1`).
pub fn build_merkle_from_leaves_topdown<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    leaves: &[[u8; 32]],
    height: usize,
    base_node_idx: usize,
    local_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    let (root, mut bottom_up_path) = build_merkle_auth_path_from_leaves(
        suite,
        pk_seed,
        layer,
        tree,
        node_kind,
        leaves,
        height,
        base_node_idx,
        local_idx,
    );
    bottom_up_path.reverse();
    (root, bottom_up_path)
}

#[inline]
pub fn fors_secret_leaf<S: TweakableHashSuite>(
    suite: S,
    sk: &PqSecretKey,
    tree_idx: u64,
    kp_idx: u32,
    global_fors_leaf: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsPrf,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: global_fors_leaf,
    };
    th_secret_prf(suite, &sk.pk_seed, &sk.sk_seed, &adrs)
}

#[inline]
pub fn fors_leaf_hash_from_secret<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    tree_idx: u64,
    kp_idx: u32,
    global_fors_leaf: u32,
    sec_val: &[u8; 32],
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsTree,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: global_fors_leaf,
    };
    th_chain_f(suite, pk_seed, &adrs, sec_val)
}

/// Extract `width` bits starting at bit offset `start_bit` (`hmsg` bytes modulo `hmsg.len()`),
/// matching `Obend.Crypto.PqHashSignatures.extractBitWindow` bit-for-bit!
#[inline]
pub fn extract_bit_window(bytes: &[u8], start_bit: usize, width: usize) -> usize {
    if width == 0 {
        return 0;
    }
    let n_bytes = if bytes.is_empty() { 1 } else { bytes.len() };
    let mut acc = 0usize;
    for b in 0..width {
        let pos = start_bit + b;
        let byte_val = bytes.get((pos / 8) % n_bytes).copied().unwrap_or(0) as usize;
        let bit = (byte_val >> (pos % 8)) & 1;
        acc = (acc << 1) | bit;
    }
    if width < (usize::BITS as usize) {
        acc & ((1usize << width) - 1)
    } else {
        acc
    }
}

/// Derive `k` independent `a`-bit FORS leaf indices starting at bit 88 (after the 64-bit WOTS+C
/// `TSW` message prefix), matching `Obend.Crypto.PqHashSignatures.deriveForsIndices`!
pub fn derive_fors_indices(k: usize, a: usize, hmsg: &[u8]) -> Vec<usize> {
    let mut out = Vec::with_capacity(k);
    for j in 0..k {
        out.push(extract_bit_window(hmsg, 88 + j * a, a));
    }
    out
}

pub fn compute_xmss_subtree_root<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree_idx: u64,
) -> [u8; 32] {
    let leaf_count = 1usize << params.subtree_height;
    let mut leaves = Vec::with_capacity(leaf_count);
    for kp in 0..leaf_count {
        leaves.push(compute_wots_pk(suite, params, sk, layer, tree_idx, kp as u32));
    }
    let (root, _) = build_merkle_from_leaves_topdown(
        suite,
        &sk.pk_seed,
        layer,
        tree_idx,
        AdrsKind::Tree,
        &leaves,
        params.subtree_height,
        0,
        0,
    );
    root
}

/// Derive canonical `PqPublicKey` `(pk_seed, pk_root)` matching `Obend.Crypto.PqHashSignatures.derivePublicKey`.
pub fn derive_public_key<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
) -> PqPublicKey {
    let top_layer = (params.num_layers.saturating_sub(1)) as u32;
    let pk_root = compute_xmss_subtree_root(suite, params, sk, top_layer, 0);
    PqPublicKey {
        pk_seed: sk.pk_seed,
        pk_root,
    }
}

/// Single-party reference signer matching `Obend.Crypto.PqHashSignatures.evalSingleSign`.
pub fn eval_single_sign<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    msg: &[u8],
    opt_rand: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
) -> Option<PqHashSig> {
    if !params.is_well_formed() || !params.leaf_idx_in_range(leaf_global_idx) {
        return None;
    }
    let pk = derive_public_key(suite, params, sk);
    eval_single_sign_with_pk(suite, params, sk, &pk, msg, opt_rand, leaf_global_idx, max_grind)
}

/// Single-party signer given already-enrolled `PqPublicKey`.
pub fn eval_single_sign_with_pk<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    msg: &[u8],
    opt_rand: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
) -> Option<PqHashSig> {
    if !params.is_well_formed() || !params.leaf_idx_in_range(leaf_global_idx) {
        return None;
    }
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let r_rand = th_prf_msg(suite, &sk.sk_prf, opt_rand, &mu);

    let (msg_tsw_ctr, fors_openings, mut cur_root) = if params.stateful_lean_sig {
        (0u32, Vec::new(), mu)
    } else {
        let sub_leaves = 1usize << params.subtree_height;
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let (ctr0, _, hmsg0) = grind_tsw_counter(
            suite,
            params.w,
            params.ell1,
            params.target_sum(),
            &r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &mu,
            0,
            tree0,
            max_grind,
        )?;
        let idxs = derive_fors_indices(params.fors_trees, params.fors_height, &hmsg0);
        let fors_leaf_count = 1usize << params.fors_height;
        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for j in 0..params.fors_trees {
            let idx_j = idxs[j];
            let mut leaves_j = Vec::with_capacity(fors_leaf_count);
            let mut revealed_sec = [0u8; 32];
            for u in 0..fors_leaf_count {
                let global_u = (j * fors_leaf_count + u) as u32;
                let sec = fors_secret_leaf(suite, sk, tree0, kp0, global_u);
                if u == idx_j {
                    revealed_sec = sec;
                }
                leaves_j.push(fors_leaf_hash_from_secret(
                    suite,
                    &sk.pk_seed,
                    tree0,
                    kp0,
                    global_u,
                    &sec,
                ));
            }
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                suite,
                &sk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                &leaves_j,
                params.fors_height,
                j,
                idx_j,
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_sec,
                auth_path: path_j,
            });
        }
        let fors_pk_adrs = HashAdrs {
            layer: 0,
            tree: tree0,
            kind: AdrsKind::ForsRoots,
            key_pair: kp0,
            chain_idx: 0,
            hash_step: 0,
        };
        let fors_pk = th_tweak_tl(suite, &sk.pk_seed, &fors_pk_adrs, &roots);
        (ctr0, openings, fors_pk)
    };

    let sub_leaves = 1usize << params.subtree_height;
    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut cur_global = leaf_global_idx;
    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let (ctr, digits, _) = grind_tsw_counter(
            suite,
            params.w,
            params.ell1,
            params.target_sum(),
            &r_rand,
            &sk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_idx,
            max_grind,
        )?;
        let mut wots_chains = Vec::with_capacity(params.ell1);
        for r in 0..params.ell1 {
            let dr = digits[r];
            let base = wots_secret_base(suite, sk, layer_u32, tree_idx, kp_idx as u32, r as u32);
            wots_chains.push(wots_chain_steps(
                suite,
                &sk.pk_seed,
                layer_u32,
                tree_idx,
                kp_idx as u32,
                r as u32,
                0,
                dr,
                base,
            ));
        }
        let mut subtree_leaves = Vec::with_capacity(sub_leaves);
        for kp in 0..sub_leaves {
            subtree_leaves.push(compute_wots_pk(suite, params, sk, layer_u32, tree_idx, kp as u32));
        }
        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            suite,
            &sk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            &subtree_leaves,
            params.subtree_height,
            0,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    Some(PqHashSig {
        r_rand,
        msg_tsw_ctr,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    })
}

/// Unified verifier matching `Obend.Crypto.PqHashSignatures.verifyPqHashSig`.
pub fn verify_pq_hash_sig<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk: &PqPublicKey,
    msg: &[u8],
    sig: &PqHashSig,
) -> bool {
    if !params.is_well_formed() || !params.leaf_idx_in_range(sig.leaf_global_idx) {
        return false;
    }
    if sig.layer_sigs.len() != params.num_layers {
        return false;
    }
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let sub_leaves = 1usize << params.subtree_height;

    let mut cur_root = if params.stateful_lean_sig {
        if !sig.fors_openings.is_empty() || sig.msg_tsw_ctr != 0 {
            return false;
        }
        mu
    } else {
        if sig.fors_openings.len() != params.fors_trees {
            return false;
        }
        let kp0 = (sig.leaf_global_idx % sub_leaves) as u32;
        let tree0 = (sig.leaf_global_idx / sub_leaves) as u64;
        let hmsg0 = th_hash_msg(
            suite,
            &sig.r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &mu,
            0,
            tree0,
            sig.msg_tsw_ctr,
        );
        let digits0 = extract_base_w_digits(params.w, params.ell1, &hmsg0);
        if !check_target_sum(params.w, params.ell1, params.target_sum(), &digits0) {
            return false;
        }
        let idxs = derive_fors_indices(params.fors_trees, params.fors_height, &hmsg0);
        let fors_leaf_count = 1usize << params.fors_height;
        let mut roots = Vec::with_capacity(params.fors_trees);
        for j in 0..params.fors_trees {
            let idx_j = idxs[j];
            let op = &sig.fors_openings[j];
            let global_u = (j * fors_leaf_count + idx_j) as u32;
            let leaf_h = fors_leaf_hash_from_secret(
                suite,
                &pk.pk_seed,
                tree0,
                kp0,
                global_u,
                &op.secret_val,
            );
            let Some(root_j) = walk_merkle_auth_path(
                suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                params.fors_height,
                j,
                idx_j,
                leaf_h,
                &op.auth_path,
            ) else {
                return false;
            };
            roots.push(root_j);
        }
        let fors_pk_adrs = HashAdrs {
            layer: 0,
            tree: tree0,
            kind: AdrsKind::ForsRoots,
            key_pair: kp0,
            chain_idx: 0,
            hash_step: 0,
        };
        th_tweak_tl(suite, &pk.pk_seed, &fors_pk_pk_adrs_fix(fors_pk_adrs), &roots)
    };

    let mut cur_global = sig.leaf_global_idx;
    for (layer_idx, lsig) in sig.layer_sigs.iter().enumerate() {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let hmsg = th_hash_msg(
            suite,
            &sig.r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_idx,
            lsig.tsw_ctr,
        );
        let digits = extract_base_w_digits(params.w, params.ell1, &hmsg);
        if !check_target_sum(params.w, params.ell1, params.target_sum(), &digits) {
            return false;
        }
        if lsig.wots_chains.len() != params.ell1 {
            return false;
        }
        let wots_pk = recover_wots_pk_from_sig(
            suite,
            params,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            kp_idx as u32,
            &digits,
            &lsig.wots_chains,
        );
        let Some(next_root) = walk_merkle_auth_path(
            suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            params.subtree_height,
            0,
            kp_idx,
            wots_pk,
            &lsig.auth_path,
        ) else {
            return false;
        };
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    cur_root == pk.pk_root
}

#[inline]
const fn fors_pk_pk_adrs_fix(a: HashAdrs) -> HashAdrs {
    a
}

/// Batch verification relation over `Poseidon2Goldilocks` `leanSig` signatures feeding STARK aggregation.
pub fn valid_lean_sig_batch(
    params: &PqHashParams,
    items: &[(PqPublicKey, &[u8], PqHashSig)],
) -> bool {
    if !params.stateful_lean_sig {
        return false;
    }
    items
        .iter()
        .all(|(pk, msg, sig)| verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, sig))
}

/// Enrolled identity digest `idCommit = cSHAKE256("OBEND.PQ.HYBRID.ID/v1", encodeMultiFrame [pk1, pk2])`.
#[inline]
pub fn compute_hybrid_id_commit(pk1_bytes: &[u8], pk2_bytes: &[u8]) -> [u8; 32] {
    let frame = encode_multi_frame(&[pk1_bytes, pk2_bytes]);
    cshake256_hash32(HYBRID_ID_CUSTOM, &frame)
}

/// Load-bearing committed-identity pinning check matching `checkHybridPinning`.
#[inline]
pub fn check_hybrid_pinning(
    id_commit: &[u8; 32],
    pk1_bytes: &[u8],
    carried_pk2: &PqPublicKey,
) -> bool {
    let pk2_wire = carried_pk2.to_wire_bytes();
    compute_hybrid_id_commit(pk1_bytes, &pk2_wire) == *id_commit
}

/// Wire envelope carrying classical/auxiliary signature `sig1`, candidate `carried_pk2`, and PQ signature `sig2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridPinnedSig<Sig1> {
    pub sig1: Sig1,
    pub carried_pk2: PqPublicKey,
    pub sig2: PqHashSig,
}

/// Committed-identity hybrid signature verifier (`S_1 && S_2` bound under `id_commit`).
pub fn verify_hybrid_pinned_sig<S: TweakableHashSuite, Sig1, F1>(
    suite: S,
    params: &PqHashParams,
    id_commit: &[u8; 32],
    pk1_bytes: &[u8],
    verify_s1: F1,
    msg: &[u8],
    hsig: &HybridPinnedSig<Sig1>,
) -> bool
where
    F1: FnOnce(&[u8], &[u8], &Sig1) -> bool,
{
    check_hybrid_pinning(id_commit, pk1_bytes, &hsig.carried_pk2)
        && verify_s1(pk1_bytes, msg, &hsig.sig1)
        && verify_pq_hash_sig(suite, params, &hsig.carried_pk2, msg, &hsig.sig2)
}

/// Exact wire-codec failure stage distinguishing malformed syntax from cryptographic rejection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultStage {
    HeaderMagicOrVersion,
    PublicKeyLength,
    SignatureFraming,
    LayerCountMismatch,
}

/// Tri-state verification reply (`VerifyReply`): never conflates `WireMalformed` with `Reject`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyReply {
    Accept,
    Reject,
    WireMalformed(FaultStage),
}

/// Tri-state wire envelope verifier matching `Obend.Crypto.PqHashSignatures.verifyPqWireEnvelope`.
pub fn verify_pq_wire_envelope<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    raw_pk: &[u8],
    raw_msg: &[u8],
    magic_prefix: &[u8],
    r_rand_slice: &[u8],
    sig: &PqHashSig,
) -> VerifyReply {
    if magic_prefix != PQ_WIRE_MAGIC {
        return VerifyReply::WireMalformed(FaultStage::HeaderMagicOrVersion);
    }
    let Ok(pk) = PqPublicKey::from_wire_bytes(raw_pk) else {
        return VerifyReply::WireMalformed(FaultStage::PublicKeyLength);
    };
    if sig.layer_sigs.len() != params.num_layers {
        return VerifyReply::WireMalformed(FaultStage::LayerCountMismatch);
    }
    if r_rand_slice.len() != 32 || r_rand_slice != sig.r_rand.as_slice() {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if params.stateful_lean_sig {
        if !sig.fors_openings.is_empty() || sig.msg_tsw_ctr != 0 {
            return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
        }
    } else if sig.fors_openings.len() != params.fors_trees
        || sig
            .fors_openings
            .iter()
            .any(|op| op.auth_path.len() != params.fors_height)
    {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if sig.layer_sigs.iter().any(|ls| {
        ls.wots_chains.len() != params.ell1 || ls.auth_path.len() != params.subtree_height
    }) {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if verify_pq_hash_sig(suite, params, &pk, raw_msg, sig) {
        VerifyReply::Accept
    } else {
        VerifyReply::Reject
    }
}

/// Helper keeping `Goldilocks` directly linked inside `adrs_tsw` for STARK public-input packing.
pub fn pack_digest32_to_goldilocks4(digest: &[u8; 32]) -> [Goldilocks; 4] {
    let mut out = [Goldilocks::ZERO; 4];
    for (i, limb) in out.iter_mut().enumerate() {
        let off = 8 * i;
        let raw = u64::from_be_bytes([
            digest[off],
            digest[off + 1],
            digest[off + 2],
            digest[off + 3],
            digest[off + 4],
            digest[off + 5],
            digest[off + 6],
            digest[off + 7],
        ]);
        *limb = Goldilocks::from_u64_reduced(raw);
    }
    out
}
