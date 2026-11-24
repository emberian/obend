#![forbid(unsafe_code)]
//! Unified Multi-Turn "Anti-Vaz" Sovereign SHE Ceremony (`Obend.Polis.SecureHardwareEnv`).
//!
//! Pure zero-dependency Rust with byte-exact parity against `lean/Obend/Polis/SecureHardwareEnv.lean`
//! and `lean/Obend/Crypto/PqHashSignatures.lean`:
//! - **Grounded `ZkmlSuiteArtifact` + `CandidateComputation` `UD-100` Receipt Gate**: pins
//!   `modelWeightsRoot`, `inputRoot`, `outputRoot`, `boundFloorsDigest`, `actionPayloadDigest`,
//!   `1 <= logArity`, `observedNumQueries == pinnedNumQueries`, post-commit PoW grinding, and
//!   explicitly refuses withdrawn `CBR` claims (supporting both `(lb=6, q=86, pow=16)` and
//!   wide-leaf `(lb=2, q=148, pow=0)`).
//! - **Sampled Bit-Exact `s8 x E2M1` (`MXFP4`) Integer Recompute Audit (`fpaudit`)**: commits all
//!   inference rounds under `OBEND.SHE.FPAUDIT_COMMIT/v1` BEFORE deriving the Fiat–Shamir audit coin
//!   (`OBEND.SHE.FPAUDIT_COIN/v1`) and recomputes exact integer dot-products (`tau = 0`), catching
//!   steered argmaxes that any positive logit-tolerance checker (`tau > 0`) admits.
//! - **Real 256-Bit Post-Quantum `PqHashSignatures` (`cshake256Suite`, `TSW`/`WOTS+C` + `XMSS`/`leanSPHINCS`)
//!   Quorums**: `(t, n)` custodian quorums (`OBEND.SHE.CUSTODIAN_SIG/v1`) and Simplex `FINALIZE` QCs
//!   (`OBEND.SHE.SIMPLEX_QC/v1`) anchored to `OBEND.SHE.STATE/v1` with stateful XMSS leaf-reuse blocking.
//! - **Constitutional Non-Regression (`vaz_coercive_floor_downgrade_refused`)** & **Sealed Oracle
//!   Ingress** treating all external sensors/displays strictly as untrusted I/O.

use crate::sha256::ct_eq;
use crate::tee::{TcbPosture, TeeVendor, VerifiedTeeEvidence};
use crate::tlsn_e2ee::{VerifiedCallTree, VerifiedE2eeChannel, VerifiedHttpsTranscript};

// ---------------------------------------------------------------------------
// `cSHAKE256` & LEB128 Framing
// ---------------------------------------------------------------------------

/// 32-byte NIST SP 800-185 `cSHAKE256` (`N = ""`, `S = customization`), matching
/// `Obend.Digest.Cshake256.cshake256Bytes` and `Obend.Crypto.cshake32ByteArray` bit-for-bit.
pub use obend_keccak::cshake256_32 as she_cshake256_32;

/// Canonical unsigned LEB128 encoding matching `Obend.Crypto.Transcript.leb128`.
pub fn she_leb128(mut n: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(4);
    loop {
        if n < 128 {
            out.push(n as u8);
            return out;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
}

/// Length-prefixed byte field (`leb128(len(xs)) || xs`) matching `Obend.Crypto.encodeListField`.
pub fn encode_she_field(xs: &[u8]) -> Vec<u8> {
    let mut out = she_leb128(xs.len() as u64);
    out.extend_from_slice(xs);
    out
}

/// Concatenate length-prefixed fields matching `Obend.Polis.SecureHardwareEnv.encodeSheFields`.
pub fn encode_she_fields(fields: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for f in fields {
        out.extend_from_slice(&encode_she_field(f));
    }
    out
}

fn encode_nat_list(xs: &[u64]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = xs.iter().map(|&n| she_leb128(n)).collect();
    encode_she_fields(&mapped)
}

pub fn zigzag_encode(z: i64) -> u64 {
    ((z << 1) ^ (z >> 63)) as u64
}

fn encode_leaf_list(xs: &[(u64, usize)]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = xs
        .iter()
        .map(|&(a, b)| encode_she_fields(&[she_leb128(a), she_leb128(b as u64)]))
        .collect();
    encode_she_fields(&mapped)
}

fn encode_int(z: i64) -> Vec<u8> {
    she_leb128(zigzag_encode(z))
}

fn encode_int_list(xs: &[i64]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = xs.iter().map(|&z| encode_int(z)).collect();
    encode_she_fields(&mapped)
}

fn encode_int_matrix(rows: &[Vec<i64>]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = rows.iter().map(|r| encode_int_list(r)).collect();
    encode_she_fields(&mapped)
}

fn encode_bytes32_list(xs: &[[u8; 32]]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = xs.iter().map(|b| b.to_vec()).collect();
    encode_she_fields(&mapped)
}

// ---------------------------------------------------------------------------
// 1. Pure-Rust `PqHashSignatures` (`cshake256Suite`, `TSW`/`WOTS+C` + `XMSS` / `leanSPHINCS`)
// ---------------------------------------------------------------------------

pub const PQ_CSHAKE_SUITE_CUSTOM: &[u8] = b"OBEND.PQ.SUITE.CSHAKE256/v1";
const PQ_TAG_PRF_MSG: &[u8] = b"OBEND.PQ.PRFMSG/v1";
const PQ_TAG_H_MSG: &[u8] = b"OBEND.PQ.HMSG/v1";
const PQ_TAG_PRF: &[u8] = b"OBEND.PQ.PRF/v1";
const PQ_TAG_TH_F: &[u8] = b"OBEND.PQ.TH_F/v1";
const PQ_TAG_TH_H: &[u8] = b"OBEND.PQ.TH_H/v1";
const PQ_TAG_TH_TL: &[u8] = b"OBEND.PQ.TH_TL/v1";
const PQ_TAG_H_PRE: &[u8] = b"OBEND.PQ.PRE/v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdrsKind {
    WotsHash = 0,
    WotsPk = 1,
    Tree = 2,
    ForsTree = 3,
    ForsRoots = 4,
    WotsPrf = 5,
    ForsPrf = 6,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HashAdrs {
    pub layer: u32,
    pub tree: u64,
    pub kind: AdrsKind,
    pub key_pair: u32,
    pub chain_idx: u32,
    pub hash_step: u32,
}

impl HashAdrs {
    const ZERO: Self = Self {
        layer: 0,
        tree: 0,
        kind: AdrsKind::WotsHash,
        key_pair: 0,
        chain_idx: 0,
        hash_step: 0,
    };
}

/// Canonical 32-byte big-endian `ADRS` matching `Obend.Crypto.PqHashSignatures.encodeAdrs`.
pub fn encode_adrs(a: &HashAdrs) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&a.layer.to_be_bytes());
    out[8..16].copy_from_slice(&a.tree.to_be_bytes());
    out[16..20].copy_from_slice(&(a.kind as u32).to_be_bytes());
    out[20..24].copy_from_slice(&a.key_pair.to_be_bytes());
    out[24..28].copy_from_slice(&a.chain_idx.to_be_bytes());
    out[28..32].copy_from_slice(&a.hash_step.to_be_bytes());
    out
}

fn pq_encode_multi_frame(fields: &[&[u8]]) -> Vec<u8> {
    let mut out = she_leb128(fields.len() as u64);
    for f in fields {
        out.extend_from_slice(&she_leb128(f.len() as u64));
        out.extend_from_slice(f);
    }
    out
}

fn pq_th_call(role_tag: &[u8], pk_seed: &[u8], adrs: &HashAdrs, args: &[&[u8]]) -> [u8; 32] {
    let adrs_bytes = encode_adrs(adrs);
    let mut fields: Vec<&[u8]> = Vec::with_capacity(3 + args.len());
    fields.push(role_tag);
    fields.push(pk_seed);
    fields.push(&adrs_bytes);
    fields.extend_from_slice(args);
    let pre = pq_encode_multi_frame(&fields);
    she_cshake256_32(PQ_CSHAKE_SUITE_CUSTOM, &pre)
}

fn pq_th_chain_f(pk_seed: &[u8], adrs: &HashAdrs, x: &[u8; 32]) -> [u8; 32] {
    pq_th_call(PQ_TAG_TH_F, pk_seed, adrs, &[x])
}

fn pq_th_node_h(pk_seed: &[u8], adrs: &HashAdrs, l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    pq_th_call(PQ_TAG_TH_H, pk_seed, adrs, &[l, r])
}

fn pq_th_tweak_tl(pk_seed: &[u8], adrs: &HashAdrs, limbs: &[[u8; 32]]) -> [u8; 32] {
    let refs: Vec<&[u8]> = limbs.iter().map(|l| l.as_slice()).collect();
    pq_th_call(PQ_TAG_TH_TL, pk_seed, adrs, &refs)
}

fn pq_th_secret_prf(pk_seed: &[u8], sk_seed: &[u8], adrs: &HashAdrs) -> [u8; 32] {
    pq_th_call(PQ_TAG_PRF, pk_seed, adrs, &[sk_seed])
}

fn pq_th_prf_msg(sk_prf: &[u8], opt_rand: &[u8], mu: &[u8; 32]) -> [u8; 32] {
    pq_th_call(
        PQ_TAG_PRF_MSG,
        &[],
        &HashAdrs::ZERO,
        &[sk_prf, opt_rand, mu],
    )
}

fn pq_th_pre_hash(pk_seed: &[u8], pk_root: &[u8], msg: &[u8]) -> [u8; 32] {
    pq_th_call(PQ_TAG_H_PRE, pk_seed, &HashAdrs::ZERO, &[pk_root, msg])
}

fn pq_th_hash_msg(
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
    pq_th_call(
        PQ_TAG_H_MSG,
        pk_seed,
        &adrs,
        &[r_rand, pk_root, mu, &ctr_be],
    )
}

/// Unpack bytes into `ell1` base-`w` digits matching `PqHashSignatures.extractBaseWDigits`.
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

/// Load-bearing Target-Sum Winternitz (`TSW`) checker matching `PqHashSignatures.checkTargetSum`.
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

/// Parameter profile matching `Obend.Crypto.PqHashSignatures.PqHashParams`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    pub const SHE_STATEFUL_XMSS_256: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 2,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 2,
        stateful_lean_sig: true,
    };

    pub const SHE_STATELESS_SPHINCS_256: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 2,
        num_layers: 2,
        fors_trees: 20,
        fors_height: 5,
        max_sigs_log2: 4,
        stateful_lean_sig: false,
    };

    pub const THINCS_CUSTODY_128: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 6,
        num_layers: 2,
        fors_trees: 18,
        fors_height: 8,
        max_sigs_log2: 12,
        stateful_lean_sig: false,
    };

    pub const fn target_sum(&self) -> usize {
        (self.ell1 * self.w.saturating_sub(1)) / 2
    }

    pub const fn well_formed(&self) -> bool {
        self.num_layers > 0
            && self.w >= 2
            && self.w <= 256
            && self.ell1 > 0
            && self.subtree_height <= 30
            && self.fors_height <= 30
            && self.num_layers.saturating_mul(self.subtree_height) <= 62
            && (self.stateful_lean_sig || self.fors_trees > 0)
    }

    pub const fn she_policy_valid(&self) -> bool {
        self.well_formed()
            && self.w == 4
            && self.ell1 >= 128
            && self.num_layers == 1
            && self.stateful_lean_sig
            && self.subtree_height >= 2
            && self.subtree_height <= 20
            && self.max_sigs_log2 == self.subtree_height
    }

    pub const fn leaf_idx_in_range(&self, leaf_global_idx: usize) -> bool {
        let total_bits = self.num_layers.saturating_mul(self.subtree_height);
        if total_bits >= (usize::BITS as usize) {
            true
        } else {
            leaf_global_idx < (1usize << total_bits)
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            she_leb128(self.w as u64),
            she_leb128(self.ell1 as u64),
            she_leb128(self.subtree_height as u64),
            she_leb128(self.num_layers as u64),
            she_leb128(self.fors_trees as u64),
            she_leb128(self.fors_height as u64),
            she_leb128(self.max_sigs_log2 as u64),
            vec![u8::from(self.stateful_lean_sig)],
        ])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PqSecretKey {
    pub sk_seed: [u8; 32],
    pub sk_prf: [u8; 32],
    pub pk_seed: [u8; 32],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PqPublicKey {
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

impl PqPublicKey {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[self.pk_seed.to_vec(), self.pk_root.to_vec()])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LayerXmssSig {
    pub tsw_ctr: u32,
    pub wots_chains: Vec<[u8; 32]>,
    pub auth_path: Vec<[u8; 32]>,
}

impl LayerXmssSig {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            she_leb128(u64::from(self.tsw_ctr)),
            encode_bytes32_list(&self.wots_chains),
            encode_bytes32_list(&self.auth_path),
        ])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub secret_val: [u8; 32],
    pub auth_path: Vec<[u8; 32]>,
}

impl ForsTreeOpening {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            self.secret_val.to_vec(),
            encode_bytes32_list(&self.auth_path),
        ])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PqHashSig {
    pub r_rand: [u8; 32],
    pub msg_tsw_ctr: u32,
    pub leaf_global_idx: usize,
    pub fors_openings: Vec<ForsTreeOpening>,
    pub layer_sigs: Vec<LayerXmssSig>,
}

impl PqHashSig {
    pub fn encode(&self) -> Vec<u8> {
        let fors_enc: Vec<Vec<u8>> = self.fors_openings.iter().map(|o| o.encode()).collect();
        let layers_enc: Vec<Vec<u8>> = self.layer_sigs.iter().map(|l| l.encode()).collect();
        encode_she_fields(&[
            self.r_rand.to_vec(),
            she_leb128(u64::from(self.msg_tsw_ctr)),
            she_leb128(self.leaf_global_idx as u64),
            encode_she_fields(&fors_enc),
            encode_she_fields(&layers_enc),
        ])
    }
}

fn encode_indexed_pq_sig_list(sigs: &[(u64, PqHashSig)]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = sigs
        .iter()
        .map(|(idx, sig)| encode_she_fields(&[she_leb128(*idx), sig.encode()]))
        .collect();
    encode_she_fields(&mapped)
}

/// The address of one WOTS+ hash chain.
#[derive(Clone, Copy)]
struct WotsChain<'a> {
    pk_seed: &'a [u8; 32],
    layer: u32,
    tree: u64,
    key_pair: u32,
    chain: u32,
}

impl WotsChain<'_> {
    /// Applies `steps` chain hashes starting at position `start_step`.
    fn advance(&self, start_step: u32, steps: usize, mut cur: [u8; 32]) -> [u8; 32] {
        for s in 0..steps {
            let adrs = HashAdrs {
                layer: self.layer,
                tree: self.tree,
                kind: AdrsKind::WotsHash,
                key_pair: self.key_pair,
                chain_idx: self.chain,
                hash_step: start_step.wrapping_add(s as u32),
            };
            cur = pq_th_chain_f(self.pk_seed, &adrs, &cur);
        }
        cur
    }
}

fn pq_wots_secret_base(sk: &PqSecretKey, layer: u32, tree: u64, kp: u32, chain: u32) -> [u8; 32] {
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPrf,
        key_pair: kp,
        chain_idx: chain,
        hash_step: 0,
    };
    pq_th_secret_prf(&sk.pk_seed, &sk.sk_seed, &adrs)
}

fn pq_compute_wots_pk(
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    kp: u32,
) -> [u8; 32] {
    let mut endpoints = Vec::with_capacity(params.ell1);
    for r in 0..params.ell1 {
        let base = pq_wots_secret_base(sk, layer, tree, kp, r as u32);
        endpoints.push(
            WotsChain {
                pk_seed: &sk.pk_seed,
                layer,
                tree,
                key_pair: kp,
                chain: r as u32,
            }
            .advance(0, params.w - 1, base),
        );
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    pq_th_tweak_tl(&sk.pk_seed, &adrs, &endpoints)
}

/// Recover a WOTS+C public key from signature chain values matching `recoverWotsPkFromSig`.
pub fn recover_wots_pk_from_sig(
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
        endpoints.push(
            WotsChain {
                pk_seed,
                layer,
                tree,
                key_pair: kp,
                chain: r as u32,
            }
            .advance(dr as u32, rem, sig_val),
        );
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    pq_th_tweak_tl(pk_seed, &adrs, &endpoints)
}

/// The Merkle tree a node belongs to: public seed, hypertree layer, tree index, and node kind.
#[derive(Clone, Copy, Debug)]
struct MerkleTreeAddr<'a> {
    pk_seed: &'a [u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
}

impl MerkleTreeAddr<'_> {
    fn node_adrs(&self, height: usize, node_idx: usize) -> HashAdrs {
        HashAdrs {
            layer: self.layer,
            tree: self.tree,
            kind: self.node_kind,
            key_pair: 0,
            chain_idx: height as u32,
            hash_step: node_idx as u32,
        }
    }
}

fn pq_compute_merkle_node<F: Fn(usize) -> [u8; 32]>(
    addr: MerkleTreeAddr<'_>,
    leaf_fn: &F,
    height: usize,
    node_idx: usize,
) -> [u8; 32] {
    if height == 0 {
        leaf_fn(node_idx)
    } else {
        let left = pq_compute_merkle_node(addr, leaf_fn, height - 1, 2 * node_idx);
        let right = pq_compute_merkle_node(addr, leaf_fn, height - 1, 2 * node_idx + 1);
        pq_th_node_h(
            addr.pk_seed,
            &addr.node_adrs(height, node_idx),
            &left,
            &right,
        )
    }
}

fn pq_build_merkle_auth_path<F: Fn(usize) -> [u8; 32]>(
    addr: MerkleTreeAddr<'_>,
    leaf_fn: &F,
    height: usize,
    node_idx: usize,
    local_idx: usize,
) -> Vec<[u8; 32]> {
    if height == 0 {
        return Vec::new();
    }
    let half = 1usize << (height - 1);
    let (sibling_idx, child_idx, child_local) = if local_idx < half {
        (2 * node_idx + 1, 2 * node_idx, local_idx)
    } else {
        (2 * node_idx, 2 * node_idx + 1, local_idx - half)
    };
    let mut out = vec![pq_compute_merkle_node(
        addr,
        leaf_fn,
        height - 1,
        sibling_idx,
    )];
    out.extend(pq_build_merkle_auth_path(
        addr,
        leaf_fn,
        height - 1,
        child_idx,
        child_local,
    ));
    out
}

/// Top-down Merkle authentication path walker matching `PqHashSignatures.walkMerkleAuthPath`.
#[expect(
    clippy::too_many_arguments,
    reason = "preserve the public positional API"
)]
pub fn walk_merkle_auth_path(
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
    walk_path(
        MerkleTreeAddr {
            pk_seed,
            layer,
            tree,
            node_kind,
        },
        height,
        node_idx,
        local_idx,
        leaf_hash,
        auth_path,
    )
}

fn walk_path(
    addr: MerkleTreeAddr<'_>,
    height: usize,
    node_idx: usize,
    local_idx: usize,
    leaf_hash: [u8; 32],
    auth_path: &[[u8; 32]],
) -> Option<[u8; 32]> {
    if height == 0 {
        return auth_path.is_empty().then_some(leaf_hash);
    }
    let (&sib, rest) = auth_path.split_first()?;
    let half = 1usize << (height - 1);
    let adrs = addr.node_adrs(height, node_idx);
    if local_idx < half {
        let sub = walk_path(addr, height - 1, 2 * node_idx, local_idx, leaf_hash, rest)?;
        Some(pq_th_node_h(addr.pk_seed, &adrs, &sub, &sib))
    } else {
        let sub = walk_path(
            addr,
            height - 1,
            2 * node_idx + 1,
            local_idx - half,
            leaf_hash,
            rest,
        )?;
        Some(pq_th_node_h(addr.pk_seed, &adrs, &sib, &sub))
    }
}

fn pq_extract_bit_window(bytes: &[u8], start_bit: usize, width: usize) -> usize {
    if width == 0 {
        return 0;
    }
    let n_bytes = if bytes.is_empty() { 1 } else { bytes.len() };
    let mut acc = 0usize;
    for b in 0..width {
        let pos = start_bit + b;
        let byte_val = bytes.get((pos / 8) % n_bytes).copied().unwrap_or(0) as usize;
        acc = (acc << 1) | ((byte_val >> (pos % 8)) & 1);
    }
    if width < (usize::BITS as usize) {
        acc & ((1usize << width) - 1)
    } else {
        acc
    }
}

fn pq_derive_fors_indices(k: usize, a: usize, hmsg: &[u8]) -> Vec<usize> {
    (0..k)
        .map(|j| pq_extract_bit_window(hmsg, 88 + j * a, a))
        .collect()
}

fn pq_fors_secret_leaf(sk: &PqSecretKey, tree_idx: u64, kp_idx: u32, global_u: u32) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsPrf,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: global_u,
    };
    pq_th_secret_prf(&sk.pk_seed, &sk.sk_seed, &adrs)
}

fn pq_fors_leaf_hash(
    pk_seed: &[u8; 32],
    tree_idx: u64,
    kp_idx: u32,
    global_u: u32,
    sec_val: &[u8; 32],
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsTree,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: global_u,
    };
    pq_th_chain_f(pk_seed, &adrs, sec_val)
}

fn pq_compute_xmss_subtree_root(
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree_idx: u64,
) -> [u8; 32] {
    let leaf_fn = |kp: usize| pq_compute_wots_pk(params, sk, layer, tree_idx, kp as u32);
    pq_compute_merkle_node(
        MerkleTreeAddr {
            pk_seed: &sk.pk_seed,
            layer,
            tree: tree_idx,
            node_kind: AdrsKind::Tree,
        },
        &leaf_fn,
        params.subtree_height,
        0,
    )
}

/// Derive canonical `PqPublicKey` matching `Obend.Crypto.PqHashSignatures.derivePublicKey`.
pub fn derive_pq_public_key(params: &PqHashParams, sk: &PqSecretKey) -> PqPublicKey {
    let top_layer = params.num_layers.saturating_sub(1) as u32;
    PqPublicKey {
        pk_seed: sk.pk_seed,
        pk_root: pq_compute_xmss_subtree_root(params, sk, top_layer, 0),
    }
}

/// What `H_msg` binds besides the grinding counter.
#[derive(Clone, Copy)]
struct TswMessage<'a> {
    r_rand: &'a [u8; 32],
    pk_seed: &'a [u8],
    pk_root: &'a [u8],
    mu: &'a [u8; 32],
    layer_idx: u32,
    tree_idx: u64,
}

fn pq_grind_tsw_counter(
    params: &PqHashParams,
    message: &TswMessage<'_>,
    max_grind: u32,
) -> Option<(u32, Vec<usize>, [u8; 32])> {
    for ctr in 0..max_grind {
        let hmsg = pq_th_hash_msg(
            message.r_rand,
            message.pk_seed,
            message.pk_root,
            message.mu,
            message.layer_idx,
            message.tree_idx,
            ctr,
        );
        let digits = extract_base_w_digits(params.w, params.ell1, &hmsg);
        if check_target_sum(params.w, params.ell1, params.target_sum(), &digits) {
            return Some((ctr, digits, hmsg));
        }
    }
    None
}

/// Reference `cshake256Suite` `TSW`+`XMSS`/`leanSPHINCS` signer matching `evalSingleSign`.
pub fn eval_pq_single_sign(
    params: &PqHashParams,
    sk: &PqSecretKey,
    msg: &[u8],
    opt_rand: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
) -> Option<PqHashSig> {
    if !params.well_formed() || !params.leaf_idx_in_range(leaf_global_idx) {
        return None;
    }
    let pk = derive_pq_public_key(params, sk);
    let mu = pq_th_pre_hash(&pk.pk_seed, &pk.pk_root, msg);
    let r_rand = pq_th_prf_msg(&sk.sk_prf, opt_rand, &mu);
    let (msg_tsw_ctr, fors_openings, mut cur_root) = if params.stateful_lean_sig {
        (0u32, Vec::new(), mu)
    } else {
        let sub_leaves = 1usize << params.subtree_height;
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let (ctr0, _, hmsg0) = pq_grind_tsw_counter(
            params,
            &TswMessage {
                r_rand: &r_rand,
                pk_seed: &pk.pk_seed,
                pk_root: &pk.pk_root,
                mu: &mu,
                layer_idx: 0,
                tree_idx: tree0,
            },
            max_grind,
        )?;
        let idxs = pq_derive_fors_indices(params.fors_trees, params.fors_height, &hmsg0);
        let leaf_fn = |global_u: usize| {
            let sec = pq_fors_secret_leaf(sk, tree0, kp0, global_u as u32);
            pq_fors_leaf_hash(&sk.pk_seed, tree0, kp0, global_u as u32, &sec)
        };
        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate() {
            let global_u = j * (1usize << params.fors_height) + idx_j;
            let secret_val = pq_fors_secret_leaf(sk, tree0, kp0, global_u as u32);
            let auth_path = pq_build_merkle_auth_path(
                MerkleTreeAddr {
                    pk_seed: &sk.pk_seed,
                    layer: 0,
                    tree: tree0,
                    node_kind: AdrsKind::ForsTree,
                },
                &leaf_fn,
                params.fors_height,
                j,
                idx_j,
            );
            openings.push(ForsTreeOpening {
                secret_val,
                auth_path,
            });
            roots.push(pq_compute_merkle_node(
                MerkleTreeAddr {
                    pk_seed: &sk.pk_seed,
                    layer: 0,
                    tree: tree0,
                    node_kind: AdrsKind::ForsTree,
                },
                &leaf_fn,
                params.fors_height,
                j,
            ));
        }
        let fors_pk = pq_th_tweak_tl(
            &sk.pk_seed,
            &HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsRoots,
                key_pair: kp0,
                chain_idx: 0,
                hash_step: 0,
            },
            &roots,
        );
        (ctr0, openings, fors_pk)
    };

    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut global_idx = leaf_global_idx;
    let sub_leaves = 1usize << params.subtree_height;
    for layer_idx in 0..params.num_layers {
        let kp_idx = global_idx % sub_leaves;
        let tree_idx_nat = global_idx / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let (ctr, digits, _) = pq_grind_tsw_counter(
            params,
            &TswMessage {
                r_rand: &r_rand,
                pk_seed: &sk.pk_seed,
                pk_root: &pk.pk_root,
                mu: &cur_root,
                layer_idx: layer_u32,
                tree_idx,
            },
            max_grind,
        )?;
        let mut wots_chains = Vec::with_capacity(params.ell1);
        for (r, &dr) in digits.iter().enumerate() {
            let base = pq_wots_secret_base(sk, layer_u32, tree_idx, kp_idx as u32, r as u32);
            wots_chains.push(
                WotsChain {
                    pk_seed: &sk.pk_seed,
                    layer: layer_u32,
                    tree: tree_idx,
                    key_pair: kp_idx as u32,
                    chain: r as u32,
                }
                .advance(0, dr, base),
            );
        }
        let leaf_fn = |kp: usize| pq_compute_wots_pk(params, sk, layer_u32, tree_idx, kp as u32);
        let auth_path = pq_build_merkle_auth_path(
            MerkleTreeAddr {
                pk_seed: &sk.pk_seed,
                layer: layer_u32,
                tree: tree_idx,
                node_kind: AdrsKind::Tree,
            },
            &leaf_fn,
            params.subtree_height,
            0,
            kp_idx,
        );
        cur_root = pq_compute_xmss_subtree_root(params, sk, layer_u32, tree_idx);
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr,
            wots_chains,
            auth_path,
        });
        global_idx = tree_idx_nat;
    }

    Some(PqHashSig {
        r_rand,
        msg_tsw_ctr,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    })
}

/// Unified `cshake256Suite` verifier matching `Obend.Crypto.PqHashSignatures.verifyPqHashSig`.
pub fn verify_pq_hash_sig(
    params: &PqHashParams,
    pk: &PqPublicKey,
    msg: &[u8],
    sig: &PqHashSig,
) -> bool {
    if !params.well_formed()
        || sig.layer_sigs.len() != params.num_layers
        || !params.leaf_idx_in_range(sig.leaf_global_idx)
    {
        return false;
    }
    let mu = pq_th_pre_hash(&pk.pk_seed, &pk.pk_root, msg);
    let mut cur_root = if params.stateful_lean_sig {
        if !sig.fors_openings.is_empty() || sig.msg_tsw_ctr != 0 {
            return false;
        }
        mu
    } else {
        if sig.fors_openings.len() != params.fors_trees {
            return false;
        }
        let sub_leaves = 1usize << params.subtree_height;
        let kp0 = (sig.leaf_global_idx % sub_leaves) as u32;
        let tree0 = (sig.leaf_global_idx / sub_leaves) as u64;
        let hmsg0 = pq_th_hash_msg(
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
        let idxs = pq_derive_fors_indices(params.fors_trees, params.fors_height, &hmsg0);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for (j, (&idx_j, op)) in idxs.iter().zip(sig.fors_openings.iter()).enumerate() {
            let global_u = j * (1usize << params.fors_height) + idx_j;
            let leaf_h =
                pq_fors_leaf_hash(&pk.pk_seed, tree0, kp0, global_u as u32, &op.secret_val);
            let Some(rj) = walk_path(
                MerkleTreeAddr {
                    pk_seed: &pk.pk_seed,
                    layer: 0,
                    tree: tree0,
                    node_kind: AdrsKind::ForsTree,
                },
                params.fors_height,
                j,
                idx_j,
                leaf_h,
                &op.auth_path,
            ) else {
                return false;
            };
            roots.push(rj);
        }
        pq_th_tweak_tl(
            &pk.pk_seed,
            &HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsRoots,
                key_pair: kp0,
                chain_idx: 0,
                hash_step: 0,
            },
            &roots,
        )
    };

    let sub_leaves = 1usize << params.subtree_height;
    let mut global_idx = sig.leaf_global_idx;
    for (layer_idx, lsig) in sig.layer_sigs.iter().enumerate() {
        let kp_idx = global_idx % sub_leaves;
        let tree_idx_nat = global_idx / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let hmsg = pq_th_hash_msg(
            &sig.r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_idx,
            lsig.tsw_ctr,
        );
        let digits = extract_base_w_digits(params.w, params.ell1, &hmsg);
        if !check_target_sum(params.w, params.ell1, params.target_sum(), &digits)
            || lsig.wots_chains.len() != params.ell1
        {
            return false;
        }
        let wots_pk = recover_wots_pk_from_sig(
            params,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            kp_idx as u32,
            &digits,
            &lsig.wots_chains,
        );
        let Some(next_root) = walk_path(
            MerkleTreeAddr {
                pk_seed: &pk.pk_seed,
                layer: layer_u32,
                tree: tree_idx,
                node_kind: AdrsKind::Tree,
            },
            params.subtree_height,
            0,
            kp_idx,
            wots_pk,
            &lsig.auth_path,
        ) else {
            return false;
        };
        cur_root = next_root;
        global_idx = tree_idx_nat;
    }

    ct_eq(&cur_root, &pk.pk_root)
}

/// Canonical SHE PQ signature verifier matching `SecureHardwareEnv.verifyShePqSig`.
pub fn verify_she_pq_sig(
    params: &PqHashParams,
    pk: &PqPublicKey,
    msg: &[u8; 32],
    sig: &PqHashSig,
) -> bool {
    if !params.she_policy_valid()
        || sig.layer_sigs.len() != params.num_layers
        || (params.max_sigs_log2 < (usize::BITS as usize)
            && sig.leaf_global_idx >= (1usize << params.max_sigs_log2))
    {
        return false;
    }
    for ls in &sig.layer_sigs {
        if ls.wots_chains.len() != params.ell1 || ls.auth_path.len() != params.subtree_height {
            return false;
        }
    }
    if params.stateful_lean_sig {
        if !sig.fors_openings.is_empty() || sig.msg_tsw_ctr != 0 {
            return false;
        }
    } else if sig.fors_openings.len() != params.fors_trees
        || sig
            .fors_openings
            .iter()
            .any(|op| op.auth_path.len() != params.fors_height)
    {
        return false;
    }
    verify_pq_hash_sig(params, pk, msg, sig)
}

// ---------------------------------------------------------------------------
// 2. Floors, Grounded `ZkmlSuiteArtifact` (`UD-100`) & Bit-Exact `fpaudit` Integer Recompute
// ---------------------------------------------------------------------------

/// Minimum proven zkML soundness floor required for Sovereign SHE actuation (`100.000` bits).
pub const SHE_MIN_PROVEN_ZKML_MILLI_BITS: u64 = 100_000;

fn le64_at(b: &[u8], off: usize) -> u64 {
    let mut acc = 0u64;
    for i in 0..8 {
        let byte = b.get(off + i).copied().unwrap_or(0);
        acc |= u64::from(byte) << (8 * i);
    }
    acc
}

pub fn has_low_zero_bits(d: &[u8; 32], bits: usize) -> bool {
    if bits == 0 {
        return true;
    }
    if bits >= 64 {
        return false;
    }
    (le64_at(d, 0) & ((1u64 << bits) - 1)) == 0
}

/// Constitutional user-sovereign safety & privacy floors (`Obend.Polis.SecureHardwareEnv.SheFloor`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SheFloor {
    SensorRoiRedaction { min_redacted_rois: u64 },
    ConsentBandNonOcclusion { min_band_height_px: u64 },
    ZkmlProvenSoundnessMilliBits { min_milli_bits: u64 },
    PhysicalProximityMaxTicks { max_ticks: u64 },
    E2eeTeeChannelBound { min_attested_gpus: u64 },
    OperatorLocalRevert { max_revert_steps: u64 },
}

impl SheFloor {
    pub const fn is_bedrock(self) -> bool {
        matches!(self, Self::OperatorLocalRevert { .. })
    }

    pub const fn well_formed(self) -> bool {
        match self {
            Self::SensorRoiRedaction { .. } | Self::E2eeTeeChannelBound { .. } => true,
            Self::ConsentBandNonOcclusion { min_band_height_px } => min_band_height_px > 0,
            Self::ZkmlProvenSoundnessMilliBits { min_milli_bits } => {
                min_milli_bits >= SHE_MIN_PROVEN_ZKML_MILLI_BITS
            }
            Self::PhysicalProximityMaxTicks { max_ticks } => max_ticks > 0,
            Self::OperatorLocalRevert { max_revert_steps } => max_revert_steps > 0,
        }
    }

    pub fn encode(self) -> Vec<u8> {
        let (tag, val) = match self {
            Self::SensorRoiRedaction { min_redacted_rois } => (0x01u8, min_redacted_rois),
            Self::ConsentBandNonOcclusion { min_band_height_px } => (0x02u8, min_band_height_px),
            Self::ZkmlProvenSoundnessMilliBits { min_milli_bits } => (0x03u8, min_milli_bits),
            Self::PhysicalProximityMaxTicks { max_ticks } => (0x04u8, max_ticks),
            Self::E2eeTeeChannelBound { min_attested_gpus } => (0x05u8, min_attested_gpus),
            Self::OperatorLocalRevert { max_revert_steps } => (0x06u8, max_revert_steps),
        };
        let mut out = vec![tag];
        out.extend_from_slice(&she_leb128(val));
        out
    }
}

pub fn encode_she_floors(floors: &[SheFloor]) -> Vec<u8> {
    let encoded: Vec<Vec<u8>> = floors.iter().map(|f| f.encode()).collect();
    encode_she_fields(&encoded)
}

pub fn she_floors_digest(floors: &[SheFloor]) -> [u8; 32] {
    she_cshake256_32(b"OBEND.SHE.FLOORS/v1", &encode_she_floors(floors))
}

pub fn she_payload_digest(payload: &[u8]) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.PAYLOAD/v1",
        &encode_she_fields(&[payload.to_vec()]),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZkmlSoundnessRegime {
    UniqueDecodingUdr,
    JohnsonBoundJbr,
    WithdrawnCapacityBoundCbr,
}

impl ZkmlSoundnessRegime {
    pub const fn tag_byte(self) -> u8 {
        match self {
            Self::UniqueDecodingUdr => 0x01,
            Self::JohnsonBoundJbr => 0x02,
            Self::WithdrawnCapacityBoundCbr => 0x03,
        }
    }
}

pub const fn udr_per_query_milli_bits(log_blowup: u64) -> u64 {
    match log_blowup {
        0 => 0,
        1 => 415,
        2 => 678,
        3 => 830,
        4 => 912,
        5 => 955,
        6 => 977,
        7 => 988,
        _ => 994,
    }
}

pub const fn jbr_per_query_milli_bits(log_blowup: u64) -> u64 {
    log_blowup.saturating_mul(500)
}

/// Grounded `ZkmlSuiteArtifact` (`CROSS_REPO_CONTRACTS.md` §2 & `VERDICTS.md` `UD-100`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZkmlSuiteArtifact {
    pub suite_id: Vec<u8>,
    pub regime: ZkmlSoundnessRegime,
    pub log_blowup: u64,
    pub log_arity: u64,
    pub pinned_num_queries: u64,
    pub pow_bits: u64,
    pub ext_field_bits: u64,
}

impl ZkmlSuiteArtifact {
    pub fn canonical_ud100_small() -> Self {
        Self {
            suite_id: b"obend.einsu.goldilocks-ext2.mxfp4.cshake256.ud100.lb6.v1".to_vec(),
            regime: ZkmlSoundnessRegime::UniqueDecodingUdr,
            log_blowup: 6,
            log_arity: 1,
            pinned_num_queries: 86,
            pow_bits: 16,
            ext_field_bits: 128,
        }
    }

    pub fn canonical_ud100_wide_leaf() -> Self {
        Self {
            suite_id: b"obend.einsu.goldilocks-ext2.mxfp4.cshake256.ud100.lb2.v1".to_vec(),
            regime: ZkmlSoundnessRegime::UniqueDecodingUdr,
            log_blowup: 2,
            log_arity: 1,
            pinned_num_queries: 148,
            pow_bits: 0,
            ext_field_bits: 128,
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            self.suite_id.clone(),
            vec![self.regime.tag_byte()],
            she_leb128(self.log_blowup),
            she_leb128(self.log_arity),
            she_leb128(self.pinned_num_queries),
            she_leb128(self.pow_bits),
            she_leb128(self.ext_field_bits),
        ])
    }
}

pub fn suite_artifact_digest(s: &ZkmlSuiteArtifact) -> [u8; 32] {
    she_cshake256_32(b"OBEND.SHE.ZKML_SUITE/v1", &s.encode())
}

pub fn suite_proven_milli_bits(s: &ZkmlSuiteArtifact) -> u64 {
    if s.log_blowup == 0 || s.log_arity == 0 || s.pinned_num_queries == 0 {
        return 0;
    }
    let cap = s.ext_field_bits.saturating_mul(1_000).min(256_000);
    let grind_mbit = s.pow_bits.min(24).saturating_mul(1_000);
    match s.regime {
        ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr => 0,
        ZkmlSoundnessRegime::UniqueDecodingUdr => s
            .pinned_num_queries
            .saturating_mul(udr_per_query_milli_bits(s.log_blowup))
            .saturating_add(grind_mbit)
            .min(cap),
        ZkmlSoundnessRegime::JohnsonBoundJbr => s
            .pinned_num_queries
            .saturating_mul(jbr_per_query_milli_bits(s.log_blowup))
            .saturating_add(grind_mbit)
            .min(cap),
    }
}

pub fn legacy_withdrawn_cbr_milli_bits(s: &ZkmlSuiteArtifact) -> u64 {
    s.log_blowup
        .saturating_mul(s.pinned_num_queries)
        .saturating_mul(1_000)
        .saturating_add(s.pow_bits.saturating_mul(1_000))
}

pub fn check_suite_artifact(s: &ZkmlSuiteArtifact) -> bool {
    !s.suite_id.is_empty()
        && s.regime != ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr
        && s.log_blowup > 0
        && s.log_blowup <= 8
        && s.log_arity >= 1
        && s.pinned_num_queries > 0
        && s.pow_bits <= 24
        && suite_proven_milli_bits(s) >= SHE_MIN_PROVEN_ZKML_MILLI_BITS
}

/// Exact signed `s8` activation bounds `[-128, 127]`.
pub const fn is_s8(x: i64) -> bool {
    x >= -128 && x <= 127
}

/// Signed `E2M1` (`MXFP4`) integer mantissa domain `{0, +-1, +-2, +-3, +-4, +-6, +-8, +-12}`.
pub const E2M1_MANTISSAS: [i64; 15] = [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12];

pub fn is_e2m1_mantissa(q: i64) -> bool {
    E2M1_MANTISSAS.contains(&q)
}

/// Exact summation-order-invariant integer dot product matching `SecureHardwareEnv.exactIntDot`.
pub fn exact_int_dot(xs: &[i64], ws: &[i64]) -> i64 {
    let sum: i128 = xs
        .iter()
        .zip(ws.iter())
        .fold(0i128, |acc, (&x, &w)| acc + (x as i128) * (w as i128));
    i64::try_from(sum).expect("exact_int_dot overflow")
}

/// Overflow-safe exact `s8 x E2M1` (`MXFP4`) integer logits (`i128` accumulation, `shift <= 8`).
pub fn checked_exact_mxfp4_logits(
    xs: &[i64],
    weight_rows: &[Vec<i64>],
    block_shifts: &[u64],
) -> Option<Vec<i64>> {
    let mut out = Vec::with_capacity(weight_rows.len());
    for (row, &sh) in weight_rows.iter().zip(block_shifts.iter()) {
        if sh > 8 {
            return None;
        }
        let dot: i128 = xs.iter().zip(row.iter()).try_fold(0i128, |acc, (&x, &w)| {
            acc.checked_add((x as i128).checked_mul(w as i128)?)
        })?;
        let shifted = dot.checked_mul(1i128 << (sh as u32))?;
        out.push(i64::try_from(shifted).ok()?);
    }
    Some(out)
}

/// Exact `s8 x E2M1` (`MXFP4`) integer logits with power-of-two block shifts (`shift <= 8`).
pub fn exact_mxfp4_logits(xs: &[i64], weight_rows: &[Vec<i64>], block_shifts: &[u64]) -> Vec<i64> {
    checked_exact_mxfp4_logits(xs, weight_rows, block_shifts)
        .expect("validated s8 x E2M1 exact_mxfp4_logits must not overflow")
}

/// Deterministic first-maximum `argmaxIdx` matching `SecureHardwareEnv.argmaxIdx`.
pub fn argmax_idx(logits: &[i64]) -> usize {
    let Some(&first) = logits.first() else {
        return 0;
    };
    let mut best_idx = 0usize;
    let mut best_val = first;
    for (idx, &v) in logits.iter().enumerate().skip(1) {
        if best_val < v {
            best_idx = idx;
            best_val = v;
        }
    }
    best_idx
}

/// Logit-tolerance checker abstraction (`tau > 0` admits steered argmaxes, unlike exact `tau = 0`).
pub fn tolerance_logit_check(tau: u64, actual: &[i64], claimed: &[i64]) -> bool {
    if actual.len() != claimed.len() {
        return false;
    }
    actual
        .iter()
        .zip(claimed.iter())
        .all(|(&a, &b)| a.abs_diff(b) <= tau)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedRecomputeRound {
    pub round_idx: usize,
    pub input_root: [u8; 32],
    pub claimed_logits: Vec<i64>,
    pub claimed_argmax: usize,
}

impl CommittedRecomputeRound {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            she_leb128(self.round_idx as u64),
            self.input_root.to_vec(),
            encode_int_list(&self.claimed_logits),
            she_leb128(self.claimed_argmax as u64),
        ])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactRecomputeAudit {
    pub committed_rounds: Vec<CommittedRecomputeRound>,
    pub commit_root: [u8; 32],
    pub opened_round_idx: usize,
    pub opened_inputs: Vec<i64>,
    pub opened_weight_rows: Vec<Vec<i64>>,
    pub opened_block_shifts: Vec<u64>,
}

impl ExactRecomputeAudit {
    pub fn encode(&self) -> Vec<u8> {
        let rounds_enc: Vec<Vec<u8>> = self.committed_rounds.iter().map(|r| r.encode()).collect();
        encode_she_fields(&[
            encode_she_fields(&rounds_enc),
            self.commit_root.to_vec(),
            she_leb128(self.opened_round_idx as u64),
            encode_int_list(&self.opened_inputs),
            encode_int_matrix(&self.opened_weight_rows),
            encode_nat_list(&self.opened_block_shifts),
        ])
    }
}

/// Grounded `CandidateComputation` (`CROSS_REPO_CONTRACTS.md` §2): native code NEVER returns an acceptance bit!
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateComputation {
    pub suite: ZkmlSuiteArtifact,
    pub statement_digest: [u8; 32],
    pub model_weights_root: [u8; 32],
    pub input_root: [u8; 32],
    pub output_root: [u8; 32],
    pub bound_floors_digest: [u8; 32],
    pub action_payload_digest: [u8; 32],
    pub observed_num_queries: u64,
    pub proof_transcript_digest: [u8; 32],
    pub pow_nonce: u64,
    pub recompute_audit: ExactRecomputeAudit,
}

impl CandidateComputation {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            self.suite.encode(),
            self.statement_digest.to_vec(),
            self.model_weights_root.to_vec(),
            self.input_root.to_vec(),
            self.output_root.to_vec(),
            self.bound_floors_digest.to_vec(),
            self.action_payload_digest.to_vec(),
            she_leb128(self.observed_num_queries),
            self.proof_transcript_digest.to_vec(),
            she_leb128(self.pow_nonce),
            self.recompute_audit.encode(),
        ])
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "preserve the public positional API"
)]
pub fn candidate_statement_digest(
    suite: &ZkmlSuiteArtifact,
    model_weights_root: &[u8; 32],
    input_root: &[u8; 32],
    commit_root: &[u8; 32],
    output_root: &[u8; 32],
    num_rounds: usize,
    bound_floors_digest: &[u8; 32],
    action_payload_digest: &[u8; 32],
) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.ZKML_STMT/v1",
        &encode_she_fields(&[
            suite_artifact_digest(suite).to_vec(),
            model_weights_root.to_vec(),
            input_root.to_vec(),
            commit_root.to_vec(),
            output_root.to_vec(),
            she_leb128(num_rounds as u64),
            bound_floors_digest.to_vec(),
            action_payload_digest.to_vec(),
        ]),
    )
}

pub fn candidate_pow_hash(
    statement_digest: &[u8; 32],
    proof_transcript_digest: &[u8; 32],
    pow_nonce: u64,
) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.ZKML_POW/v1",
        &encode_she_fields(&[
            statement_digest.to_vec(),
            proof_transcript_digest.to_vec(),
            she_leb128(pow_nonce),
        ]),
    )
}

pub fn fpaudit_weights_root(weight_rows: &[Vec<i64>], block_shifts: &[u64]) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.FPAUDIT_WEIGHTS/v1",
        &encode_she_fields(&[
            encode_int_matrix(weight_rows),
            encode_nat_list(block_shifts),
        ]),
    )
}

pub fn fpaudit_input_root(sensor_seal_digest: &[u8; 32], xs: &[i64]) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.FPAUDIT_INPUT/v1",
        &encode_she_fields(&[sensor_seal_digest.to_vec(), encode_int_list(xs)]),
    )
}

pub fn fpaudit_round_hash(r: &CommittedRecomputeRound) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.FPAUDIT_ROUND/v1",
        &encode_she_fields(&[
            she_leb128(r.round_idx as u64),
            r.input_root.to_vec(),
            encode_int_list(&r.claimed_logits),
            she_leb128(r.claimed_argmax as u64),
        ]),
    )
}

pub fn fpaudit_commit_root(rounds: &[CommittedRecomputeRound]) -> [u8; 32] {
    let hashes: Vec<Vec<u8>> = rounds
        .iter()
        .map(|r| fpaudit_round_hash(r).to_vec())
        .collect();
    she_cshake256_32(b"OBEND.SHE.FPAUDIT_COMMIT/v1", &encode_she_fields(&hashes))
}

pub fn fpaudit_output_root(rounds: &[CommittedRecomputeRound]) -> [u8; 32] {
    let argmaxes: Vec<u64> = rounds.iter().map(|r| r.claimed_argmax as u64).collect();
    she_cshake256_32(b"OBEND.SHE.FPAUDIT_OUT/v1", &encode_nat_list(&argmaxes))
}

pub fn fpaudit_opened_round_idx(
    statement_digest: &[u8; 32],
    commit_root: &[u8; 32],
    output_root: &[u8; 32],
    proof_transcript_digest: &[u8; 32],
    pow_nonce: u64,
    num_rounds: usize,
) -> usize {
    if num_rounds == 0 {
        return 0;
    }
    let d = she_cshake256_32(
        b"OBEND.SHE.FPAUDIT_COIN/v1",
        &encode_she_fields(&[
            statement_digest.to_vec(),
            commit_root.to_vec(),
            output_root.to_vec(),
            proof_transcript_digest.to_vec(),
            she_leb128(pow_nonce),
        ]),
    );
    (le64_at(&d, 0) % (num_rounds as u64)) as usize
}

/// Verify commit-before-coin sampled bit-exact `s8 x E2M1` integer recompute (`SecureHardwareEnv.verifyExactRecomputeAudit`).
pub fn verify_exact_recompute_audit(c: &CandidateComputation) -> bool {
    let a = &c.recompute_audit;
    if a.committed_rounds.is_empty() {
        return false;
    }
    for (i, r) in a.committed_rounds.iter().enumerate() {
        if r.round_idx != i
            || r.claimed_logits.is_empty()
            || r.claimed_argmax != argmax_idx(&r.claimed_logits)
        {
            return false;
        }
    }
    if !ct_eq(&a.commit_root, &fpaudit_commit_root(&a.committed_rounds))
        || !ct_eq(&c.output_root, &fpaudit_output_root(&a.committed_rounds))
    {
        return false;
    }
    let expected_open = fpaudit_opened_round_idx(
        &c.statement_digest,
        &a.commit_root,
        &c.output_root,
        &c.proof_transcript_digest,
        c.pow_nonce,
        a.committed_rounds.len(),
    );
    if a.opened_round_idx != expected_open {
        return false;
    }
    let Some(opened) = a.committed_rounds.get(a.opened_round_idx) else {
        return false;
    };
    if a.opened_inputs.is_empty()
        || !a.opened_inputs.iter().all(|&x| is_s8(x))
        || a.opened_weight_rows.is_empty()
        || a.opened_weight_rows.len() != a.opened_block_shifts.len()
        || !a.opened_weight_rows.iter().all(|row| {
            row.len() == a.opened_inputs.len() && row.iter().all(|&q| is_e2m1_mantissa(q))
        })
        || !a.opened_block_shifts.iter().all(|&sh| sh <= 8)
    {
        return false;
    }
    if !ct_eq(
        &c.model_weights_root,
        &fpaudit_weights_root(&a.opened_weight_rows, &a.opened_block_shifts),
    ) || !ct_eq(
        &opened.input_root,
        &fpaudit_input_root(&c.input_root, &a.opened_inputs),
    ) {
        return false;
    }
    let Some(recomputed) = checked_exact_mxfp4_logits(
        &a.opened_inputs,
        &a.opened_weight_rows,
        &a.opened_block_shifts,
    ) else {
        return false;
    };
    recomputed == opened.claimed_logits && argmax_idx(&recomputed) == opened.claimed_argmax
}

/// Fail-closed grounded `CandidateComputation` verifier matching `SecureHardwareEnv.verifyCandidateComputation`.
pub fn verify_candidate_computation(c: &CandidateComputation) -> bool {
    if !check_suite_artifact(&c.suite) || c.observed_num_queries != c.suite.pinned_num_queries {
        return false;
    }
    let expected_stmt = candidate_statement_digest(
        &c.suite,
        &c.model_weights_root,
        &c.input_root,
        &c.recompute_audit.commit_root,
        &c.output_root,
        c.recompute_audit.committed_rounds.len(),
        &c.bound_floors_digest,
        &c.action_payload_digest,
    );
    if !ct_eq(&c.statement_digest, &expected_stmt) {
        return false;
    }
    if c.suite.pow_bits == 0 && c.pow_nonce != 0 {
        return false;
    }
    let pow_bits = (c.suite.pow_bits.min(24)) as usize;
    let pow_h = candidate_pow_hash(&c.statement_digest, &c.proof_transcript_digest, c.pow_nonce);
    if !has_low_zero_bits(&pow_h, pow_bits) {
        return false;
    }
    verify_exact_recompute_audit(c)
}

/// Realized proven soundness in milli-bits matching `SecureHardwareEnv.provenZkmlMilliBits`.
pub fn proven_zkml_milli_bits(c: &CandidateComputation) -> u64 {
    if verify_candidate_computation(c) {
        suite_proven_milli_bits(&c.suite)
    } else {
        0
    }
}

/// Honest builder for grounded `CandidateComputation` with optional PoW grinding (`pow_override = None` grinds live).
#[expect(
    clippy::too_many_arguments,
    reason = "preserve the public positional API"
)]
pub fn build_honest_candidate(
    suite: &ZkmlSuiteArtifact,
    sensor_seal_digest: [u8; 32],
    bound_floors_digest: [u8; 32],
    action_payload_digest: [u8; 32],
    proof_transcript_digest: [u8; 32],
    pow_override: Option<u64>,
    round_inputs: &[Vec<i64>],
    weight_rows: &[Vec<i64>],
    block_shifts: &[u64],
) -> CandidateComputation {
    let model_weights_root = fpaudit_weights_root(weight_rows, block_shifts);
    let committed_rounds: Vec<CommittedRecomputeRound> = round_inputs
        .iter()
        .enumerate()
        .map(|(i, xs)| {
            let logits = exact_mxfp4_logits(xs, weight_rows, block_shifts);
            let argmax = argmax_idx(&logits);
            CommittedRecomputeRound {
                round_idx: i,
                input_root: fpaudit_input_root(&sensor_seal_digest, xs),
                claimed_logits: logits,
                claimed_argmax: argmax,
            }
        })
        .collect();
    let commit_root = fpaudit_commit_root(&committed_rounds);
    let output_root = fpaudit_output_root(&committed_rounds);
    let statement_digest = candidate_statement_digest(
        suite,
        &model_weights_root,
        &sensor_seal_digest,
        &commit_root,
        &output_root,
        committed_rounds.len(),
        &bound_floors_digest,
        &action_payload_digest,
    );
    let pow_bits = (suite.pow_bits.min(24)) as usize;
    let pow_nonce = match pow_override {
        Some(n) => n,
        None => {
            let mut n = 0u64;
            loop {
                let h = candidate_pow_hash(&statement_digest, &proof_transcript_digest, n);
                if has_low_zero_bits(&h, pow_bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        }
    };
    let opened_round_idx = fpaudit_opened_round_idx(
        &statement_digest,
        &commit_root,
        &output_root,
        &proof_transcript_digest,
        pow_nonce,
        committed_rounds.len(),
    );
    let opened_inputs = round_inputs
        .get(opened_round_idx)
        .cloned()
        .unwrap_or_default();
    CandidateComputation {
        suite: suite.clone(),
        statement_digest,
        model_weights_root,
        input_root: sensor_seal_digest,
        output_root,
        bound_floors_digest,
        action_payload_digest,
        observed_num_queries: suite.pinned_num_queries,
        proof_transcript_digest,
        pow_nonce,
        recompute_audit: ExactRecomputeAudit {
            committed_rounds,
            commit_root,
            opened_round_idx,
            opened_inputs,
            opened_weight_rows: weight_rows.to_vec(),
            opened_block_shifts: block_shifts.to_vec(),
        },
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UpgradeAuthorityClaim {
    LocalCustodianCeremony,
    VendorRootDirective {
        vendor_sig: Vec<u8>,
    },
    AgencyEmergencyOrder {
        agency_id: Vec<u8>,
        agency_sig: Vec<u8>,
    },
}

impl UpgradeAuthorityClaim {
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Self::LocalCustodianCeremony => encode_she_fields(&[vec![0x01]]),
            Self::VendorRootDirective { vendor_sig } => {
                encode_she_fields(&[vec![0x02], vendor_sig.clone()])
            }
            Self::AgencyEmergencyOrder {
                agency_id,
                agency_sig,
            } => encode_she_fields(&[vec![0x03], agency_id.clone(), agency_sig.clone()]),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActuationTurnProposal {
    pub sensor_seq: u64,
    pub sensor_seal_digest: [u8; 32],
    pub candidate: CandidateComputation,
    pub nullifier: [u8; 32],
    pub mandate_cost: u64,
    pub redacted_roi_count: u64,
    pub consent_band_height_px: u64,
    pub attested_gpu_count: u64,
    pub shared_ring_at_copy: Vec<u8>,
    pub private_frame_copy: Vec<u8>,
    pub dispatched_payload: Vec<u8>,
    pub simplex_committee_n: u64,
    pub simplex_faulty_f: u64,
    pub simplex_qc_signatures: Vec<(u64, PqHashSig)>,
    pub custodian_epoch: u64,
    pub custodian_signatures: Vec<(u64, PqHashSig)>,
    pub tof_round_trip_ticks: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpgradeJudgeProposal {
    pub new_judge_digest: [u8; 32],
    pub new_model_weights_root: [u8; 32],
    pub new_zkml_suite_digest: [u8; 32],
    pub new_floors: Vec<SheFloor>,
    pub new_revert_window_steps: u64,
    pub new_custodian_epoch: u64,
    pub custodian_signatures: Vec<(u64, PqHashSig)>,
    pub tof_round_trip_ticks: u64,
    pub authority_claim: UpgradeAuthorityClaim,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MandateAttenuation {
    pub new_budget_cap: u64,
    pub new_max_proximity_ticks: u64,
    pub newly_revoked_custodians: Vec<u64>,
    pub reason_digest: [u8; 32],
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SheTurn {
    ProposeAndSettleActuation(ActuationTurnProposal),
    UpgradeHabitatJudge(UpgradeJudgeProposal),
    RevokeOrAttenuateMandate(MandateAttenuation),
}

fn encode_unsigned_actuation(act: &ActuationTurnProposal) -> Vec<u8> {
    encode_she_fields(&[
        she_leb128(act.sensor_seq),
        act.sensor_seal_digest.to_vec(),
        act.candidate.encode(),
        act.nullifier.to_vec(),
        she_leb128(act.mandate_cost),
        she_leb128(act.redacted_roi_count),
        she_leb128(act.consent_band_height_px),
        she_leb128(act.attested_gpu_count),
        act.shared_ring_at_copy.clone(),
        act.private_frame_copy.clone(),
        act.dispatched_payload.clone(),
        she_leb128(act.simplex_committee_n),
        she_leb128(act.simplex_faulty_f),
        she_leb128(act.custodian_epoch),
        she_leb128(act.tof_round_trip_ticks),
    ])
}

fn encode_unsigned_upgrade(up: &UpgradeJudgeProposal) -> Vec<u8> {
    encode_she_fields(&[
        up.new_judge_digest.to_vec(),
        up.new_model_weights_root.to_vec(),
        up.new_zkml_suite_digest.to_vec(),
        encode_she_floors(&up.new_floors),
        she_leb128(up.new_revert_window_steps),
        she_leb128(up.new_custodian_epoch),
        she_leb128(up.tof_round_trip_ticks),
        up.authority_claim.encode(),
    ])
}

/// Domain-separated pre-state anchor (`OBEND.SHE.STATE/v1`) matching `SecureHardwareEnv.sheStateDigest`.
pub fn she_state_digest(st: &SheState) -> [u8; 32] {
    let cust_pks_enc: Vec<Vec<u8>> = st.custodian_pks.iter().map(|pk| pk.encode()).collect();
    let simp_pks_enc: Vec<Vec<u8>> = st
        .simplex_validator_pks
        .iter()
        .map(|pk| pk.encode())
        .collect();
    let settled_digests: Vec<[u8; 32]> = st
        .settled_outbox_actions
        .iter()
        .map(|r| r.turn_envelope_digest)
        .collect();
    she_cshake256_32(
        b"OBEND.SHE.STATE/v1",
        &encode_she_fields(&[
            st.habitat_judge_digest.to_vec(),
            st.pinned_model_weights_root.to_vec(),
            st.pinned_zkml_suite_digest.to_vec(),
            she_leb128(st.mono_sensor_seq),
            encode_bytes32_list(&st.consumed_nullifiers),
            she_leb128(st.remaining_mandate_budget),
            she_floors_digest(&st.active_safety_and_privacy_floors).to_vec(),
            encode_bytes32_list(&settled_digests),
            st.pq_params.encode(),
            encode_she_fields(&cust_pks_enc),
            encode_she_fields(&simp_pks_enc),
            encode_leaf_list(&st.consumed_custodian_leaves),
            encode_leaf_list(&st.consumed_simplex_leaves),
            she_leb128(st.custodian_threshold_t),
            she_leb128(st.custodian_total_n),
            she_leb128(st.custodian_quorum_epoch),
            encode_nat_list(&st.revoked_custodians),
            she_leb128(st.max_proximity_ticks),
            she_leb128(st.revert_window_steps),
        ]),
    )
}

/// Domain-separated custodian actuation signing message (`OBEND.SHE.CUSTODIAN_SIG/v1`).
pub fn she_custodian_actuation_msg(st: &SheState, act: &ActuationTurnProposal) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.CUSTODIAN_SIG/v1",
        &encode_she_fields(&[
            she_state_digest(st).to_vec(),
            vec![0x01],
            she_leb128(act.custodian_epoch),
            encode_unsigned_actuation(act),
        ]),
    )
}

/// Domain-separated custodian upgrade signing message (`OBEND.SHE.CUSTODIAN_SIG/v1`).
pub fn she_custodian_upgrade_msg(st: &SheState, up: &UpgradeJudgeProposal) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.CUSTODIAN_SIG/v1",
        &encode_she_fields(&[
            she_state_digest(st).to_vec(),
            vec![0x02],
            she_leb128(up.new_custodian_epoch),
            encode_unsigned_upgrade(up),
        ]),
    )
}

/// Domain-separated Simplex `FINALIZE` (`0x02`) QC signing message (`OBEND.SHE.SIMPLEX_QC/v1`).
pub fn she_simplex_qc_msg(st: &SheState, act: &ActuationTurnProposal) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.SIMPLEX_QC/v1",
        &encode_she_fields(&[
            she_state_digest(st).to_vec(),
            vec![0x02],
            she_leb128(act.simplex_committee_n),
            she_leb128(act.simplex_faulty_f),
            encode_unsigned_actuation(act),
        ]),
    )
}

/// Canonical `OBEND.SHE.TURN/v1` length-framed preimage matching `SecureHardwareEnv.sheTurnPreimage`.
pub fn she_turn_preimage(turn: &SheTurn) -> Vec<u8> {
    let fields: Vec<Vec<u8>> = match turn {
        SheTurn::ProposeAndSettleActuation(act) => vec![
            vec![0x01],
            she_leb128(act.sensor_seq),
            act.sensor_seal_digest.to_vec(),
            act.candidate.encode(),
            act.nullifier.to_vec(),
            she_leb128(act.mandate_cost),
            she_leb128(act.redacted_roi_count),
            she_leb128(act.consent_band_height_px),
            she_leb128(act.attested_gpu_count),
            act.shared_ring_at_copy.clone(),
            act.private_frame_copy.clone(),
            act.dispatched_payload.clone(),
            she_leb128(act.simplex_committee_n),
            she_leb128(act.simplex_faulty_f),
            encode_indexed_pq_sig_list(&act.simplex_qc_signatures),
            she_leb128(act.custodian_epoch),
            encode_indexed_pq_sig_list(&act.custodian_signatures),
            she_leb128(act.tof_round_trip_ticks),
        ],
        SheTurn::UpgradeHabitatJudge(up) => vec![
            vec![0x02],
            up.new_judge_digest.to_vec(),
            up.new_model_weights_root.to_vec(),
            up.new_zkml_suite_digest.to_vec(),
            encode_she_floors(&up.new_floors),
            she_leb128(up.new_revert_window_steps),
            she_leb128(up.new_custodian_epoch),
            encode_indexed_pq_sig_list(&up.custodian_signatures),
            she_leb128(up.tof_round_trip_ticks),
            up.authority_claim.encode(),
        ],
        SheTurn::RevokeOrAttenuateMandate(rev) => vec![
            vec![0x03],
            she_leb128(rev.new_budget_cap),
            she_leb128(rev.new_max_proximity_ticks),
            encode_nat_list(&rev.newly_revoked_custodians),
            rev.reason_digest.to_vec(),
        ],
    };
    encode_she_fields(&fields)
}

pub fn she_turn_envelope_digest(turn: &SheTurn) -> [u8; 32] {
    she_cshake256_32(b"OBEND.SHE.TURN/v1", &she_turn_preimage(turn))
}

// ---------------------------------------------------------------------------
// 3. Persistent Sovereign SHE State, Refusals, & `apply_she_turn`
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SettledActuationRecord {
    pub sensor_seq: u64,
    pub sensor_seal_digest: [u8; 32],
    pub nullifier: [u8; 32],
    pub mandate_cost: u64,
    pub redacted_roi_count: u64,
    pub consent_band_height_px: u64,
    pub attested_gpu_count: u64,
    pub proven_zkml_milli_bits: u64,
    pub zkml_regime: ZkmlSoundnessRegime,
    pub zkml_log_arity: u64,
    pub zkml_observed_queries: u64,
    pub zkml_pinned_queries: u64,
    pub zkml_suite_digest: [u8; 32],
    pub fpaudit_commit_root: [u8; 32],
    pub fpaudit_opened_round_idx: usize,
    pub model_weights_root: [u8; 32],
    pub active_floors_at_settlement: Vec<SheFloor>,
    pub bound_floors_digest: [u8; 32],
    pub revert_window_at_settlement: u64,
    pub shared_ring_at_copy: Vec<u8>,
    pub private_frame_copy: Vec<u8>,
    pub dispatched_payload: Vec<u8>,
    pub simplex_committee_n: u64,
    pub simplex_faulty_f: u64,
    pub simplex_quorum_count: usize,
    pub simplex_qc_signatures: Vec<(u64, PqHashSig)>,
    pub simplex_qc_signing_msg: [u8; 32],
    pub custodian_epoch: u64,
    pub custodian_signers: Vec<u64>,
    pub custodian_signatures: Vec<(u64, PqHashSig)>,
    pub custodian_signing_msg: [u8; 32],
    pub tof_round_trip_ticks: u64,
    pub max_proximity_ticks_at_settle: u64,
    pub turn_envelope_digest: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SheState {
    pub habitat_judge_digest: [u8; 32],
    pub pinned_model_weights_root: [u8; 32],
    pub pinned_zkml_suite_digest: [u8; 32],
    pub mono_sensor_seq: u64,
    pub consumed_nullifiers: Vec<[u8; 32]>,
    pub remaining_mandate_budget: u64,
    pub active_safety_and_privacy_floors: Vec<SheFloor>,
    pub settled_outbox_actions: Vec<SettledActuationRecord>,
    pub pq_params: PqHashParams,
    pub custodian_pks: Vec<PqPublicKey>,
    pub simplex_validator_pks: Vec<PqPublicKey>,
    pub consumed_custodian_leaves: Vec<(u64, usize)>,
    pub consumed_simplex_leaves: Vec<(u64, usize)>,
    pub custodian_threshold_t: u64,
    pub custodian_total_n: u64,
    pub custodian_quorum_epoch: u64,
    pub revoked_custodians: Vec<u64>,
    pub max_proximity_ticks: u64,
    pub revert_window_steps: u64,
}

impl SheState {
    pub fn settled_total_cost(&self) -> u64 {
        self.settled_outbox_actions
            .iter()
            .fold(0u64, |acc, r| acc.saturating_add(r.mandate_cost))
    }

    pub fn well_formed_config(&self) -> bool {
        check_slice_nodup(&self.active_safety_and_privacy_floors)
            && self
                .active_safety_and_privacy_floors
                .iter()
                .any(|f| f.is_bedrock())
            && self
                .active_safety_and_privacy_floors
                .iter()
                .all(|f| f.well_formed())
            && self.pq_params.she_policy_valid()
            && (self.custodian_pks.len() as u64) == self.custodian_total_n
            && check_slice_nodup(&self.custodian_pks)
            && !self.simplex_validator_pks.is_empty()
            && check_slice_nodup(&self.simplex_validator_pks)
            && self
                .custodian_pks
                .iter()
                .all(|pk| !self.simplex_validator_pks.contains(pk))
            && self.custodian_threshold_t >= 1
            && self.custodian_threshold_t <= self.custodian_total_n
            && self.max_proximity_ticks > 0
    }

    pub fn well_formed(&self) -> bool {
        self.well_formed_config()
            && self.settled_outbox_actions.is_empty()
            && self.consumed_nullifiers.is_empty()
            && self.consumed_custodian_leaves.is_empty()
            && self.consumed_simplex_leaves.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SheRefusal {
    MalformedInitialState,
    InvalidDigestWidth,
    NonMonotoneSensorSeq {
        current_seq: u64,
        proposed_seq: u64,
    },
    SensorSealMismatch,
    ZkmlProofUnverified,
    ZkmlSuiteNotPinned,
    WithdrawnCbrRegimeRefused,
    BelowProven100BitFloor {
        actual_milli_bits: u64,
    },
    ModelWeightsRootMismatch,
    FloorsDigestMismatch,
    PayloadDigestMismatch,
    FloorConstraintViolated(SheFloor),
    NullifierReplayed,
    MandateBudgetExceeded {
        requested: u64,
        available: u64,
    },
    PrivateFrameCopyMismatch,
    InvalidSimplexCommittee {
        committee_n: u64,
        faulty_f: u64,
    },
    InvalidSimplexFinalityQc {
        signed_count: usize,
        required_quorum: u64,
    },
    InvalidSimplexPqSignature {
        validator: u64,
    },
    CustodianEpochMismatch {
        expected: u64,
        actual: u64,
    },
    DuplicateOrOutOfRangeSigner,
    RevokedCustodianSigner {
        signer: u64,
    },
    InsufficientCustodianQuorum {
        signed_count: usize,
        required_t: u64,
    },
    InvalidCustodianPqSignature {
        signer: u64,
    },
    ReusedStatefulPqLeaf {
        signer: u64,
        leaf_idx: usize,
    },
    TofProximityExceeded {
        actual_ticks: u64,
        max_ticks: u64,
    },
    CoerciveFloorDowngrade {
        dropped_floor: SheFloor,
    },
    ExternalAuthorityRefused,
    MalformedFloorSet,
    NonMonotoneCustodianEpoch {
        current_epoch: u64,
        proposed_epoch: u64,
    },
    MandateAmplificationRefused,
    ProximityWideningRefused {
        proposed_ticks: u64,
        current_max_ticks: u64,
    },
    OracleEvidenceBindingMismatch,
}

fn check_slice_nodup<T: PartialEq>(xs: &[T]) -> bool {
    for (i, x) in xs.iter().enumerate() {
        if xs[i + 1..].contains(x) {
            return false;
        }
    }
    true
}

fn check_strictly_increasing(xs: &[u64]) -> bool {
    xs.windows(2).all(|w| w[0] < w[1])
}

fn check_floor_on_actuation(
    revert_steps: u64,
    act: &ActuationTurnProposal,
    floor: SheFloor,
) -> bool {
    match floor {
        SheFloor::SensorRoiRedaction { min_redacted_rois } => {
            act.redacted_roi_count >= min_redacted_rois
        }
        SheFloor::ConsentBandNonOcclusion { min_band_height_px } => {
            min_band_height_px > 0 && act.consent_band_height_px >= min_band_height_px
        }
        SheFloor::ZkmlProvenSoundnessMilliBits { min_milli_bits } => {
            proven_zkml_milli_bits(&act.candidate) >= min_milli_bits
        }
        SheFloor::PhysicalProximityMaxTicks { max_ticks } => act.tof_round_trip_ticks <= max_ticks,
        SheFloor::E2eeTeeChannelBound { min_attested_gpus } => {
            act.attested_gpu_count >= min_attested_gpus
        }
        SheFloor::OperatorLocalRevert { max_revert_steps } => revert_steps <= max_revert_steps,
    }
}

fn check_custodian_pq_quorum(
    st: &SheState,
    msg: &[u8; 32],
    sigs: &[(u64, PqHashSig)],
) -> Result<(), SheRefusal> {
    let signers: Vec<u64> = sigs.iter().map(|(i, _)| *i).collect();
    if st.custodian_threshold_t < 1
        || st.custodian_threshold_t > st.custodian_total_n
        || (st.custodian_pks.len() as u64) != st.custodian_total_n
        || !check_slice_nodup(&st.custodian_pks)
    {
        return Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: sigs.len(),
            required_t: st.custodian_threshold_t,
        });
    }
    if !check_strictly_increasing(&signers) || !signers.iter().all(|&s| s < st.custodian_total_n) {
        return Err(SheRefusal::DuplicateOrOutOfRangeSigner);
    }
    if let Some(&rev) = signers
        .iter()
        .find(|&&s| st.revoked_custodians.contains(&s))
    {
        return Err(SheRefusal::RevokedCustodianSigner { signer: rev });
    }
    if st.pq_params.stateful_lean_sig {
        if let Some((signer, sig)) = sigs.iter().find(|(s, sg)| {
            st.consumed_custodian_leaves
                .contains(&(*s, sg.leaf_global_idx))
        }) {
            return Err(SheRefusal::ReusedStatefulPqLeaf {
                signer: *signer,
                leaf_idx: sig.leaf_global_idx,
            });
        }
    }
    for (signer, sig) in sigs {
        let Some(pk) = st.custodian_pks.get(*signer as usize) else {
            return Err(SheRefusal::InvalidCustodianPqSignature { signer: *signer });
        };
        if !verify_she_pq_sig(&st.pq_params, pk, msg, sig) {
            return Err(SheRefusal::InvalidCustodianPqSignature { signer: *signer });
        }
    }
    if (sigs.len() as u64) < st.custodian_threshold_t {
        return Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: sigs.len(),
            required_t: st.custodian_threshold_t,
        });
    }
    Ok(())
}

fn check_simplex_pq_quorum(
    st: &SheState,
    msg: &[u8; 32],
    committee_n: u64,
    faulty_f: u64,
    sigs: &[(u64, PqHashSig)],
) -> Result<(), SheRefusal> {
    let Some(min_committee) = faulty_f.checked_mul(3).and_then(|v| v.checked_add(1)) else {
        return Err(SheRefusal::InvalidSimplexCommittee {
            committee_n,
            faulty_f,
        });
    };
    if committee_n < min_committee
        || committee_n != (st.simplex_validator_pks.len() as u64)
        || !check_slice_nodup(&st.simplex_validator_pks)
    {
        return Err(SheRefusal::InvalidSimplexCommittee {
            committee_n,
            faulty_f,
        });
    }
    let signers: Vec<u64> = sigs.iter().map(|(v, _)| *v).collect();
    let required_qc = committee_n - faulty_f;
    if !check_strictly_increasing(&signers)
        || !signers.iter().all(|&v| v < committee_n)
        || (sigs.len() as u64) < required_qc
    {
        return Err(SheRefusal::InvalidSimplexFinalityQc {
            signed_count: sigs.len(),
            required_quorum: required_qc,
        });
    }
    if st.pq_params.stateful_lean_sig {
        if let Some((validator, sig)) = sigs.iter().find(|(v, sg)| {
            st.consumed_simplex_leaves
                .contains(&(*v, sg.leaf_global_idx))
        }) {
            return Err(SheRefusal::ReusedStatefulPqLeaf {
                signer: *validator,
                leaf_idx: sig.leaf_global_idx,
            });
        }
    }
    for (validator, sig) in sigs {
        let Some(pk) = st.simplex_validator_pks.get(*validator as usize) else {
            return Err(SheRefusal::InvalidSimplexPqSignature {
                validator: *validator,
            });
        };
        if !verify_she_pq_sig(&st.pq_params, pk, msg, sig) {
            return Err(SheRefusal::InvalidSimplexPqSignature {
                validator: *validator,
            });
        }
    }
    Ok(())
}

/// Deterministic single-turn Sovereign SHE transition gate matching `SecureHardwareEnv.applySheTurn`.
pub fn apply_she_turn(st: &SheState, turn: &SheTurn) -> Result<SheState, SheRefusal> {
    match turn {
        SheTurn::ProposeAndSettleActuation(act) => {
            if act.sensor_seq <= st.mono_sensor_seq {
                return Err(SheRefusal::NonMonotoneSensorSeq {
                    current_seq: st.mono_sensor_seq,
                    proposed_seq: act.sensor_seq,
                });
            }
            if !ct_eq(&act.candidate.input_root, &act.sensor_seal_digest) {
                return Err(SheRefusal::SensorSealMismatch);
            }
            if act.candidate.suite.regime == ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr {
                return Err(SheRefusal::WithdrawnCbrRegimeRefused);
            }
            if !verify_candidate_computation(&act.candidate) {
                return Err(SheRefusal::ZkmlProofUnverified);
            }
            if !ct_eq(
                &suite_artifact_digest(&act.candidate.suite),
                &st.pinned_zkml_suite_digest,
            ) {
                return Err(SheRefusal::ZkmlSuiteNotPinned);
            }
            let milli_bits = proven_zkml_milli_bits(&act.candidate);
            if milli_bits < SHE_MIN_PROVEN_ZKML_MILLI_BITS {
                return Err(SheRefusal::BelowProven100BitFloor {
                    actual_milli_bits: milli_bits,
                });
            }
            if !ct_eq(
                &act.candidate.model_weights_root,
                &st.pinned_model_weights_root,
            ) {
                return Err(SheRefusal::ModelWeightsRootMismatch);
            }
            let expected_floors_dig = she_floors_digest(&st.active_safety_and_privacy_floors);
            if !ct_eq(&act.candidate.bound_floors_digest, &expected_floors_dig) {
                return Err(SheRefusal::FloorsDigestMismatch);
            }
            let expected_payload_dig = she_payload_digest(&act.private_frame_copy);
            if !ct_eq(&act.candidate.action_payload_digest, &expected_payload_dig) {
                return Err(SheRefusal::PayloadDigestMismatch);
            }
            if act.tof_round_trip_ticks > st.max_proximity_ticks {
                return Err(SheRefusal::TofProximityExceeded {
                    actual_ticks: act.tof_round_trip_ticks,
                    max_ticks: st.max_proximity_ticks,
                });
            }
            if let Some(&violated) = st
                .active_safety_and_privacy_floors
                .iter()
                .find(|&&f| !check_floor_on_actuation(st.revert_window_steps, act, f))
            {
                return Err(SheRefusal::FloorConstraintViolated(violated));
            }
            if st
                .consumed_nullifiers
                .iter()
                .any(|n| ct_eq(n, &act.nullifier))
            {
                return Err(SheRefusal::NullifierReplayed);
            }
            if act.mandate_cost > st.remaining_mandate_budget {
                return Err(SheRefusal::MandateBudgetExceeded {
                    requested: act.mandate_cost,
                    available: st.remaining_mandate_budget,
                });
            }
            if act.private_frame_copy != act.shared_ring_at_copy
                || act.dispatched_payload != act.private_frame_copy
            {
                return Err(SheRefusal::PrivateFrameCopyMismatch);
            }
            let simplex_msg = she_simplex_qc_msg(st, act);
            check_simplex_pq_quorum(
                st,
                &simplex_msg,
                act.simplex_committee_n,
                act.simplex_faulty_f,
                &act.simplex_qc_signatures,
            )?;
            if act.custodian_epoch != st.custodian_quorum_epoch {
                return Err(SheRefusal::CustodianEpochMismatch {
                    expected: st.custodian_quorum_epoch,
                    actual: act.custodian_epoch,
                });
            }
            let custodian_msg = she_custodian_actuation_msg(st, act);
            check_custodian_pq_quorum(st, &custodian_msg, &act.custodian_signatures)?;

            let turn_envelope_digest = she_turn_envelope_digest(turn);
            let record = SettledActuationRecord {
                sensor_seq: act.sensor_seq,
                sensor_seal_digest: act.sensor_seal_digest,
                nullifier: act.nullifier,
                mandate_cost: act.mandate_cost,
                redacted_roi_count: act.redacted_roi_count,
                consent_band_height_px: act.consent_band_height_px,
                attested_gpu_count: act.attested_gpu_count,
                proven_zkml_milli_bits: milli_bits,
                zkml_regime: act.candidate.suite.regime,
                zkml_log_arity: act.candidate.suite.log_arity,
                zkml_observed_queries: act.candidate.observed_num_queries,
                zkml_pinned_queries: act.candidate.suite.pinned_num_queries,
                zkml_suite_digest: suite_artifact_digest(&act.candidate.suite),
                fpaudit_commit_root: act.candidate.recompute_audit.commit_root,
                fpaudit_opened_round_idx: act.candidate.recompute_audit.opened_round_idx,
                model_weights_root: act.candidate.model_weights_root,
                active_floors_at_settlement: st.active_safety_and_privacy_floors.clone(),
                bound_floors_digest: act.candidate.bound_floors_digest,
                revert_window_at_settlement: st.revert_window_steps,
                shared_ring_at_copy: act.shared_ring_at_copy.clone(),
                private_frame_copy: act.private_frame_copy.clone(),
                dispatched_payload: act.dispatched_payload.clone(),
                simplex_committee_n: act.simplex_committee_n,
                simplex_faulty_f: act.simplex_faulty_f,
                simplex_quorum_count: act.simplex_qc_signatures.len(),
                simplex_qc_signatures: act.simplex_qc_signatures.clone(),
                simplex_qc_signing_msg: simplex_msg,
                custodian_epoch: act.custodian_epoch,
                custodian_signers: act.custodian_signatures.iter().map(|(i, _)| *i).collect(),
                custodian_signatures: act.custodian_signatures.clone(),
                custodian_signing_msg: custodian_msg,
                tof_round_trip_ticks: act.tof_round_trip_ticks,
                max_proximity_ticks_at_settle: st.max_proximity_ticks,
                turn_envelope_digest,
            };

            let mut next = st.clone();
            next.mono_sensor_seq = act.sensor_seq;
            next.consumed_nullifiers.push(act.nullifier);
            next.remaining_mandate_budget -= act.mandate_cost;
            for (s, sig) in &act.custodian_signatures {
                next.consumed_custodian_leaves
                    .push((*s, sig.leaf_global_idx));
            }
            for (v, sig) in &act.simplex_qc_signatures {
                next.consumed_simplex_leaves.push((*v, sig.leaf_global_idx));
            }
            next.settled_outbox_actions.push(record);
            Ok(next)
        }
        SheTurn::UpgradeHabitatJudge(up) => {
            if let Some(&dropped) = st
                .active_safety_and_privacy_floors
                .iter()
                .find(|&&f| !up.new_floors.contains(&f))
            {
                return Err(SheRefusal::CoerciveFloorDowngrade {
                    dropped_floor: dropped,
                });
            }
            if up.authority_claim != UpgradeAuthorityClaim::LocalCustodianCeremony {
                return Err(SheRefusal::ExternalAuthorityRefused);
            }
            let revert_ok = up.new_floors.iter().all(|&f| match f {
                SheFloor::OperatorLocalRevert { max_revert_steps } => {
                    up.new_revert_window_steps <= max_revert_steps
                }
                _ => true,
            });
            if !check_slice_nodup(&up.new_floors)
                || !up.new_floors.iter().any(|f| f.is_bedrock())
                || !up.new_floors.iter().all(|f| f.well_formed())
                || !revert_ok
            {
                return Err(SheRefusal::MalformedFloorSet);
            }
            if up.new_custodian_epoch <= st.custodian_quorum_epoch {
                return Err(SheRefusal::NonMonotoneCustodianEpoch {
                    current_epoch: st.custodian_quorum_epoch,
                    proposed_epoch: up.new_custodian_epoch,
                });
            }
            let upgrade_msg = she_custodian_upgrade_msg(st, up);
            check_custodian_pq_quorum(st, &upgrade_msg, &up.custodian_signatures)?;
            if up.tof_round_trip_ticks > st.max_proximity_ticks {
                return Err(SheRefusal::TofProximityExceeded {
                    actual_ticks: up.tof_round_trip_ticks,
                    max_ticks: st.max_proximity_ticks,
                });
            }

            let mut next = st.clone();
            next.habitat_judge_digest = up.new_judge_digest;
            next.pinned_model_weights_root = up.new_model_weights_root;
            next.pinned_zkml_suite_digest = up.new_zkml_suite_digest;
            next.active_safety_and_privacy_floors = up.new_floors.clone();
            next.revert_window_steps = up.new_revert_window_steps;
            next.custodian_quorum_epoch = up.new_custodian_epoch;
            for (s, sig) in &up.custodian_signatures {
                next.consumed_custodian_leaves
                    .push((*s, sig.leaf_global_idx));
            }
            Ok(next)
        }
        SheTurn::RevokeOrAttenuateMandate(rev) => {
            if rev.new_budget_cap > st.remaining_mandate_budget {
                return Err(SheRefusal::MandateAmplificationRefused);
            }
            if rev.new_max_proximity_ticks == 0
                || rev.new_max_proximity_ticks > st.max_proximity_ticks
            {
                return Err(SheRefusal::ProximityWideningRefused {
                    proposed_ticks: rev.new_max_proximity_ticks,
                    current_max_ticks: st.max_proximity_ticks,
                });
            }
            if !rev
                .newly_revoked_custodians
                .iter()
                .all(|&c| c < st.custodian_total_n)
            {
                return Err(SheRefusal::DuplicateOrOutOfRangeSigner);
            }

            let mut next = st.clone();
            next.remaining_mandate_budget = rev.new_budget_cap;
            next.max_proximity_ticks = rev.new_max_proximity_ticks;
            for &c in &rev.newly_revoked_custodians {
                if !next.revoked_custodians.contains(&c) {
                    next.revoked_custodians.push(c);
                }
            }
            Ok(next)
        }
    }
}

pub fn run_she_trace(st: &SheState, turns: &[SheTurn]) -> Result<SheState, (usize, SheRefusal)> {
    if !st.well_formed() {
        return Err((0, SheRefusal::MalformedInitialState));
    }
    let mut cur = st.clone();
    for (idx, turn) in turns.iter().enumerate() {
        cur = apply_she_turn(&cur, turn).map_err(|e| (idx, e))?;
    }
    Ok(cur)
}

// ---------------------------------------------------------------------------
// 4. Sealed Integration with `obend-oracles-e2ee` TLSNotary & TEE Receipts
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedOracleIngress {
    mono_seq: u64,
    seal_digest: [u8; 32],
    attested_gpu_count: u64,
}

impl SealedOracleIngress {
    pub const fn mono_seq(&self) -> u64 {
        self.mono_seq
    }

    pub const fn seal_digest(&self) -> [u8; 32] {
        self.seal_digest
    }

    pub const fn attested_gpu_count(&self) -> u64 {
        self.attested_gpu_count
    }

    pub fn from_tlsn_and_tee(
        mono_seq: u64,
        transcript: &VerifiedHttpsTranscript,
        cpu_tee: &VerifiedTeeEvidence,
        gpu_tees: &[VerifiedTeeEvidence],
    ) -> Result<Self, SheRefusal> {
        if matches!(cpu_tee.vendor(), TeeVendor::NvidiaGpu(_))
            || matches!(
                (cpu_tee.vendor(), cpu_tee.tcb_posture()),
                (
                    TeeVendor::AmdSevSnp(_) | TeeVendor::IntelTdx,
                    TcbPosture::NoPolicyOnPlatform
                )
            )
        {
            return Err(SheRefusal::OracleEvidenceBindingMismatch);
        }
        let mut seen_gpu_keys = std::collections::BTreeSet::new();
        let mut gpu_digests: Vec<[u8; 32]> = Vec::with_capacity(gpu_tees.len());
        for gpu in gpu_tees {
            if !matches!(gpu.vendor(), TeeVendor::NvidiaGpu(_))
                || gpu.tcb_posture() != TcbPosture::VerifiedFloor
                || gpu.gpu_fwid().is_none()
                || !seen_gpu_keys.insert(gpu.leaf_spki_sha256())
            {
                return Err(SheRefusal::OracleEvidenceBindingMismatch);
            }
            let dig = gpu.evidence_digest();
            if gpu_digests.iter().any(|prev| ct_eq(prev, &dig)) {
                return Err(SheRefusal::OracleEvidenceBindingMismatch);
            }
            gpu_digests.push(dig);
        }
        let seal_digest = she_cshake256_32(
            b"OBEND.SHE.ORACLE_SEAL/v1",
            &encode_she_fields(&[
                she_leb128(mono_seq),
                transcript.transcript_digest().to_vec(),
                cpu_tee.evidence_digest().to_vec(),
                encode_bytes32_list(&gpu_digests),
            ]),
        );
        Ok(Self {
            mono_seq,
            seal_digest,
            attested_gpu_count: gpu_digests.len() as u64,
        })
    }

    pub fn from_verified_calltree(mono_seq: u64, tree: &VerifiedCallTree) -> Self {
        Self {
            mono_seq,
            seal_digest: tree.root_digest(),
            attested_gpu_count: 0,
        }
    }

    pub fn from_verified_e2ee_channel(
        mono_seq: u64,
        channel: &VerifiedE2eeChannel,
        cpu_tee: &VerifiedTeeEvidence,
    ) -> Result<Self, SheRefusal> {
        if !ct_eq(&channel.cpu_evidence_digest(), &cpu_tee.evidence_digest()) {
            return Err(SheRefusal::OracleEvidenceBindingMismatch);
        }
        Ok(Self {
            mono_seq,
            seal_digest: channel.channel_binding_id(),
            attested_gpu_count: channel.gpu_fwids().len() as u64,
        })
    }
}

pub fn apply_oracle_attested_actuation(
    state: &SheState,
    ingress: &SealedOracleIngress,
    proposal: &ActuationTurnProposal,
) -> Result<SheState, SheRefusal> {
    if proposal.sensor_seq != ingress.mono_seq()
        || !ct_eq(&proposal.sensor_seal_digest, &ingress.seal_digest())
        || proposal.attested_gpu_count > ingress.attested_gpu_count()
    {
        return Err(SheRefusal::OracleEvidenceBindingMismatch);
    }
    apply_she_turn(state, &SheTurn::ProposeAndSettleActuation(proposal.clone()))
}
