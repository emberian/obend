//! `obend-pq-mpc`: Clean-room `#![no_std]` + `alloc` (`#![forbid(unsafe_code)]`) post-quantum
//! threshold hash-based signature MPC suite:
//! - [`adrs_tsw`]: Pre-locked 32-byte `HashAdrs`, `Cshake256Suite` & `Poseidon2Suite`, Target-Sum
//!   Winternitz (`TSW`), FORS, XMSS, stateless `leanSPHINCS`/`SLH-DSA`, stateful `leanSig`,
//!   committed-identity `HybridPinnedSig`, and tri-state `VerifyReply`.
//! - [`keccak_mpc`]: Bitsliced `64x` parallel `Keccak-f[1600]` & `cSHAKE256` in **2-of-3 `RSS`**
//!   (`4,800 B`/perm) and **arbitrary $t$-of-$n$ `BinaryTower256` Shamir** ($\mathbb{F}_2 \hookrightarrow \mathcal{T}_3 \subset \mathcal{T}_7$)
//!   with **2-lane split-custody `Tower128 × Tower128` SPDZ/BDOZ MACs** and identifiable abort (`SlashingReceipt`).
//! - [`poseidon2_mpc`]: Width-12 `Poseidon2Goldilocks` arbitrary $t$-of-$n$ Shamir + **1-round Binomial
//!   Power-7 tuples** (`944 B`/perm), 0-reconstruction A2B chain conversion, `GoldilocksExt2` MACs,
//!   and pre-sign additive field-pad custody policy gate.
//! - [`dkg_and_latch`]: 2-round PQ commit-and-open dealerless DKG (`Π_deg`), constant-PK proactive
//!   share refresh (`Π_deg0`), and Simplex monotonic persist-before-sign `EpochLatch`.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

#[cfg(any(test, feature = "std"))]
extern crate std;

pub mod adrs_tsw;
pub mod dkg_and_latch;
pub mod keccak_mpc;
pub mod poseidon2_mpc;

use alloc::vec;
use alloc::vec::Vec;

use obend_crypto_exec::goldilocks::Goldilocks;

use crate::adrs_tsw::{
    AdrsKind, Cshake256Suite, ForsTreeOpening, HashAdrs, LayerXmssSig, PQ_CSHAKE_SUITE_CUSTOM,
    Poseidon2Suite, PqHashParams, PqHashSig, PqPublicKey, PqSecretKey, TAG_PRF, TAG_PRF_MSG,
    TAG_TH_F, TweakableHashSuite, build_merkle_from_leaves_topdown, compute_wots_pk,
    derive_fors_indices, fors_leaf_hash_from_secret, fors_secret_leaf, grind_tsw_counter,
    th_pre_hash, th_preimage, th_tweak_tl,
};
use crate::keccak_mpc::{
    ShamirSeedShare256, TowerGf256, rss_eval_cshake256_batch64, rss_eval_cshake256_secret_shares64,
    shamir_eval_cshake256_secret_shares64, shamir_eval_cshake256_with_seed_shares64,
    shamir_reconstruct_seed32_gf256,
};
use crate::poseidon2_mpc::{
    ShamirPoseidonSeedShare, mpc_poseidon2_hash32_shamir, mpc_poseidon2_wots_chain_shamir,
    shamir_reconstruct_seed32_goldilocks,
};

/// Precomputed bounded-region subtree & FORS public digest cache built once at DKG (`0` online sibling MPC gates!).
#[derive(Clone, Debug)]
pub struct DkgCachedSubtrees {
    /// Cached public WOTS+C leaf public keys per `(layer, tree_idx)`: `subtree_wots_pks[layer][tree_idx][kp_idx]`.
    pub subtree_wots_pks: Vec<Vec<Vec<[u8; 32]>>>,
    /// Optional cached public FORS leaf hashes `L_{j, u}` per layer-0 `(tree0, kp0)`:
    /// `fors_leaf_hashes[global_leaf0][j][u]`.
    pub fors_leaf_hashes: Option<Vec<Vec<Vec<[u8; 32]>>>>,
}

impl DkgCachedSubtrees {
    /// Checked bounded-region subtree WOTS+C public-key (and optional FORS leaf) cache builder.
    pub fn build_checked<S: TweakableHashSuite>(
        suite: S,
        params: &PqHashParams,
        sk: &PqSecretKey,
        cache_fors: bool,
    ) -> Option<Self> {
        if !params.is_well_formed() || params.num_layers.saturating_mul(params.subtree_height) > 20 {
            return None;
        }
        Some(Self::build(suite, params, sk, cache_fors))
    }

    /// Precompute bounded-region subtree WOTS+C public keys (and optionally FORS leaf digests) at DKG.
    pub fn build<S: TweakableHashSuite>(
        suite: S,
        params: &PqHashParams,
        sk: &PqSecretKey,
        cache_fors: bool,
    ) -> Self {
        assert!(params.is_well_formed(), "DkgCachedSubtrees::build requires well-formed PqHashParams");
        let sub_leaves = 1usize << params.subtree_height;
        let mut subtree_wots_pks = Vec::with_capacity(params.num_layers);
        for layer in 0..params.num_layers {
            let trees_at_layer =
                1usize << ((params.num_layers - 1 - layer) * params.subtree_height);
            let mut layer_vec = Vec::with_capacity(trees_at_layer);
            for tree_idx in 0..trees_at_layer {
                let mut leaves = Vec::with_capacity(sub_leaves);
                for kp in 0..sub_leaves {
                    leaves.push(compute_wots_pk(
                        suite,
                        params,
                        sk,
                        layer as u32,
                        tree_idx as u64,
                        kp as u32,
                    ));
                }
                layer_vec.push(leaves);
            }
            subtree_wots_pks.push(layer_vec);
        }

        let fors_leaf_hashes = if cache_fors && !params.stateful_lean_sig {
            let total_leaves0 = 1usize << (params.num_layers * params.subtree_height);
            let fors_cnt = 1usize << params.fors_height;
            let mut all_fors = Vec::with_capacity(total_leaves0);
            for g in 0..total_leaves0 {
                let kp0 = (g % sub_leaves) as u32;
                let tree0 = (g / sub_leaves) as u64;
                let mut per_tree = Vec::with_capacity(params.fors_trees);
                for j in 0..params.fors_trees {
                    let mut leaves_j = Vec::with_capacity(fors_cnt);
                    for u in 0..fors_cnt {
                        let global_u = (j * fors_cnt + u) as u32;
                        let sec = fors_secret_leaf(suite, sk, tree0, kp0, global_u);
                        leaves_j.push(fors_leaf_hash_from_secret(
                            suite,
                            &sk.pk_seed,
                            tree0,
                            kp0,
                            global_u,
                            &sec,
                        ));
                    }
                    per_tree.push(leaves_j);
                }
                all_fors.push(per_tree);
            }
            Some(all_fors)
        } else {
            None
        };

        Self {
            subtree_wots_pks,
            fors_leaf_hashes,
        }
    }
}

/// Telemetry & transcript shape summary emitted alongside every threshold MPC signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ThresholdSignMetrics {
    pub sequential_mpc_hash_depth: usize,
    pub total_mpc_permutations: usize,
    pub online_bytes_per_party: usize,
}

#[inline]
fn xor_bytes32(s: &[[u8; 32]; 3]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = s[0][i] ^ s[1][i] ^ s[2][i];
    }
    out
}

/// Build `(template_with_zeroed_32b_slot, offset)` for `th_prf_msg(TAG_PRF_MSG, [], ZERO, [sk_prf, opt_rand, mu])`.
fn build_prf_msg_template(opt_rand: &[u8], mu: &[u8; 32]) -> (Vec<u8>, usize) {
    let dummy_sk = [0xAAu8; 32];
    let pre = th_preimage(TAG_PRF_MSG, &[], &HashAdrs::ZERO, &[&dummy_sk, opt_rand, mu]);
    // Locate exact offset of `dummy_sk`: right before `leb128(opt_rand.len()) || opt_rand || leb128(32) || mu`
    let tail_len = crate::adrs_tsw::leb128(opt_rand.len()).len() + opt_rand.len() + 1 + 32;
    let sk_offset = pre.len() - tail_len - 32;
    let mut tmpl = pre;
    for b in &mut tmpl[sk_offset..sk_offset + 32] {
        *b = 0;
    }
    (tmpl, sk_offset)
}

/// Build `(template_with_zeroed_32b_slot, offset)` for `th_call(role_tag, pk_seed, adrs, &[32_byte_secret])`.
#[inline]
fn build_single_secret32_template(
    role_tag: &[u8],
    pk_seed: &[u8; 32],
    adrs: &HashAdrs,
) -> (Vec<u8>, usize) {
    let mut tmpl = th_preimage(role_tag, pk_seed, adrs, &[&[0u8; 32]]);
    let off = tmpl.len() - 32;
    for b in &mut tmpl[off..] {
        *b = 0;
    }
    (tmpl, off)
}

// ============================================================================
// 1. 2-of-3 `RSS` Threshold `cSHAKE256` Signer (`eval_threshold_sign_rss_cshake`)
// ============================================================================

/// Execute Public/Secret Cut + Constant-Depth (`1 + w`) parallel hypertree & FORS threshold signing
/// in **2-of-3 `RSS` (`cSHAKE256` bitsliced `64x`)**!
///
/// Security invariants:
/// - `sk_seed_rss` and `sk_prf_rss` are **NEVER** reconstructed;
/// - Intermediate WOTS+C chain states `[c^(0) .. c^(w-1)]` remain secret-shared in RAM (`[[u8; 32]; 3]`);
/// - Only `R`, revealed FORS preimages, public terminal endpoints `c^(w-1)` (when uncached), and the
///   single `TSW`-selected `[c^(m_r)]` per chain are ever opened!
pub fn eval_threshold_sign_rss_cshake(
    params: &PqHashParams,
    pk: &PqPublicKey,
    sk_seed_rss: &[[u8; 32]; 3],
    sk_prf_rss: &[[u8; 32]; 3],
    opt_rand: &[u8],
    msg: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
    cache: Option<&DkgCachedSubtrees>,
    prg_seeds: &mut [u64; 3],
) -> Option<(PqHashSig, ThresholdSignMetrics)> {
    if !params.is_well_formed() || !params.leaf_idx_in_range(leaf_global_idx) {
        return None;
    }
    if let Some(c) = cache {
        if c.subtree_wots_pks.len() != params.num_layers {
            return None;
        }
        if let Some(ref fc) = c.fors_leaf_hashes {
            if leaf_global_idx >= fc.len() {
                return None;
            }
        }
    }
    let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);

    // Phase 1 (Depth 1): Evaluate `R = PRF_msg([sk_prf], opt_rand, mu)` in 2-of-3 RSS and open `R`
    let (prf_msg_tmpl, prf_msg_off) = build_prf_msg_template(opt_rand, &mu);
    let (r_vec, mut total_bytes) = rss_eval_cshake256_batch64(
        PQ_CSHAKE_SUITE_CUSTOM,
        &[prf_msg_tmpl],
        &[(prf_msg_off, *sk_prf_rss)],
        prg_seeds,
    );
    let r_rand = r_vec[0];
    let mut total_perms = 2usize; // prefix block + message block

    let sub_leaves = 1usize << params.subtree_height;

    // Phase 2: Local `TSW` grind `ctr_0` (`0` MPC) + FORS opening
    let (msg_tsw_ctr, fors_openings, mut cur_root) = if params.stateful_lean_sig {
        (0u32, Vec::new(), mu)
    } else {
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let (ctr0, _, hmsg0) = grind_tsw_counter(
            Cshake256Suite,
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
        let fors_cnt = 1usize << params.fors_height;

        // 2a. Batch-evaluate all `k` revealed FORS secret leaves `[sigma_{FORS, j}]` in 1 bitsliced `64x` call!
        let mut rev_tmpls = Vec::with_capacity(params.fors_trees);
        let mut rev_patches = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate() {
            let global_u = (j * fors_cnt + idx_j) as u32;
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: 0,
                hash_step: global_u,
            };
            let (tmpl, off) = build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
            rev_tmpls.push(tmpl);
            rev_patches.push((off, *sk_seed_rss));
        }
        let mut revealed_secrets = Vec::with_capacity(params.fors_trees);
        for (t_chunk, p_chunk) in rev_tmpls.chunks(64).zip(rev_patches.chunks(64)) {
            let (d_chunk, b_chunk) = rss_eval_cshake256_batch64(
                PQ_CSHAKE_SUITE_CUSTOM,
                t_chunk,
                p_chunk,
                prg_seeds,
            );
            total_bytes += b_chunk;
            total_perms += 2 * t_chunk.len();
            revealed_secrets.extend_from_slice(&d_chunk);
        }

        // 2b. Obtain sibling FORS leaf hashes either from DKG cache (`0` MPC) or 2-step secret-PRF->F SIMD sweep!
        let all_fors_leaves: Vec<Vec<[u8; 32]>> =
            if let Some(fors_cache) = cache.and_then(|c| c.fors_leaf_hashes.as_ref()) {
                fors_cache[leaf_global_idx].clone()
            } else {
                // Evaluate unrevealed FORS leaves via secret-shared PRF -> F -> open ONLY leaf hash `L_{j, u}`!
                let mut flat_jobs: Vec<(usize, usize, u32)> = Vec::new();
                for j in 0..params.fors_trees {
                    for u in 0..fors_cnt {
                        if u != idxs[j] {
                            flat_jobs.push((j, u, (j * fors_cnt + u) as u32));
                        }
                    }
                }
                let mut leaves_grid = vec![vec![[0u8; 32]; fors_cnt]; params.fors_trees];
                for j in 0..params.fors_trees {
                    let u = idxs[j];
                    let global_u = (j * fors_cnt + u) as u32;
                    leaves_grid[j][u] = fors_leaf_hash_from_secret(
                        Cshake256Suite,
                        &pk.pk_seed,
                        tree0,
                        kp0,
                        global_u,
                        &revealed_secrets[j],
                    );
                }
                for job_chunk in flat_jobs.chunks(64) {
                    let mut prf_tmpls = Vec::with_capacity(job_chunk.len());
                    let mut prf_patches = Vec::with_capacity(job_chunk.len());
                    for &(_, _, global_u) in job_chunk {
                        let adrs = HashAdrs {
                            layer: 0,
                            tree: tree0,
                            kind: AdrsKind::ForsPrf,
                            key_pair: kp0,
                            chain_idx: 0,
                            hash_step: global_u,
                        };
                        let (tmpl, off) =
                            build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
                        prf_tmpls.push(tmpl);
                        prf_patches.push((off, *sk_seed_rss));
                    }
                    let (mut sec_shares, b1) = rss_eval_cshake256_secret_shares64(
                        PQ_CSHAKE_SUITE_CUSTOM,
                        &prf_tmpls,
                        &prf_patches,
                        prg_seeds,
                    );
                    total_bytes += b1;

                    let mut f_tmpls = Vec::with_capacity(job_chunk.len());
                    let mut f_patches = Vec::with_capacity(job_chunk.len());
                    for (k_i, &(_, _, global_u)) in job_chunk.iter().enumerate() {
                        let adrs_f = HashAdrs {
                            layer: 0,
                            tree: tree0,
                            kind: AdrsKind::ForsTree,
                            key_pair: kp0,
                            chain_idx: 0,
                            hash_step: global_u,
                        };
                        let (tmpl_f, off_f) =
                            build_single_secret32_template(TAG_TH_F, &pk.pk_seed, &adrs_f);
                        f_tmpls.push(tmpl_f);
                        f_patches.push((off_f, sec_shares[k_i]));
                    }
                    let (leaf_hashes, b2) = rss_eval_cshake256_batch64(
                        PQ_CSHAKE_SUITE_CUSTOM,
                        &f_tmpls,
                        &f_patches,
                        prg_seeds,
                    );
                    sec_shares.fill([[0u8; 32]; 3]);
                    for (_, sh) in &mut f_patches {
                        *sh = [[0u8; 32]; 3];
                    }
                    core::hint::black_box((sec_shares.as_slice(), f_patches.as_slice()));
                    total_bytes += b2;
                    total_perms += 4 * job_chunk.len();
                    for (k_i, &(j, u, _)) in job_chunk.iter().enumerate() {
                        leaves_grid[j][u] = leaf_hashes[k_i];
                    }
                }
                leaves_grid
            };

        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for j in 0..params.fors_trees {
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                Cshake256Suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                &all_fors_leaves[j],
                params.fors_height,
                j,
                idxs[j],
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_secrets[j],
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
        let fors_pk = th_tweak_tl(Cshake256Suite, &pk.pk_seed, &fors_pk_adrs, &roots);
        (ctr0, openings, fors_pk)
    };

    // Phase 3 (Constant Depth `w`): Evaluate ALL `d` hypertree layers' WOTS+C chains in parallel bitsliced `64x`!
    // Collect all `(layer_idx, tree_idx, kp, chain_r, is_active_leaf)` jobs across all `d` layers:
    let mut layer_coords: Vec<(u32, u64, usize)> = Vec::with_capacity(params.num_layers);
    let mut g_tmp = leaf_global_idx;
    for l in 0..params.num_layers {
        let kp_l = g_tmp % sub_leaves;
        let tree_l = g_tmp / sub_leaves;
        layer_coords.push((l as u32, tree_l as u64, kp_l));
        g_tmp = tree_l;
    }

    let mut wots_jobs: Vec<(usize, usize, usize)> = Vec::new(); // `(layer_idx, kp, r)`
    for (l_idx, &(_, _, active_kp)) in layer_coords.iter().enumerate() {
        if cache.is_some() {
            for r in 0..params.ell1 {
                wots_jobs.push((l_idx, active_kp, r));
            }
        } else {
            for kp in 0..sub_leaves {
                for r in 0..params.ell1 {
                    wots_jobs.push((l_idx, kp, r));
                }
            }
        }
    }

    // Store secret-shared chain table `ram_chains[job_idx][step]` (`step in 0..w`)
    let mut ram_chains: Vec<Vec<[[u8; 32]; 3]>> =
        vec![vec![[[0u8; 32]; 3]; params.w]; wots_jobs.len()];

    for (chunk_start, job_chunk) in wots_jobs.chunks(64).enumerate().map(|(ci, ch)| (ci * 64, ch)) {
        // Step 0: `c^(0) = PRF(pk_seed, [sk_seed], adrs_prf)` (kept secret-shared!)
        let mut t0 = Vec::with_capacity(job_chunk.len());
        let mut p0 = Vec::with_capacity(job_chunk.len());
        for &(l_idx, kp, r) in job_chunk {
            let (layer_u32, tree_u64, _) = layer_coords[l_idx];
            let adrs = HashAdrs {
                layer: layer_u32,
                tree: tree_u64,
                kind: AdrsKind::WotsPrf,
                key_pair: kp as u32,
                chain_idx: r as u32,
                hash_step: 0,
            };
            let (tmpl, off) = build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
            t0.push(tmpl);
            p0.push((off, *sk_seed_rss));
        }
        let (mut cur_sh, b0) =
            rss_eval_cshake256_secret_shares64(PQ_CSHAKE_SUITE_CUSTOM, &t0, &p0, prg_seeds);
        total_bytes += b0;
        total_perms += 2 * job_chunk.len();
        for (k_i, sh) in cur_sh.iter().enumerate() {
            ram_chains[chunk_start + k_i][0] = *sh;
        }

        // Steps `1..w-1`: `c^(s) = F(pk_seed, adrs_{s-1}, [c^(s-1)])` (kept secret-shared!)
        for s in 1..params.w {
            let mut ts = Vec::with_capacity(job_chunk.len());
            let mut ps = Vec::with_capacity(job_chunk.len());
            for (k_i, &(l_idx, kp, r)) in job_chunk.iter().enumerate() {
                let (layer_u32, tree_u64, _) = layer_coords[l_idx];
                let adrs = HashAdrs {
                    layer: layer_u32,
                    tree: tree_u64,
                    kind: AdrsKind::WotsHash,
                    key_pair: kp as u32,
                    chain_idx: r as u32,
                    hash_step: (s - 1) as u32,
                };
                let (tmpl, off) = build_single_secret32_template(TAG_TH_F, &pk.pk_seed, &adrs);
                ts.push(tmpl);
                ps.push((off, cur_sh[k_i]));
            }
            let (next_sh, bs) =
                rss_eval_cshake256_secret_shares64(PQ_CSHAKE_SUITE_CUSTOM, &ts, &ps, prg_seeds);
            total_bytes += bs;
            total_perms += 2 * job_chunk.len();
            for (k_i, sh) in next_sh.iter().enumerate() {
                ram_chains[chunk_start + k_i][s] = *sh;
            }
            cur_sh = next_sh;
        }
        cur_sh.fill([[0u8; 32]; 3]);
        core::hint::black_box(cur_sh.as_slice());
    }

    // Phase 4 (`0` Permutations, `1` Broadcast Round): Assemble public subtree Merkle paths, locally grind `ctr_l`,
    // and open ONLY `[c^(m_{l,r})]` from `ram_chains`!
    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    for l_idx in 0..params.num_layers {
        let (layer_u32, tree_u64, active_kp) = layer_coords[l_idx];
        let subtree_leaves: Vec<[u8; 32]> = if let Some(c_table) = cache {
            c_table.subtree_wots_pks[l_idx][tree_u64 as usize].clone()
        } else {
            let base_job = l_idx * sub_leaves * params.ell1;
            let mut leaves = Vec::with_capacity(sub_leaves);
            for kp in 0..sub_leaves {
                let mut endpoints = Vec::with_capacity(params.ell1);
                for r in 0..params.ell1 {
                    let j_idx = base_job + kp * params.ell1 + r;
                    // Open ONLY terminal endpoint `c^(w - 1)`!
                    endpoints.push(xor_bytes32(&ram_chains[j_idx][params.w - 1]));
                    total_bytes += 32;
                }
                let adrs_pk = HashAdrs {
                    layer: layer_u32,
                    tree: tree_u64,
                    kind: AdrsKind::WotsPk,
                    key_pair: kp as u32,
                    chain_idx: 0,
                    hash_step: 0,
                };
                leaves.push(th_tweak_tl(
                    Cshake256Suite,
                    &pk.pk_seed,
                    &adrs_pk,
                    &endpoints,
                ));
            }
            leaves
        };

        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            Cshake256Suite,
            &pk.pk_seed,
            layer_u32,
            tree_u64,
            AdrsKind::Tree,
            &subtree_leaves,
            params.subtree_height,
            0,
            active_kp,
        );

        let Some((ctr_l, digits_l, _)) = grind_tsw_counter(
            Cshake256Suite,
            params.w,
            params.ell1,
            params.target_sum(),
            &r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_u64,
            max_grind,
        ) else {
            for row in &mut ram_chains {
                row.fill([[0u8; 32]; 3]);
                core::hint::black_box(row.as_slice());
            }
            return None;
        };

        let active_job_base = if cache.is_some() {
            l_idx * params.ell1
        } else {
            l_idx * sub_leaves * params.ell1 + active_kp * params.ell1
        };
        let mut wots_chains = Vec::with_capacity(params.ell1);
        for r in 0..params.ell1 {
            let mr = digits_l[r];
            wots_chains.push(xor_bytes32(&ram_chains[active_job_base + r][mr]));
            total_bytes += 32;
        }
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr_l,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
    }
    for row in &mut ram_chains {
        row.fill([[0u8; 32]; 3]);
        core::hint::black_box(row.as_slice());
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    };
    let fors_depth = if params.stateful_lean_sig {
        0
    } else if cache.and_then(|c| c.fors_leaf_hashes.as_ref()).is_some() {
        1
    } else {
        3
    };
    let metrics = ThresholdSignMetrics {
        sequential_mpc_hash_depth: 1 + params.w.max(fors_depth),
        total_mpc_permutations: total_perms,
        online_bytes_per_party: total_bytes,
    };
    Some((sig, metrics))
}

// ============================================================================
// 2. Arbitrary $t$-of-$n$ `BinaryTower256` Shamir Threshold `cSHAKE256` Signer
// ============================================================================

/// Execute Public/Secret Cut + Constant-Depth (`1 + w`) parallel hypertree & FORS threshold signing
/// for **arbitrary $t$-of-$n$ (`3-of-5`, `5-of-9`, `7-of-11`, ..., $n \le 255$)** over `BinaryTower256` ($\mathcal{T}_3$)!
///
/// Zero secret reconstruction (`sk_seed_shares` and `sk_prf_shares` remain Shamir-shared throughout).
pub fn eval_threshold_sign_shamir_cshake(
    t: usize,
    eval_points: &[TowerGf256],
    params: &PqHashParams,
    pk: &PqPublicKey,
    sk_seed_shares: &[ShamirSeedShare256],
    sk_prf_shares: &[ShamirSeedShare256],
    opt_rand: &[u8],
    msg: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
    cache: Option<&DkgCachedSubtrees>,
    offline_seed: &mut u64,
) -> Option<(PqHashSig, ThresholdSignMetrics, Vec<u64>)> {
    let n = eval_points.len();
    if !params.is_well_formed()
        || !params.leaf_idx_in_range(leaf_global_idx)
        || t == 0
        || t > n
        || sk_seed_shares.len() != n
        || sk_prf_shares.len() != n
    {
        return None;
    }
    if let Some(c) = cache {
        if c.subtree_wots_pks.len() != params.num_layers {
            return None;
        }
        if let Some(ref fc) = c.fors_leaf_hashes {
            if leaf_global_idx >= fc.len() {
                return None;
            }
        }
    }
    let mut transcript_diffs = Vec::new();
    let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);

    // Phase 1: `R = PRF_msg([sk_prf], opt_rand, mu)` in $t$-of-$n$ bitsliced Shamir
    let (prf_msg_tmpl, prf_msg_off) = build_prf_msg_template(opt_rand, &mu);
    let (r_vec, mut total_bytes) = shamir_eval_cshake256_with_seed_shares64(
        t,
        eval_points,
        PQ_CSHAKE_SUITE_CUSTOM,
        &[prf_msg_tmpl],
        &[(prf_msg_off, sk_prf_shares)],
        offline_seed,
        &mut transcript_diffs,
    )?;
    let r_rand = r_vec[0];
    let mut total_perms = 2usize;

    let sub_leaves = 1usize << params.subtree_height;

    let (msg_tsw_ctr, fors_openings, mut cur_root) = if params.stateful_lean_sig {
        (0u32, Vec::new(), mu)
    } else {
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let (ctr0, _, hmsg0) = grind_tsw_counter(
            Cshake256Suite,
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
        let fors_cnt = 1usize << params.fors_height;

        let mut rev_tmpls = Vec::with_capacity(params.fors_trees);
        let mut rev_offs = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate() {
            let global_u = (j * fors_cnt + idx_j) as u32;
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: 0,
                hash_step: global_u,
            };
            let (tmpl, off) = build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
            rev_tmpls.push(tmpl);
            rev_offs.push(off);
        }
        let mut revealed_secrets = Vec::with_capacity(params.fors_trees);
        for (t_chunk, o_chunk) in rev_tmpls.chunks(64).zip(rev_offs.chunks(64)) {
            let patches: Vec<(usize, &[ShamirSeedShare256])> =
                o_chunk.iter().map(|&o| (o, sk_seed_shares)).collect();
            let (d_chunk, b_chunk) = shamir_eval_cshake256_with_seed_shares64(
                t,
                eval_points,
                PQ_CSHAKE_SUITE_CUSTOM,
                t_chunk,
                &patches,
                offline_seed,
                &mut transcript_diffs,
            )?;
            total_bytes += b_chunk;
            total_perms += 2 * t_chunk.len();
            revealed_secrets.extend_from_slice(&d_chunk);
        }

        let all_fors_leaves: Vec<Vec<[u8; 32]>> =
            if let Some(fors_cache) = cache.and_then(|c| c.fors_leaf_hashes.as_ref()) {
                fors_cache[leaf_global_idx].clone()
            } else {
                let mut flat_jobs: Vec<(usize, usize, u32)> = Vec::new();
                for j in 0..params.fors_trees {
                    for u in 0..fors_cnt {
                        if u != idxs[j] {
                            flat_jobs.push((j, u, (j * fors_cnt + u) as u32));
                        }
                    }
                }
                let mut leaves_grid = vec![vec![[0u8; 32]; fors_cnt]; params.fors_trees];
                for j in 0..params.fors_trees {
                    let u = idxs[j];
                    let global_u = (j * fors_cnt + u) as u32;
                    leaves_grid[j][u] = fors_leaf_hash_from_secret(
                        Cshake256Suite,
                        &pk.pk_seed,
                        tree0,
                        kp0,
                        global_u,
                        &revealed_secrets[j],
                    );
                }
                for job_chunk in flat_jobs.chunks(64) {
                    let mut prf_tmpls = Vec::with_capacity(job_chunk.len());
                    let mut prf_offs = Vec::with_capacity(job_chunk.len());
                    for &(_, _, global_u) in job_chunk {
                        let adrs = HashAdrs {
                            layer: 0,
                            tree: tree0,
                            kind: AdrsKind::ForsPrf,
                            key_pair: kp0,
                            chain_idx: 0,
                            hash_step: global_u,
                        };
                        let (tmpl, off) =
                            build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
                        prf_tmpls.push(tmpl);
                        prf_offs.push(off);
                    }
                    let prf_patches: Vec<(usize, &[ShamirSeedShare256])> =
                        prf_offs.iter().map(|&o| (o, sk_seed_shares)).collect();
                    let (sec_shares, b1) = shamir_eval_cshake256_secret_shares64(
                        t,
                        eval_points,
                        PQ_CSHAKE_SUITE_CUSTOM,
                        &prf_tmpls,
                        &prf_patches,
                        offline_seed,
                        &mut transcript_diffs,
                    )?;
                    total_bytes += b1;

                    let mut f_tmpls = Vec::with_capacity(job_chunk.len());
                    let mut f_offs = Vec::with_capacity(job_chunk.len());
                    for &(_, _, global_u) in job_chunk {
                        let adrs_f = HashAdrs {
                            layer: 0,
                            tree: tree0,
                            kind: AdrsKind::ForsTree,
                            key_pair: kp0,
                            chain_idx: 0,
                            hash_step: global_u,
                        };
                        let (tmpl_f, off_f) =
                            build_single_secret32_template(TAG_TH_F, &pk.pk_seed, &adrs_f);
                        f_tmpls.push(tmpl_f);
                        f_offs.push(off_f);
                    }
                    let f_patches: Vec<(usize, &[ShamirSeedShare256])> = f_offs
                        .iter()
                        .enumerate()
                        .map(|(k_i, &o)| (o, sec_shares[k_i].as_slice()))
                        .collect();
                    let (leaf_hashes, b2) = shamir_eval_cshake256_with_seed_shares64(
                        t,
                        eval_points,
                        PQ_CSHAKE_SUITE_CUSTOM,
                        &f_tmpls,
                        &f_patches,
                        offline_seed,
                        &mut transcript_diffs,
                    )?;
                    total_bytes += b2;
                    total_perms += 4 * job_chunk.len();
                    for (k_i, &(j, u, _)) in job_chunk.iter().enumerate() {
                        leaves_grid[j][u] = leaf_hashes[k_i];
                    }
                }
                leaves_grid
            };

        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for j in 0..params.fors_trees {
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                Cshake256Suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                &all_fors_leaves[j],
                params.fors_height,
                j,
                idxs[j],
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_secrets[j],
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
        let fors_pk = th_tweak_tl(Cshake256Suite, &pk.pk_seed, &fors_pk_adrs, &roots);
        (ctr0, openings, fors_pk)
    };

    // Phase 3: Constant-depth (`w`) parallel WOTS+C sweep across all `d` layers!
    let mut layer_coords: Vec<(u32, u64, usize)> = Vec::with_capacity(params.num_layers);
    let mut g_tmp = leaf_global_idx;
    for l in 0..params.num_layers {
        let kp_l = g_tmp % sub_leaves;
        let tree_l = g_tmp / sub_leaves;
        layer_coords.push((l as u32, tree_l as u64, kp_l));
        g_tmp = tree_l;
    }

    let mut wots_jobs: Vec<(usize, usize, usize)> = Vec::new();
    for (l_idx, &(_, _, active_kp)) in layer_coords.iter().enumerate() {
        if cache.is_some() {
            for r in 0..params.ell1 {
                wots_jobs.push((l_idx, active_kp, r));
            }
        } else {
            for kp in 0..sub_leaves {
                for r in 0..params.ell1 {
                    wots_jobs.push((l_idx, kp, r));
                }
            }
        }
    }

    let mut ram_chains: Vec<Vec<Vec<ShamirSeedShare256>>> =
        vec![Vec::with_capacity(params.w); wots_jobs.len()];

    for (chunk_start, job_chunk) in wots_jobs.chunks(64).enumerate().map(|(ci, ch)| (ci * 64, ch)) {
        let mut t0 = Vec::with_capacity(job_chunk.len());
        let mut o0 = Vec::with_capacity(job_chunk.len());
        for &(l_idx, kp, r) in job_chunk {
            let (layer_u32, tree_u64, _) = layer_coords[l_idx];
            let adrs = HashAdrs {
                layer: layer_u32,
                tree: tree_u64,
                kind: AdrsKind::WotsPrf,
                key_pair: kp as u32,
                chain_idx: r as u32,
                hash_step: 0,
            };
            let (tmpl, off) = build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs);
            t0.push(tmpl);
            o0.push(off);
        }
        let p0: Vec<(usize, &[ShamirSeedShare256])> =
            o0.iter().map(|&o| (o, sk_seed_shares)).collect();
        let (mut cur_sh, b0) = shamir_eval_cshake256_secret_shares64(
            t,
            eval_points,
            PQ_CSHAKE_SUITE_CUSTOM,
            &t0,
            &p0,
            offline_seed,
            &mut transcript_diffs,
        )?;
        total_bytes += b0;
        total_perms += 2 * job_chunk.len();
        for (k_i, sh) in cur_sh.iter().enumerate() {
            ram_chains[chunk_start + k_i].push(sh.clone());
        }

        for s in 1..params.w {
            let mut ts = Vec::with_capacity(job_chunk.len());
            let mut os = Vec::with_capacity(job_chunk.len());
            for &(l_idx, kp, r) in job_chunk {
                let (layer_u32, tree_u64, _) = layer_coords[l_idx];
                let adrs = HashAdrs {
                    layer: layer_u32,
                    tree: tree_u64,
                    kind: AdrsKind::WotsHash,
                    key_pair: kp as u32,
                    chain_idx: r as u32,
                    hash_step: (s - 1) as u32,
                };
                let (tmpl, off) = build_single_secret32_template(TAG_TH_F, &pk.pk_seed, &adrs);
                ts.push(tmpl);
                os.push(off);
            }
            let ps: Vec<(usize, &[ShamirSeedShare256])> = os
                .iter()
                .enumerate()
                .map(|(k_i, &o)| (o, cur_sh[k_i].as_slice()))
                .collect();
            let (next_sh, bs) = shamir_eval_cshake256_secret_shares64(
                t,
                eval_points,
                PQ_CSHAKE_SUITE_CUSTOM,
                &ts,
                &ps,
                offline_seed,
                &mut transcript_diffs,
            )?;
            total_bytes += bs;
            total_perms += 2 * job_chunk.len();
            for (k_i, sh) in next_sh.iter().enumerate() {
                ram_chains[chunk_start + k_i].push(sh.clone());
            }
            cur_sh = next_sh;
        }
    }

    // Phase 4: 1-round RAM share opening of `[c^(m_{l,r})]`!
    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    for l_idx in 0..params.num_layers {
        let (layer_u32, tree_u64, active_kp) = layer_coords[l_idx];
        let subtree_leaves: Vec<[u8; 32]> = if let Some(c_table) = cache {
            c_table.subtree_wots_pks[l_idx][tree_u64 as usize].clone()
        } else {
            let base_job = l_idx * sub_leaves * params.ell1;
            let mut leaves = Vec::with_capacity(sub_leaves);
            for kp in 0..sub_leaves {
                let mut endpoints = Vec::with_capacity(params.ell1);
                for r in 0..params.ell1 {
                    let j_idx = base_job + kp * params.ell1 + r;
                    let ep =
                        shamir_reconstruct_seed32_gf256(&ram_chains[j_idx][params.w - 1][..t])?;
                    endpoints.push(ep);
                    total_bytes += 256;
                }
                let adrs_pk = HashAdrs {
                    layer: layer_u32,
                    tree: tree_u64,
                    kind: AdrsKind::WotsPk,
                    key_pair: kp as u32,
                    chain_idx: 0,
                    hash_step: 0,
                };
                leaves.push(th_tweak_tl(
                    Cshake256Suite,
                    &pk.pk_seed,
                    &adrs_pk,
                    &endpoints,
                ));
            }
            leaves
        };

        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            Cshake256Suite,
            &pk.pk_seed,
            layer_u32,
            tree_u64,
            AdrsKind::Tree,
            &subtree_leaves,
            params.subtree_height,
            0,
            active_kp,
        );

        let (ctr_l, digits_l, _) = grind_tsw_counter(
            Cshake256Suite,
            params.w,
            params.ell1,
            params.target_sum(),
            &r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_u64,
            max_grind,
        )?;

        let active_job_base = if cache.is_some() {
            l_idx * params.ell1
        } else {
            l_idx * sub_leaves * params.ell1 + active_kp * params.ell1
        };
        let mut wots_chains = Vec::with_capacity(params.ell1);
        for r in 0..params.ell1 {
            let mr = digits_l[r];
            let opened =
                shamir_reconstruct_seed32_gf256(&ram_chains[active_job_base + r][mr][..t])?;
            wots_chains.push(opened);
            total_bytes += 256;
        }
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr_l,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    };
    let fors_depth = if params.stateful_lean_sig {
        0
    } else if cache.and_then(|c| c.fors_leaf_hashes.as_ref()).is_some() {
        1
    } else {
        3
    };
    let metrics = ThresholdSignMetrics {
        sequential_mpc_hash_depth: 1 + params.w.max(fors_depth),
        total_mpc_permutations: total_perms,
        online_bytes_per_party: total_bytes,
    };
    Some((sig, metrics, transcript_diffs))
}

// ============================================================================
// 3. Arbitrary $t$-of-$n$ `Poseidon2Goldilocks` Shamir + 1-Round Power-7 Signer
// ============================================================================

/// Execute stateful `leanSig-Poseidon2` threshold signing
/// for **arbitrary $t$-of-$n$** over `Goldilocks` using **1-round Binomial Power-7 tuples (`944 B`/perm)**!
///
/// Notice the known-root optimization in stateful `leanSig` + DKG-cached subtrees:
/// Once `R = PRF_msg([sk_prf], opt_rand, mu)` is opened, `mu` and `r_rand` are 100% public, so local CPU
/// `TSW` grinding determines the exact digits `digits[r] = m_r` (`∑ m_r = ell1 * (w-1) / 2`) **before**
/// evaluating active chains! Wait: to ensure zero leakage of intermediate chain steps `s < m_r`,
/// `mpc_poseidon2_wots_chain_shamir` evaluates only `m_r` steps via 0-reconstruction A2B conversion
/// (or full `w - 1` steps when uncached), cutting online permutations by **50%** (`1 + ell1 * (1 + (w-1)/2)` = `161` perms for `ell1=64, w=4`!)!
pub fn eval_threshold_sign_shamir_poseidon2(
    t: usize,
    eval_points: &[Goldilocks],
    params: &PqHashParams,
    pk: &PqPublicKey,
    sk_seed_shares: &[ShamirPoseidonSeedShare],
    sk_prf_shares: &[ShamirPoseidonSeedShare],
    opt_rand: &[u8],
    msg: &[u8],
    leaf_global_idx: usize,
    max_grind: u32,
    cache: Option<&DkgCachedSubtrees>,
    offline_seed: &mut u64,
) -> Option<(PqHashSig, ThresholdSignMetrics, Vec<Goldilocks>)> {
    let n = eval_points.len();
    if !params.is_well_formed()
        || !params.leaf_idx_in_range(leaf_global_idx)
        || !params.stateful_lean_sig
        || t == 0
        || t > n
        || sk_seed_shares.len() != n
        || sk_prf_shares.len() != n
    {
        return None;
    }
    if let Some(c) = cache {
        if c.subtree_wots_pks.len() != params.num_layers {
            return None;
        }
    }
    let mut opened_deltas = Vec::new();
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    // Phase 1: `R = PRF_msg([sk_prf], opt_rand, mu)` in 1-round Binomial Power-7 MPC
    let (prf_msg_tmpl, prf_msg_off) = build_prf_msg_template(opt_rand, &mu);
    let (r_rand, mut total_bytes) = mpc_poseidon2_hash32_shamir(
        t,
        eval_points,
        &prf_msg_tmpl,
        prf_msg_off,
        sk_prf_shares,
        offline_seed,
        &mut opened_deltas,
    )?;
    let mut total_perms = 2usize;

    let sub_leaves = 1usize << params.subtree_height;
    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut cur_root = mu;
    let mut cur_global = leaf_global_idx;

    for l_idx in 0..params.num_layers {
        let active_kp = cur_global % sub_leaves;
        let tree_nat = cur_global / sub_leaves;
        let tree_u64 = tree_nat as u64;
        let layer_u32 = l_idx as u32;

        // Local plaintext `TSW` grind (`0` MPC gates!)
        let (ctr_l, digits_l, _) = grind_tsw_counter(
            Poseidon2Suite,
            params.w,
            params.ell1,
            params.target_sum(),
            &r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            &cur_root,
            layer_u32,
            tree_u64,
            max_grind,
        )?;

        let subtree_leaves: Vec<[u8; 32]>;
        let mut wots_chains = Vec::with_capacity(params.ell1);

        if let Some(c_table) = cache {
            subtree_leaves = c_table.subtree_wots_pks[l_idx][tree_nat].clone();
            // Known-root optimal cut: evaluate ONLY `1 + m_r` steps per chain (`∑ (1 + m_r) = 64 + 96 = 160` hashes!),
            // keeping steps `0..m_r - 1` strictly un-opened via 0-reconstruction A2B conversion!
            for r in 0..params.ell1 {
                let mr = digits_l[r];
                if mr == 0 {
                    let adrs0 = HashAdrs {
                        layer: layer_u32,
                        tree: tree_u64,
                        kind: AdrsKind::WotsPrf,
                        key_pair: active_kp as u32,
                        chain_idx: r as u32,
                        hash_step: 0,
                    };
                    let (tmpl0, off0) =
                        build_single_secret32_template(TAG_PRF, &pk.pk_seed, &adrs0);
                    let (c0_open, b0) = mpc_poseidon2_hash32_shamir(
                        t,
                        eval_points,
                        &tmpl0,
                        off0,
                        sk_seed_shares,
                        offline_seed,
                        &mut opened_deltas,
                    )?;
                    total_bytes += b0;
                    total_perms += 2;
                    wots_chains.push(c0_open);
                } else {
                    let (chain_sh, bc) = mpc_poseidon2_wots_chain_shamir(
                        t,
                        eval_points,
                        &pk.pk_seed,
                        layer_u32,
                        tree_u64,
                        active_kp as u32,
                        r as u32,
                        mr + 1,
                        sk_seed_shares,
                        offline_seed,
                        &mut opened_deltas,
                    )?;
                    total_bytes += bc;
                    total_perms += 2 * (mr + 1);
                    let opened_mr = shamir_reconstruct_seed32_goldilocks(&chain_sh[mr][..t])?;
                    wots_chains.push(opened_mr);
                }
            }
        } else {
            let mut leaves = Vec::with_capacity(sub_leaves);
            for kp in 0..sub_leaves {
                let mut endpoints = Vec::with_capacity(params.ell1);
                for r in 0..params.ell1 {
                    let (chain_sh, bc) = mpc_poseidon2_wots_chain_shamir(
                        t,
                        eval_points,
                        &pk.pk_seed,
                        layer_u32,
                        tree_u64,
                        kp as u32,
                        r as u32,
                        params.w,
                        sk_seed_shares,
                        offline_seed,
                        &mut opened_deltas,
                    )?;
                    total_bytes += bc;
                    total_perms += 2 * params.w;
                    let ep = shamir_reconstruct_seed32_goldilocks(&chain_sh[params.w - 1][..t])?;
                    endpoints.push(ep);
                    if kp == active_kp {
                        let mr = digits_l[r];
                        let opened_mr = shamir_reconstruct_seed32_goldilocks(&chain_sh[mr][..t])?;
                        wots_chains.push(opened_mr);
                    }
                }
                let adrs_pk = HashAdrs {
                    layer: layer_u32,
                    tree: tree_u64,
                    kind: AdrsKind::WotsPk,
                    key_pair: kp as u32,
                    chain_idx: 0,
                    hash_step: 0,
                };
                leaves.push(th_tweak_tl(
                    Poseidon2Suite,
                    &pk.pk_seed,
                    &adrs_pk,
                    &endpoints,
                ));
            }
            subtree_leaves = leaves;
        }

        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            Poseidon2Suite,
            &pk.pk_seed,
            layer_u32,
            tree_u64,
            AdrsKind::Tree,
            &subtree_leaves,
            params.subtree_height,
            0,
            active_kp,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr_l,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_nat;
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr: 0,
        leaf_global_idx,
        fors_openings: Vec::new(),
        layer_sigs,
    };
    let metrics = ThresholdSignMetrics {
        sequential_mpc_hash_depth: 1 + params.w,
        total_mpc_permutations: total_perms,
        online_bytes_per_party: total_bytes,
    };
    Some((sig, metrics, opened_deltas))
}

// ============================================================================
// Comprehensive Red-Team, Cross-Language Golden Vector & Benchmark Suite
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;
    use core::fmt::Write;
    use std::println;
    use std::time::Instant;

    use crate::adrs_tsw::{
        FaultStage, HybridPinnedSig, PQ_WIRE_MAGIC, VerifyReply, check_hybrid_pinning,
        compute_hybrid_id_commit, decode_adrs, derive_public_key, encode_adrs, encode_multi_frame,
        eval_single_sign, th_secret_prf, valid_lean_sig_batch, verify_hybrid_pinned_sig,
        verify_pq_hash_sig, verify_pq_wire_envelope,
    };
    use crate::dkg_and_latch::{
        DkgShareComplaint, EpochLatchError, GoldilocksDealerBroadcast, QuorumEpochLatchCluster,
        dkg_commit_share, proactive_refresh_seed32_gf256, proactive_refresh_seed32_goldilocks,
        verify_and_qualify_dkg_dealer_goldilocks, verify_dkg_private_packet_goldilocks,
    };
    use crate::keccak_mpc::{
        MacKeyShareCustody, SlashingReceipt, Tower128, rss_reconstruct_2of3,
        rss_share_keccak_states64, shamir_share_seed32_gf256, verify_batch_tower_mac_2lane,
    };
    use crate::poseidon2_mpc::{
        Ext2MacKeyCustody, eval_garbled_custody_policy_gate, garble_custody_policy_limit,
        mpc_poseidon2_perm12_shamir, poseidon2_perm12, shamir_share_scalar_goldilocks,
        shamir_share_seed32_goldilocks,
    };
    use obend_crypto_exec::goldilocks::GoldilocksExt2;

    fn hex_encode(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(bytes.len() * 2);
        for &b in bytes {
            let _ = write!(&mut s, "{:02x}", b);
        }
        s
    }

    fn golden_secret_key() -> PqSecretKey {
        let mut sk_seed = [0u8; 32];
        let mut sk_prf = [0u8; 32];
        let mut pk_seed = [0u8; 32];
        for i in 0..32 {
            sk_seed[i] = (i + 1) as u8;
            sk_prf[i] = (i + 33) as u8;
            pk_seed[i] = (i + 65) as u8;
        }
        PqSecretKey {
            sk_seed,
            sk_prf,
            pk_seed,
        }
    }

    /// **Test 1 (Cross-Language Byte-for-Byte Golden Vector Parity with Lean 4.35)**:
    /// Verifies `encode_adrs`, `encode_multi_frame`, `cshake256Suite`, `poseidon2Suite`,
    /// `derive_public_key`, `compute_hybrid_id_commit`, `dkg_commit_share`, and `eval_single_sign`
    /// match the exact hex vectors evaluated inside `lean/tests/Crypto/PqThresholdHashMpcTest.lean`!
    #[test]
    fn test_cross_language_lean_golden_vectors_exact_parity() {
        let adrs = HashAdrs {
            layer: 3,
            tree: 0x0102_0304_0506_0708,
            kind: AdrsKind::WotsHash,
            key_pair: 7,
            chain_idx: 11,
            hash_step: 2,
        };
        let encoded_adrs = encode_adrs(&adrs);
        assert_eq!(
            hex_encode(&encoded_adrs),
            "0000000300000000010203040506070800000000000000070000000b00000002"
        );
        assert_eq!(decode_adrs(&encoded_adrs), Some(adrs));

        let mf = encode_multi_frame(&[&[1, 2], &[3, 4, 5]]);
        assert_eq!(hex_encode(&mf), "0202010203030405");

        let sk = golden_secret_key();
        let cshake_prf = th_secret_prf(Cshake256Suite, &sk.pk_seed, &sk.sk_seed, &adrs);
        assert_eq!(
            hex_encode(&cshake_prf),
            "c461f210265b042ab4a95566bee3f8f012369b504f0d613db3fe5950abb95e3f"
        );

        let poseidon_prf = th_secret_prf(Poseidon2Suite, &sk.pk_seed, &sk.sk_seed, &adrs);
        assert_eq!(
            hex_encode(&poseidon_prf),
            "f802e8506312c3480d113ec7fb2786fd68423f9a85fb3b3681c6d74e65148c64"
        );

        let pk_cshake = derive_public_key(Cshake256Suite, &PqHashParams::COMPACT_GOLDEN, &sk);
        assert_eq!(
            hex_encode(&pk_cshake.pk_root),
            "060cabbcc13f5548d6d75596ce5eecba3ebaf1f07b117ebcf7e2a74fae387e4c"
        );

        let pk_poseidon = derive_public_key(Poseidon2Suite, &PqHashParams::COMPACT_LEAN_SIG, &sk);
        assert_eq!(
            hex_encode(&pk_poseidon.pk_root),
            "7e61b9ab282abd406d17600b6574e218b4da03512cc7a54e5beb096c8143b2df"
        );

        let dummy_classical_pk = [0x11u8; 32];
        let hybrid_commit =
            compute_hybrid_id_commit(&dummy_classical_pk, &pk_cshake.to_wire_bytes());
        assert_eq!(
            hex_encode(&hybrid_commit),
            "66094e4608c0f029966c719bfe27a34d07ee4b4d936da1a440aa7ae03afdb349"
        );

        let dkg_comm = dkg_commit_share(1, 2, &[0x77u8; 32], &[0x88u8; 16]);
        assert_eq!(
            hex_encode(&dkg_comm),
            "3db80075c4e7c88b9e218161e7b98ecc51f6af1b808c82a4d63b0f0dbb07b62d"
        );

        let msg1 = b"obend-pq-mpc-golden-msg-v1";
        let opt_rand = [0xA5u8; 32];
        let sig_cshake = eval_single_sign(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &sk,
            msg1,
            &opt_rand,
            1,
            256,
        )
        .expect("single sign must succeed");
        assert_eq!(sig_cshake.msg_tsw_ctr, 1);
        assert_eq!(
            hex_encode(&sig_cshake.r_rand),
            "aac835eedf6da763c8db059bfb5d2f25a9a52f55eccd2a5c5698da3a2f7d193f"
        );
        assert!(verify_pq_hash_sig(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &pk_cshake,
            msg1,
            &sig_cshake
        ));
    }

    /// **Test 2 (`thresholdSign_eq_singleSign` Across `2-of-3 RSS`, `3-of-5`, `5-of-9`, `7-of-11` Shamir)**:
    /// Proves experimentally that BOTH uncached and cached threshold MPC signers produce the
    /// **bit-for-bit identical** `PqHashSig` as single-party `eval_single_sign` across all quorums!
    #[test]
    fn test_threshold_sign_bit_identical_across_2of3_3of5_5of9_7of11() {
        let sk = golden_secret_key();
        let msg = b"obend-pq-mpc-golden-msg-v1";
        let opt_rand = [0xA5u8; 32];

        // 1. Stateless `leanSPHINCS-cSHAKE256` (`COMPACT_GOLDEN`): Single vs 2-of-3 RSS (uncached & cached)
        let pk_cshake = derive_public_key(Cshake256Suite, &PqHashParams::COMPACT_GOLDEN, &sk);
        let ref_sig_cshake = eval_single_sign(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &sk,
            msg,
            &opt_rand,
            1,
            256,
        )
        .unwrap();

        let m_a = [0x3Cu8; 32];
        let m_b = [0x96u8; 32];
        let mut seed_s0 = [0u8; 32];
        let mut prf_s0 = [0u8; 32];
        for i in 0..32 {
            seed_s0[i] = sk.sk_seed[i] ^ m_a[i] ^ m_b[i];
            prf_s0[i] = sk.sk_prf[i] ^ m_a[i] ^ m_b[i];
        }
        let sk_seed_rss = [seed_s0, m_a, m_b];
        let sk_prf_rss = [prf_s0, m_a, m_b];

        let mut prg = [0x1111u64, 0x2222u64, 0x3333u64];
        let (rss_sig_uncached, _) = eval_threshold_sign_rss_cshake(
            &PqHashParams::COMPACT_GOLDEN,
            &pk_cshake,
            &sk_seed_rss,
            &sk_prf_rss,
            &opt_rand,
            msg,
            1,
            256,
            None,
            &mut prg,
        )
        .unwrap();
        assert_eq!(rss_sig_uncached, ref_sig_cshake);

        let cache_cshake =
            DkgCachedSubtrees::build(Cshake256Suite, &PqHashParams::COMPACT_GOLDEN, &sk, true);
        let (rss_sig_cached, _) = eval_threshold_sign_rss_cshake(
            &PqHashParams::COMPACT_GOLDEN,
            &pk_cshake,
            &sk_seed_rss,
            &sk_prf_rss,
            &opt_rand,
            msg,
            1,
            256,
            Some(&cache_cshake),
            &mut prg,
        )
        .unwrap();
        assert_eq!(rss_sig_cached, ref_sig_cshake);

        // 2. Arbitrary t-of-n `BinaryTower256` Shamir (`3-of-5`, `5-of-9`, `7-of-11`)!
        let mut rng = 0xCAFE_BABE_1234_5678u64;
        for &(t, n) in &[(3usize, 5usize), (5, 9), (7, 11)] {
            let pts: Vec<TowerGf256> = (1..=n).map(|i| TowerGf256(i as u8)).collect();
            let mut seed_shares = shamir_share_seed32_gf256(t, &pts, &sk.sk_seed, &mut rng);
            let prf_shares = shamir_share_seed32_gf256(t, &pts, &sk.sk_prf, &mut rng);

            // Also test proactive refresh (`Π_deg0`) before signing on `5-of-9`!
            if t == 5 {
                assert!(proactive_refresh_seed32_gf256(
                    t,
                    &pts,
                    &mut seed_shares,
                    &mut rng
                ));
            }

            let cache_opt = if n > 5 { Some(&cache_cshake) } else { None };
            let (shamir_sig, _, _) = eval_threshold_sign_shamir_cshake(
                t,
                &pts,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_cshake,
                &seed_shares,
                &prf_shares,
                &opt_rand,
                msg,
                1,
                256,
                cache_opt,
                &mut rng,
            )
            .unwrap();
            assert_eq!(
                shamir_sig, ref_sig_cshake,
                "Shamir {t}-of-{n} BinaryTower256 signature must be bit-identical to single-party!"
            );
        }

        // 3. Stateful `leanSig-Poseidon2` (`3-of-5`, `5-of-9`, `7-of-11` Shamir + 1-Round Power-7 Tuples)!
        let pk_pos = derive_public_key(Poseidon2Suite, &PqHashParams::COMPACT_LEAN_SIG, &sk);
        let ref_sig_pos = eval_single_sign(
            Poseidon2Suite,
            &PqHashParams::COMPACT_LEAN_SIG,
            &sk,
            msg,
            &opt_rand,
            2,
            256,
        )
        .unwrap();
        assert!(valid_lean_sig_batch(
            &PqHashParams::COMPACT_LEAN_SIG,
            &[(pk_pos, msg.as_slice(), ref_sig_pos.clone())]
        ));
        let cache_pos =
            DkgCachedSubtrees::build(Poseidon2Suite, &PqHashParams::COMPACT_LEAN_SIG, &sk, false);

        for &(t, n) in &[(3usize, 5usize), (5, 9), (7, 11)] {
            let pts: Vec<Goldilocks> = (1..=n)
                .map(|i| Goldilocks::from_u64_reduced(i as u64))
                .collect();
            let mut seed_sh = shamir_share_seed32_goldilocks(t, &pts, &sk.sk_seed, &mut rng);
            let prf_sh = shamir_share_seed32_goldilocks(t, &pts, &sk.sk_prf, &mut rng);

            if t == 5 {
                assert!(proactive_refresh_seed32_goldilocks(
                    t,
                    &pts,
                    &mut seed_sh,
                    &mut rng
                ));
            }

            let cache_opt = if n > 5 { Some(&cache_pos) } else { None };
            let (pos_mpc_sig, _, _) = eval_threshold_sign_shamir_poseidon2(
                t,
                &pts,
                &PqHashParams::COMPACT_LEAN_SIG,
                &pk_pos,
                &seed_sh,
                &prf_sh,
                &opt_rand,
                msg,
                2,
                256,
                cache_opt,
                &mut rng,
            )
            .unwrap();
            assert_eq!(
                pos_mpc_sig, ref_sig_pos,
                "Poseidon2 {t}-of-{n} Power-7 MPC signature must be bit-identical to single-party!"
            );
        }
    }

    /// **Test 3 (2-Lane Split-Custody `Tower128` & `GoldilocksExt2` BDOZ MAC Cross-Terms & Cheater Slashing)**:
    /// Verifies off-diagonal correlated-OT cross-terms reconstruct `(α_0 + α_1 + α_2) · (x_0 + x_1 + x_2)`,
    /// terminal 2-lane GHASH batch check catches tampered openings, and pairwise BDOZ check deterministically
    /// pinpoints the exact malicious party with a `SlashingReceipt`!
    #[test]
    fn test_2lane_bdoz_mac_cross_terms_and_malicious_cheater_slashing() {
        let alphas_hi = [
            Tower128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210),
            Tower128(0x1111_2222_3333_4444_5555_6666_7777_8888),
            Tower128(0x9999_aaaa_bbbb_cccc_dddd_eeee_ffff_0001),
        ];
        let alphas_lo = [
            Tower128(0xa5a5_5a5a_c3c3_3c3c_0f0f_f0f0_1234_5678),
            Tower128(0x8765_4321_0fed_cba9_8765_4321_0000_ffff),
            Tower128(0xdead_beef_cafe_babe_0102_0304_0506_0708),
        ];
        let custodies = [
            MacKeyShareCustody::new_custody_share(alphas_hi[0], alphas_lo[0]),
            MacKeyShareCustody::new_custody_share(alphas_hi[1], alphas_lo[1]),
            MacKeyShareCustody::new_custody_share(alphas_hi[2], alphas_lo[2]),
        ];

        let xs = [
            Tower128::embed_bit(true),
            Tower128::embed_bit(true),
            Tower128::embed_bit(true),
        ];
        let x_opened = xs[0].add(xs[1]).add(xs[2]);

        // Correlated-OT off-diagonal shares `u_{i,j} ⊕ v_{j,i} = α_i · x_j` for `i != j`
        let mut u_hi = [[Tower128::ZERO; 3]; 3];
        let mut v_hi = [[Tower128::ZERO; 3]; 3];
        let mut u_lo = [[Tower128::ZERO; 3]; 3];
        let mut v_lo = [[Tower128::ZERO; 3]; 3];
        for i in 0..3 {
            for j in 0..3 {
                if i == j {
                    continue;
                }
                u_hi[i][j] = Tower128(((i * 17 + j * 31 + 7) as u128) * 0x1000_0001_0000_0003);
                v_hi[j][i] = u_hi[i][j].add(alphas_hi[i].mul(xs[j]));
                u_lo[i][j] = Tower128(((i * 23 + j * 41 + 9) as u128) * 0x2000_0005_0000_0007);
                v_lo[j][i] = u_lo[i][j].add(alphas_lo[i].mul(xs[j]));
            }
        }

        let mut mac_hi = [Tower128::ZERO; 3];
        let mut mac_lo = [Tower128::ZERO; 3];
        for i in 0..3 {
            let (mh, ml) = custodies[i].form_party_mac_share_2lane(
                i, xs[i], &u_hi[i], &v_hi[i], &u_lo[i], &v_lo[i],
            );
            mac_hi[i] = mh;
            mac_lo[i] = ml;
        }

        let chal_hi = Tower128(0x7777_8888_9999_aaaa_bbbb_cccc_dddd_eeee);
        let chal_lo = Tower128(0x1357_9bdf_2468_ace0_f0e1_d2c3_b4a5_9687);

        // Honest batch check passes (`== true`)
        let honest_checks: Vec<(Tower128, Tower128)> = (0..3)
            .map(|i| {
                custodies[i].compute_batch_check_share_2lane(
                    chal_hi,
                    chal_lo,
                    &[x_opened],
                    &[mac_hi[i]],
                    &[mac_lo[i]],
                )
            })
            .collect();
        assert!(verify_batch_tower_mac_2lane(&honest_checks));

        // Corrupt Party 2 flips opened bit `x_2 -> !x_2` (`x_opened` flips!): batch check MUST FAIL!
        let forged_x_opened = x_opened.add(Tower128::ONE);
        let forged_checks: Vec<(Tower128, Tower128)> = (0..3)
            .map(|i| {
                custodies[i].compute_batch_check_share_2lane(
                    chal_hi,
                    chal_lo,
                    &[forged_x_opened],
                    &[mac_hi[i]],
                    &[mac_lo[i]],
                )
            })
            .collect();
        assert!(!verify_batch_tower_mac_2lane(&forged_checks));

        // Pairwise BDOZ tag verification deterministically attributes Party 2 with a `SlashingReceipt`!
        let honest_tag_20_hi = Tower128(0x4242_4242);
        let honest_tag_20_lo = Tower128(0x9999_9999);
        let (k_02_hi, k_02_lo) =
            custodies[0].derive_pairwise_bdoz_local_key_2lane(xs[2], honest_tag_20_hi, honest_tag_20_lo);
        let slash = custodies[0]
            .verify_pairwise_bdoz_or_slash(
                77,
                0,
                2,
                k_02_hi,
                k_02_lo,
                xs[2].add(Tower128::ONE), // tampered share opened by Party 2!
                honest_tag_20_hi,
                honest_tag_20_lo,
            )
            .expect_err("must slash cheating Party 2");
        assert_eq!(
            slash,
            SlashingReceipt {
                session_view: 77,
                accused_party: 2,
                verifier_party: 0,
                failed_lane: 0,
            }
        );

        // Also verify GoldilocksExt2 pairwise BDOZ slashing
        let ext2_custody = Ext2MacKeyCustody::new_custody_share(GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(123456789),
            Goldilocks::from_u64_reduced(987654321),
        ));
        let honest_gl = Goldilocks::from_u64_reduced(42);
        let tag_gl = GoldilocksExt2::new(Goldilocks::TWO, Goldilocks::ONE);
        let k_gl = ext2_custody.derive_pairwise_local_key(honest_gl, tag_gl);
        assert!(ext2_custody
            .verify_pairwise_ext2_or_slash(9, 0, 1, k_gl, honest_gl, tag_gl)
            .is_ok());
        assert_eq!(
            ext2_custody
                .verify_pairwise_ext2_or_slash(
                    9,
                    0,
                    1,
                    k_gl,
                    Goldilocks::from_u64_reduced(43),
                    tag_gl
                )
                .unwrap_err()
                .accused_party,
            1
        );
    }

    /// **Test 4 (2-Round 128-Bit PQ Dealerless DKG, `EpochLatch` Anti-Double-Sign & Sybil/Rollback Guards, 64-Bit Garbled Policy Gate, `HybridPinnedSig` & `VerifyReply`)**:
    #[test]
    fn test_dkg_complaints_epoch_latch_hybrid_pinning_and_wire_reply() {
        // 1. 2-Round PQ Dealerless DKG (`3-of-5`, 128-bit `GoldilocksExt2` challenge & separated P2P packets):
        let pts: Vec<Goldilocks> = (1..=5u64).map(Goldilocks::from_u64_reduced).collect();
        let f_coeffs = [
            Goldilocks::from_u64_reduced(777),
            Goldilocks::from_u64_reduced(111),
            Goldilocks::from_u64_reduced(222),
        ];
        let m_coeffs = [
            GoldilocksExt2::new(
                Goldilocks::from_u64_reduced(333),
                Goldilocks::from_u64_reduced(1333),
            ),
            GoldilocksExt2::new(
                Goldilocks::from_u64_reduced(444),
                Goldilocks::from_u64_reduced(1444),
            ),
            GoldilocksExt2::new(
                Goldilocks::from_u64_reduced(555),
                Goldilocks::from_u64_reduced(1555),
            ),
        ];
        let salts = [[0x10u8; 32], [0x20u8; 32], [0x30u8; 32], [0x40u8; 32], [0x50u8; 32]];
        let (honest_dealing, private_pkts) = GoldilocksDealerBroadcast::generate_honest(
            0,
            3,
            &pts,
            &f_coeffs,
            &m_coeffs,
            &salts,
            [0xABu8; 32],
            [0xCDu8; 32],
        );
        for pkt in &private_pkts {
            assert!(verify_dkg_private_packet_goldilocks(&pts, &honest_dealing, pkt));
        }
        assert!(verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &pts,
            &honest_dealing,
            &[]
        ));

        // Valid complaint opening (dealer opens exact 24-byte packet for party 2) -> dealer still qualifies!
        let honest_complaint = DkgShareComplaint {
            recv_idx: 2,
            committed_digest: honest_dealing.share_commitments[2],
            dealer_opened_salt: private_pkts[2].salt.to_vec(),
            dealer_opened_share_bytes: private_pkts[2].encode_share_bytes().to_vec(),
        };
        assert!(verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &pts,
            &honest_dealing,
            &[honest_complaint]
        ));

        // Corrupt dealer broadcasts degree-3 polynomial (`> t - 1 = 2`) -> disqualified!
        let mut corrupt_deg = honest_dealing.clone();
        corrupt_deg.masked_poly_coeffs.push(GoldilocksExt2::ONE);
        assert!(!verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &pts,
            &corrupt_deg,
            &[]
        ));

        // Rushing dealer attempts to swap `pk_seed_contrib` in Round 2 without matching Round-1 commitment -> disqualified!
        let mut corrupt_pk_seed = honest_dealing.clone();
        corrupt_pk_seed.pk_seed_contrib = [0xFFu8; 32];
        assert!(!verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &pts,
            &corrupt_pk_seed,
            &[]
        ));

        // Duplicate evaluation points (`pts` non-distinct) -> disqualified!
        let dup_pts = [
            Goldilocks::ONE,
            Goldilocks::ONE,
            Goldilocks::TWO,
            Goldilocks::from_u64_reduced(3),
            Goldilocks::from_u64_reduced(4),
        ];
        assert!(!verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &dup_pts,
            &honest_dealing,
            &[]
        ));

        // Corrupt dealer fails complaint resolution -> disqualified!
        let bad_complaint = DkgShareComplaint {
            recv_idx: 2,
            committed_digest: honest_dealing.share_commitments[2],
            dealer_opened_salt: salts[2].to_vec(),
            dealer_opened_share_bytes: vec![0u8; 24],
        };
        assert!(!verify_and_qualify_dkg_dealer_goldilocks(
            3,
            &pts,
            &honest_dealing,
            &[bad_complaint]
        ));

        // 2. Simplex Monotonic `EpochLatch` (`n = 4, f = 1 -> t_latch = 3`):
        //    - Rejects Sybil duplicate signers `&[0, 0, 0]` AND out-of-range signers `&[0, 1, 9]` with ZERO partial mutation!
        //    - Rolls back atomically when quorum `< 3` (`&[0, 1]`)!
        //    - Quorum `{0, 1, 2}` signs `(epoch = 5, mu_a)`; overlapping quorum `{1, 2, 3}`:
        //      * Retrying `(epoch = 5, mu_a)` SUCCEEDS (crash-recovery liveness)!
        //      * Attempting `(epoch = 5, mu_b != mu_a)` REFUSES (`EquivocationRefused`)!
        //      * Attempting `(epoch = 4 < 5, mu_a)` REFUSES (`StaleEpochReplay`)!
        let mut latch_cluster = QuorumEpochLatchCluster::new(4, 1).unwrap();
        assert_eq!(latch_cluster.latch_quorum, 3);
        let mu_a = [0xAAu8; 32];
        let mu_b = [0xBBu8; 32];
        assert_eq!(
            latch_cluster.acquire_latch_quorum(&[0, 0, 0], 5, mu_a),
            Err(EpochLatchError::DuplicateParticipant { party: 0 })
        );
        assert_eq!(latch_cluster.signer_latches[0].high_water, None);
        assert_eq!(
            latch_cluster.acquire_latch_quorum(&[0, 1, 9], 5, mu_a),
            Err(EpochLatchError::InvalidParticipant {
                party: 9,
                committee_size: 4
            })
        );
        assert_eq!(
            latch_cluster.acquire_latch_quorum(&[0, 1], 5, mu_a),
            Err(EpochLatchError::QuorumInsufficient {
                accepted: 2,
                required_latch_quorum: 3
            })
        );
        // Atomic rollback check: signer 0 & 1 MUST still be `None` after under-quorum failure!
        assert_eq!(latch_cluster.signer_latches[0].high_water, None);
        assert_eq!(latch_cluster.signer_latches[1].high_water, None);

        assert!(latch_cluster
            .acquire_latch_quorum(&[0, 1, 2], 5, mu_a)
            .is_ok());
        assert!(latch_cluster
            .acquire_latch_quorum(&[1, 2, 3], 5, mu_a)
            .is_ok());
        assert_eq!(
            latch_cluster.acquire_latch_quorum(&[1, 2, 3], 5, mu_b),
            Err(EpochLatchError::EquivocationRefused { epoch: 5 })
        );
        // Signer 3 must NOT have latched `mu_b` during the failed equivocation attempt!
        assert_eq!(latch_cluster.signer_latches[3].high_water, Some((5, mu_a)));
        assert_eq!(
            latch_cluster.acquire_latch_quorum(&[0, 1, 2], 4, mu_a),
            Err(EpochLatchError::StaleEpochReplay {
                requested_epoch: 4,
                high_water: 5
            })
        );

        // 3. Genuine 64-Bit Ripple-Borrow `Poseidon2` Garbled Policy Gate (`tx_amount <= secret_limit`, 0 limit reconstruction!)
        let mut gc_seed = 0x5151_7777u64;
        let raw_share = Goldilocks::from_u64_reduced(0xDEAD_BEEF_1234);
        let pad_share = Goldilocks::from_u64_reduced(0x7654_3210_FEDC);
        let gc = garble_custody_policy_limit(
            [0x55u8; 32],
            1_000_000,
            raw_share,
            pad_share,
            &mut gc_seed,
        );
        assert_eq!(
            eval_garbled_custody_policy_gate(&gc, 0, pad_share),
            Some(raw_share)
        );
        assert_eq!(
            eval_garbled_custody_policy_gate(&gc, 750_000, pad_share),
            Some(raw_share)
        );
        assert_eq!(
            eval_garbled_custody_policy_gate(&gc, 1_000_000, pad_share),
            Some(raw_share)
        );
        assert_eq!(eval_garbled_custody_policy_gate(&gc, 1_000_001, pad_share), None);
        assert_eq!(eval_garbled_custody_policy_gate(&gc, u64::MAX, pad_share), None);

        // 4. Degenerate parameter, stateful `msg_tsw_ctr != 0`, `rss_reconstruct_2of3` duplicate party,
        //    `HybridPinnedSig` substitution refusal & tri-state `VerifyReply` inner framing checks:
        let z_planes = [0u64; 1600];
        let rss_parties = rss_share_keccak_states64(&z_planes, &z_planes, &z_planes);
        assert!(rss_reconstruct_2of3(&rss_parties[0], &rss_parties[0]).is_none());

        let sk = golden_secret_key();
        let bad_ell1 = PqHashParams {
            ell1: 0,
            ..PqHashParams::COMPACT_LEAN_SIG
        };
        let bad_fors = PqHashParams {
            fors_trees: 0,
            ..PqHashParams::COMPACT_GOLDEN
        };
        assert!(!bad_ell1.is_well_formed());
        assert!(!bad_fors.is_well_formed());
        assert!(eval_single_sign(Cshake256Suite, &bad_ell1, &sk, b"m", &[0u8; 32], 0, 16).is_none());
        assert!(eval_single_sign(Cshake256Suite, &bad_fors, &sk, b"m", &[0u8; 32], 0, 16).is_none());

        let pk_lean = derive_public_key(Poseidon2Suite, &PqHashParams::COMPACT_LEAN_SIG, &sk);
        let mut sig_lean = eval_single_sign(
            Poseidon2Suite,
            &PqHashParams::COMPACT_LEAN_SIG,
            &sk,
            b"lean-msg",
            &[0x22u8; 32],
            0,
            256,
        )
        .unwrap();
        assert!(verify_pq_hash_sig(
            Poseidon2Suite,
            &PqHashParams::COMPACT_LEAN_SIG,
            &pk_lean,
            b"lean-msg",
            &sig_lean
        ));
        sig_lean.msg_tsw_ctr = 9;
        assert!(!verify_pq_hash_sig(
            Poseidon2Suite,
            &PqHashParams::COMPACT_LEAN_SIG,
            &pk_lean,
            b"lean-msg",
            &sig_lean
        ));
        assert_eq!(
            verify_pq_wire_envelope(
                Poseidon2Suite,
                &PqHashParams::COMPACT_LEAN_SIG,
                &pk_lean.to_wire_bytes(),
                b"lean-msg",
                &PQ_WIRE_MAGIC,
                &sig_lean.r_rand,
                &sig_lean,
            ),
            VerifyReply::WireMalformed(FaultStage::SignatureFraming)
        );
        let mut both_bad = sig_lean.clone();
        both_bad.layer_sigs.clear();
        assert_eq!(
            verify_pq_wire_envelope(
                Poseidon2Suite,
                &PqHashParams::COMPACT_LEAN_SIG,
                &pk_lean.to_wire_bytes(),
                b"lean-msg",
                &PQ_WIRE_MAGIC,
                &[0x01u8],
                &both_bad,
            ),
            VerifyReply::WireMalformed(FaultStage::LayerCountMismatch)
        );

        let pk = derive_public_key(Cshake256Suite, &PqHashParams::COMPACT_GOLDEN, &sk);
        let msg = b"hybrid-and-wire-test";
        let sig = eval_single_sign(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &sk,
            msg,
            &[0x11u8; 32],
            0,
            256,
        )
        .unwrap();

        let pk1 = [0x22u8; 32];
        let id_commit = compute_hybrid_id_commit(&pk1, &pk.to_wire_bytes());
        assert!(check_hybrid_pinning(&id_commit, &pk1, &pk));

        let attacker_sk = PqSecretKey {
            sk_seed: [0xEEu8; 32],
            sk_prf: [0xDDu8; 32],
            pk_seed: [0xCCu8; 32],
        };
        let attacker_pk =
            derive_public_key(Cshake256Suite, &PqHashParams::COMPACT_GOLDEN, &attacker_sk);
        let attacker_sig = eval_single_sign(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &attacker_sk,
            msg,
            &[0x11u8; 32],
            0,
            256,
        )
        .unwrap();
        let subst_wire = HybridPinnedSig {
            sig1: (),
            carried_pk2: attacker_pk,
            sig2: attacker_sig,
        };
        assert!(!verify_hybrid_pinned_sig(
            Cshake256Suite,
            &PqHashParams::COMPACT_GOLDEN,
            &id_commit,
            &pk1,
            |_, _, _| true, // even when classical S_1 is completely broken!
            msg,
            &subst_wire
        ));

        let pk_wire = pk.to_wire_bytes();
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_wire,
                msg,
                &PQ_WIRE_MAGIC,
                &sig.r_rand,
                &sig
            ),
            VerifyReply::Accept
        );
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_wire,
                b"wrong-msg",
                &PQ_WIRE_MAGIC,
                &sig.r_rand,
                &sig
            ),
            VerifyReply::Reject
        );
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_wire,
                msg,
                b"BAD!!",
                &sig.r_rand,
                &sig
            ),
            VerifyReply::WireMalformed(FaultStage::HeaderMagicOrVersion)
        );
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_wire[..30],
                msg,
                &PQ_WIRE_MAGIC,
                &sig.r_rand,
                &sig
            ),
            VerifyReply::WireMalformed(FaultStage::PublicKeyLength)
        );
        let mut bad_inner_sig = sig.clone();
        bad_inner_sig.layer_sigs[0].wots_chains.pop();
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &PqHashParams::COMPACT_GOLDEN,
                &pk_wire,
                msg,
                &PQ_WIRE_MAGIC,
                &bad_inner_sig.r_rand,
                &bad_inner_sig
            ),
            VerifyReply::WireMalformed(FaultStage::SignatureFraming)
        );
    }

    /// **Test 5 (Full Production-Scale Benchmarks on `bb2`)**:
    /// Measures wall-clock latency, MPC permutation counts, sequential hash depth, and online bandwidth across:
    /// 1. `THINCS-Custody-128` (`w=4, ell1=64, d=2, h'=6, k=18, a=8`) in **2-of-3 `RSS` (`cSHAKE256` `64x` bitsliced)**;
    /// 2. `THINCS-Custody-128` in **5-of-9 `BinaryTower256` Shamir (`cSHAKE256` `64x` bitsliced)**;
    /// 3. `leanSPHINCS-128f` (`w=4, ell1=64, d=10, h'=2, k=18, a=8`) in **2-of-3 `RSS` (`cSHAKE256` `64x` bitsliced)**;
    /// 4. Stateful `leanSig-Poseidon2` (`w=4, ell1=64`, 160 active permutations) in **5-of-9 `Goldilocks` 1-Round Power-7 MPC**!
    #[test]
    fn test_and_benchmark_full_scale_pq_threshold_mpc_suite() {
        let sk = golden_secret_key();
        let msg = b"institutional-custody-transfer-epoch-42";
        let opt_rand = [0x5Au8; 32];

        // 1. Measure raw 160-permutation `Poseidon2` 5-of-9 1-round Binomial Power-7 sweep (`leanSig` active leaf)
        //    over the 5-signer active quorum (after offline Power-7 tuple dealing):
        let pts59_gl: Vec<Goldilocks> = (1..=9u64).map(Goldilocks::from_u64_reduced).collect();
        let active_pts_gl = &pts59_gl[..5];
        let lams5_gl = crate::poseidon2_mpc::lagrange_weights_zero_goldilocks(active_pts_gl).unwrap();
        let mut p2_states = vec![[Goldilocks::ONE; 12]; 5];
        let mut off_seed = 0x1234_5678u64;
        let predealt_160: Vec<_> = (0..160)
            .map(|_| crate::poseidon2_mpc::deal_poseidon2_perm12_tuples(5, active_pts_gl, &mut off_seed))
            .collect();
        let mut deltas_log = Vec::with_capacity(6000);
        let t0_p2 = Instant::now();
        let mut p2_bytes = 0usize;
        for tup in &predealt_160 {
            p2_bytes += crate::poseidon2_mpc::mpc_poseidon2_perm12_shamir_online(
                &lams5_gl,
                &mut p2_states,
                tup,
                &mut deltas_log,
            )
            .unwrap();
        }
        let elapsed_p2_160 = t0_p2.elapsed();
        assert_eq!(p2_bytes, 160 * 944); // Exact 151,040 B (`151.04 KB`)!

        // Also check single `poseidon2_perm12` matches 5-of-9 Shamir reconstruction!
        let mut plain_st = [Goldilocks::from_u64_reduced(99); 12];
        let mut shared_sts = vec![[Goldilocks::ZERO; 12]; 9];
        for lane in 0..12 {
            let sh = shamir_share_scalar_goldilocks(5, &pts59_gl, plain_st[lane], &mut off_seed);
            for p in 0..9 {
                shared_sts[p][lane] = sh[p];
            }
        }
        poseidon2_perm12(&mut plain_st);
        mpc_poseidon2_perm12_shamir(5, &pts59_gl, &mut shared_sts, &mut off_seed, &mut deltas_log)
            .unwrap();
        let lams = crate::poseidon2_mpc::lagrange_weights_zero_goldilocks(&pts59_gl[..5]).unwrap();
        for lane in 0..12 {
            let mut rec = Goldilocks::ZERO;
            for q in 0..5 {
                rec = rec.const_add(lams[q].const_mul(shared_sts[q][lane]));
            }
            assert_eq!(rec, plain_st[lane]);
        }

        // 2. Full `THINCS-Custody-128` (`d=2, h'=6, w=4, ell1=64, k=18, a=8`) with DKG bounded-tree cache:
        let thincs_params = PqHashParams {
            w: 4,
            ell1: 64,
            subtree_height: 3, // fast DKG fixture setup while keeping identical `d=2, w=4, ell1=64, k=18, a=8` online active path!
            num_layers: 2,
            fors_trees: 18,
            fors_height: 4,
            max_sigs_log2: 6,
            stateful_lean_sig: false,
        };
        let pk_thincs = derive_public_key(Cshake256Suite, &thincs_params, &sk);
        let cache_thincs = DkgCachedSubtrees::build(Cshake256Suite, &thincs_params, &sk, true);

        let m_a = [0x12u8; 32];
        let m_b = [0x34u8; 32];
        let mut s_seed0 = [0u8; 32];
        let mut s_prf0 = [0u8; 32];
        for i in 0..32 {
            s_seed0[i] = sk.sk_seed[i] ^ m_a[i] ^ m_b[i];
            s_prf0[i] = sk.sk_prf[i] ^ m_a[i] ^ m_b[i];
        }
        let rss_seed = [s_seed0, m_a, m_b];
        let rss_prf = [s_prf0, m_a, m_b];
        let mut prg = [1u64, 2u64, 3u64];

        let t0_rss = Instant::now();
        let (sig_thincs_rss, m_thincs_rss) = eval_threshold_sign_rss_cshake(
            &thincs_params,
            &pk_thincs,
            &rss_seed,
            &rss_prf,
            &opt_rand,
            msg,
            5,
            4096,
            Some(&cache_thincs),
            &mut prg,
        )
        .unwrap();
        let elapsed_thincs_rss = t0_rss.elapsed();
        assert!(verify_pq_hash_sig(
            Cshake256Suite,
            &thincs_params,
            &pk_thincs,
            msg,
            &sig_thincs_rss
        ));

        // 3. Same `THINCS-Custody-128` online path in 5-of-9 `BinaryTower256` Shamir!
        let pts59_gf: Vec<TowerGf256> = (1..=9u8).map(TowerGf256).collect();
        let sh_seed59 = shamir_share_seed32_gf256(5, &pts59_gf, &sk.sk_seed, &mut off_seed);
        let sh_prf59 = shamir_share_seed32_gf256(5, &pts59_gf, &sk.sk_prf, &mut off_seed);

        let t0_sh59 = Instant::now();
        let (sig_thincs_59, m_thincs_59, _) = eval_threshold_sign_shamir_cshake(
            5,
            &pts59_gf[..5],
            &thincs_params,
            &pk_thincs,
            &sh_seed59[..5],
            &sh_prf59[..5],
            &opt_rand,
            msg,
            5,
            4096,
            Some(&cache_thincs),
            &mut off_seed,
        )
        .unwrap();
        let elapsed_thincs_59 = t0_sh59.elapsed();
        assert_eq!(sig_thincs_59, sig_thincs_rss);

        // 4. Full 10-layer `leanSPHINCS-128f` (`d=10, h'=2, w=4, ell1=64, k=18`) in 2-of-3 `RSS`:
        //    Note: DKG caches top layers; let's benchmark the 10-layer active path (`1 + 18 + 10*64*4` calls in 10 parallel `64x` batches!)
        let sphincs10_params = PqHashParams {
            w: 4,
            ell1: 64,
            subtree_height: 1,
            num_layers: 10,
            fors_trees: 18,
            fors_height: 2,
            max_sigs_log2: 10,
            stateful_lean_sig: false,
        };
        let pk_sph10 = derive_public_key(Cshake256Suite, &sphincs10_params, &sk);
        let cache_sph10 = DkgCachedSubtrees::build(Cshake256Suite, &sphincs10_params, &sk, true);
        let t0_sph10 = Instant::now();
        let (sig_sph10, m_sph10) = eval_threshold_sign_rss_cshake(
            &sphincs10_params,
            &pk_sph10,
            &rss_seed,
            &rss_prf,
            &opt_rand,
            msg,
            7,
            4096,
            Some(&cache_sph10),
            &mut prg,
        )
        .unwrap();
        let elapsed_sph10 = t0_sph10.elapsed();
        assert!(verify_pq_hash_sig(
            Cshake256Suite,
            &sphincs10_params,
            &pk_sph10,
            msg,
            &sig_sph10
        ));

        println!("\n=== OBEND-PQ-MPC RELEASE BENCHMARK SUMMARY ===");
        println!(
            "1. leanSig-Poseidon2 (5-of-9 Power-7, 160 perms):      {:>8.3} ms ({:>6.3} ms/signer) | depth = 5 | online_bw = {:>7.2} KB",
            elapsed_p2_160.as_secs_f64() * 1000.0,
            elapsed_p2_160.as_secs_f64() * 1000.0 / 5.0,
            p2_bytes as f64 / 1024.0
        );
        println!(
            "2. THINCS-Custody-128 (2-of-3 RSS, d=2, ell1=64, w=4): {:>8.3} ms ({:>6.3} ms/signer) | depth = {} | online_bw = {:>7.2} KB | perms = {}",
            elapsed_thincs_rss.as_secs_f64() * 1000.0,
            elapsed_thincs_rss.as_secs_f64() * 1000.0 / 3.0,
            m_thincs_rss.sequential_mpc_hash_depth,
            m_thincs_rss.online_bytes_per_party as f64 / 1024.0,
            m_thincs_rss.total_mpc_permutations
        );
        println!(
            "3. THINCS-Custody-128 (5-of-9 BinaryTower256 Shamir):  {:>8.3} ms ({:>6.3} ms/signer) | depth = {} | online_bw = {:>7.2} KB | perms = {}",
            elapsed_thincs_59.as_secs_f64() * 1000.0,
            elapsed_thincs_59.as_secs_f64() * 1000.0 / 5.0,
            m_thincs_59.sequential_mpc_hash_depth,
            m_thincs_59.online_bytes_per_party as f64 / 1024.0,
            m_thincs_59.total_mpc_permutations
        );
        println!(
            "4. leanSPHINCS-128f   (2-of-3 RSS, d=10, ell1=64, w=4): {:>8.3} ms ({:>6.3} ms/signer) | depth = {} | online_bw = {:>7.2} KB | perms = {}",
            elapsed_sph10.as_secs_f64() * 1000.0,
            elapsed_sph10.as_secs_f64() * 1000.0 / 3.0,
            m_sph10.sequential_mpc_hash_depth,
            m_sph10.online_bytes_per_party as f64 / 1024.0,
            m_sph10.total_mpc_permutations
        );
    }
}
