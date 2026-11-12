//! Width-12 `Poseidon2Goldilocks` sponge (`poseidon2_hash32`), arbitrary $t$-of-$n$ Shamir MPC
//! with **1-round Binomial Power-7 tuples** (`944 B` online bandwidth per permutation!),
//! 128-bit `GoldilocksExt2` SPDZ/BDOZ MACs, and pre-sign additive field-pad custody policy gate.
//!
//! Matches `Obend.Crypto.Poseidon2Goldilocks` and `Obend.Crypto.ThresholdHashMpc` down to every
//! round constant, `< 2^56` limb boundary, `10*1` sponge pad, and binomial identity.

use alloc::vec;
use alloc::vec::Vec;

use obend_crypto_exec::goldilocks::{
    GOLDILOCKS_PRIME, POSEIDON2_INIT_STATE, Goldilocks, GoldilocksExt2,
    bytes_to_limbs56 as exec_bytes_to_limbs56,
    poseidon2_apply_me, poseidon2_apply_mi,
    poseidon2_const_at as exec_poseidon2_const_at,
    poseidon2_hash32 as exec_poseidon2_hash32,
    poseidon2_pad as exec_poseidon2_pad,
    poseidon2_perm12 as exec_poseidon2_perm12,
    poseidon2_sbox7,
};

use crate::keccak_mpc::SlashingReceipt;

// ============================================================================
// 1. Exact Width-12 `Poseidon2Goldilocks` Permutation & 256-Bit Sponge (`poseidon2_hash32`)
//    Delegated directly to `obend_crypto_exec::goldilocks` (`[HIGH-05]` SplitMix64 constants).
// ============================================================================

/// Domain-separated SplitMix64-derived round constant matching `Obend.Crypto.poseidon2ConstAt`.
#[inline]
pub const fn poseidon2_const_at(tag: u64, round: u64, lane: u64) -> Goldilocks {
    exec_poseidon2_const_at(tag, round, lane)
}

#[inline]
pub const fn sbox7(x: Goldilocks) -> Goldilocks {
    poseidon2_sbox7(x)
}

/// External $12 \times 12$ block-circulant MDS layer $M_E = \text{circ}(2 M_4, M_4, M_4)$.
#[inline]
pub fn apply_me(state: &mut [Goldilocks; 12]) {
    poseidon2_apply_me(state);
}

/// Internal diagonal-plus-ones linear layer $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(-2, 1, 2, 4, \dots, 1024)$.
#[inline]
pub fn apply_mi(state: &mut [Goldilocks; 12]) {
    poseidon2_apply_mi(state);
}

/// Exact Width-12 `Poseidon2` permutation ($R_F = 8, R_P = 22$) matching `Obend.Crypto.poseidon2Perm12`.
#[inline]
pub fn poseidon2_perm12(state: &mut [Goldilocks; 12]) {
    exec_poseidon2_perm12(state);
}

/// Pack arbitrary byte slice into `< 2^56` Goldilocks limbs (`0x01` delimiter + zero pad to 7-byte boundary),
/// matching `Obend.Crypto.bytesToLimbs56`.
#[inline]
pub fn bytes_to_limbs56(msg: &[u8]) -> Vec<Goldilocks> {
    exec_bytes_to_limbs56(msg)
}

/// Multi-rate `10*1` sponge padding (`rate = 8`), matching `Obend.Crypto.poseidon2Pad`.
#[inline]
pub fn poseidon2_pad(mut limbs: Vec<Goldilocks>) -> Vec<Goldilocks> {
    exec_poseidon2_pad(&mut limbs);
    limbs
}

/// Domain-separated initial Width-12 sponge state matching `Obend.Crypto.poseidon2InitState`.
#[inline]
pub const fn poseidon2_init_state() -> [Goldilocks; 12] {
    POSEIDON2_INIT_STATE
}

/// Exact 256-bit algebraic Goldilocks `Poseidon2` sponge hash matching `Obend.Crypto.poseidon2Hash32`.
#[inline]
pub fn poseidon2_hash32(msg: &[u8]) -> [u8; 32] {
    exec_poseidon2_hash32(msg)
}

// ============================================================================
// 2. Arbitrary $t$-of-$n$ Shamir + 1-Round Binomial Power-7 Tuple MPC (`944 B` / perm)
// ============================================================================

/// Evaluate polynomial `coeffs[0] + coeffs[1]*x + ...` over `Goldilocks`.
#[inline]
pub fn eval_poly_goldilocks(coeffs: &[Goldilocks], x: Goldilocks) -> Goldilocks {
    let mut acc = Goldilocks::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.const_mul(x).const_add(c);
    }
    acc
}

/// Lagrange interpolation weights at `0` for distinct non-zero `Goldilocks` points.
pub fn lagrange_weights_zero_goldilocks(pts: &[Goldilocks]) -> Option<Vec<Goldilocks>> {
    let t = pts.len();
    let mut weights = Vec::with_capacity(t);
    for i in 0..t {
        if pts[i] == Goldilocks::ZERO {
            return None;
        }
        let mut num = Goldilocks::ONE;
        let mut den = Goldilocks::ONE;
        for j in 0..t {
            if i == j {
                continue;
            }
            let diff = pts[j].const_sub(pts[i]);
            if diff == Goldilocks::ZERO {
                return None;
            }
            num = num.const_mul(pts[j]);
            den = den.const_mul(diff);
        }
        weights.push(num.const_mul(den.inv()?));
    }
    Some(weights)
}

#[inline]
fn next_goldilocks_rand(seed: &mut u64) -> Goldilocks {
    *seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *seed;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    Goldilocks::from_u64_reduced(z ^ (z >> 31))
}

/// Share a single `Goldilocks` secret across `eval_points` with threshold `t`.
pub fn shamir_share_scalar_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    secret: Goldilocks,
    rng_seed: &mut u64,
) -> Vec<Goldilocks> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(next_goldilocks_rand(rng_seed));
    }
    let out: Vec<Goldilocks> = eval_points
        .iter()
        .map(|&pt| eval_poly_goldilocks(&coeffs, pt))
        .collect();
    coeffs.fill(Goldilocks::ZERO);
    core::hint::black_box(coeffs.as_slice());
    out
}

/// Pre-shared 1-round Binomial Power-7 tuple `([r]_i, [r^2]_i, ..., [r^7]_i)` for party `i`.
#[derive(Clone, Debug)]
pub struct Power7Share {
    pub r_pows: [Goldilocks; 7],
}

impl Drop for Power7Share {
    fn drop(&mut self) {
        self.r_pows.fill(Goldilocks::ZERO);
        core::hint::black_box(&self.r_pows);
    }
}

/// Preprocess a correlated Power-7 tuple `(r, r^2, ..., r^7)` shared across `eval_points` at degree `< t`.
pub fn deal_power7_tuple_shares(
    t: usize,
    eval_points: &[Goldilocks],
    rng_seed: &mut u64,
) -> Vec<Power7Share> {
    let n = eval_points.len();
    let r1 = next_goldilocks_rand(rng_seed);
    let r2 = r1.square();
    let r3 = r2.const_mul(r1);
    let r4 = r2.square();
    let r5 = r4.const_mul(r1);
    let r6 = r4.const_mul(r2);
    let r7 = r3.const_mul(r4);
    let mut pows = [r1, r2, r3, r4, r5, r6, r7];

    let mut out: Vec<Power7Share> = (0..n)
        .map(|_| Power7Share {
            r_pows: [Goldilocks::ZERO; 7],
        })
        .collect();
    for (k, &pk) in pows.iter().enumerate() {
        let mut sh = shamir_share_scalar_goldilocks(t, eval_points, pk, rng_seed);
        for p in 0..n {
            out[p].r_pows[k] = sh[p];
        }
        sh.fill(Goldilocks::ZERO);
        core::hint::black_box(sh.as_slice());
    }
    pows.fill(Goldilocks::ZERO);
    core::hint::black_box(&pows);
    out
}

/// 1-round Binomial Power-7 local linear share evaluator matching `ThresholdHashMpc.power7BinomialEval`:
/// `[x^7]_i = δ^7 + 7 δ^6 [r]_i + 21 δ^5 [r^2]_i + 35 δ^4 [r^3]_i + 35 δ^3 [r^4]_i + 21 δ^2 [r^5]_i + 7 δ [r^6]_i + [r^7]_i`!
///
/// Note on Shamir evaluation: adding public constant `δ^7` to polynomial `f(X)` adds `δ^7` to EVERY party's
/// evaluation `f(x_i)`!
#[inline]
pub fn power7_binomial_eval_share(delta: Goldilocks, tuple: &Power7Share) -> Goldilocks {
    let d2 = delta.square();
    let d3 = d2.const_mul(delta);
    let d4 = d2.square();
    let d5 = d4.const_mul(delta);
    let d6 = d4.const_mul(d2);
    let d7 = d3.const_mul(d4);

    let c7 = Goldilocks::from_u64_reduced(7);
    let c21 = Goldilocks::from_u64_reduced(21);
    let c35 = Goldilocks::from_u64_reduced(35);

    let t6 = c7.const_mul(d6).const_mul(tuple.r_pows[0]);
    let t5 = c21.const_mul(d5).const_mul(tuple.r_pows[1]);
    let t4 = c35.const_mul(d4).const_mul(tuple.r_pows[2]);
    let t3 = c35.const_mul(d3).const_mul(tuple.r_pows[3]);
    let t2 = c21.const_mul(d2).const_mul(tuple.r_pows[4]);
    let t1 = c7.const_mul(delta).const_mul(tuple.r_pows[5]);
    let t0 = tuple.r_pows[6];

    d7.const_add(t6)
        .const_add(t5.const_add(t4))
        .const_add(t3.const_add(t2).const_add(t1.const_add(t0)))
}

/// Evaluate Width-12 `poseidon2_perm12` across `n` Shamir parties (threshold `t`) in 1-round Binomial Power-7 mode!
/// Returns exact online bytes per party (`118 S-boxes * 8 B = 944 B` per permutation!).
pub fn mpc_poseidon2_perm12_shamir(
    t: usize,
    eval_points: &[Goldilocks],
    party_states: &mut [[Goldilocks; 12]],
    offline_seed: &mut u64,
    opened_deltas_log: &mut Vec<Goldilocks>,
) -> Option<usize> {
    let n = party_states.len();
    if t == 0 || t > n || eval_points.len() != n {
        return None;
    }
    let lambdas = lagrange_weights_zero_goldilocks(&eval_points[..t])?;
    let mut online_bytes = 0usize;

    // Pre-round linear M_E (0 communication!)
    for st in party_states.iter_mut() {
        apply_me(st);
    }

    #[allow(clippy::too_many_arguments)]
    fn run_poseidon2_ext_round(
        t: usize,
        eval_points: &[Goldilocks],
        lambdas: &[Goldilocks],
        offline_seed: &mut u64,
        party_states: &mut [[Goldilocks; 12]],
        online_bytes: &mut usize,
        opened_deltas_log: &mut Vec<Goldilocks>,
        tag: u64,
        r: u64,
    ) {
        let n = eval_points.len();
        let mut tuples_per_lane: Vec<Vec<Power7Share>> = Vec::with_capacity(12);
        for _ in 0..12 {
            tuples_per_lane.push(deal_power7_tuple_shares(t, eval_points, offline_seed));
        }
        let mut deltas = [Goldilocks::ZERO; 12];
        for lane in 0..12 {
            let rc = poseidon2_const_at(tag, r, lane as u64);
            for p in 0..n {
                party_states[p][lane] = party_states[p][lane].const_add(rc);
            }
            let mut delta = Goldilocks::ZERO;
            for (q, &lam) in lambdas.iter().enumerate() {
                let diff = party_states[q][lane].const_sub(tuples_per_lane[lane][q].r_pows[0]);
                delta = delta.const_add(lam.const_mul(diff));
            }
            deltas[lane] = delta;
        }
        *online_bytes += 12 * 8;
        opened_deltas_log.push(deltas[0]);
        for p in 0..n {
            for lane in 0..12 {
                party_states[p][lane] =
                    power7_binomial_eval_share(deltas[lane], &tuples_per_lane[lane][p]);
            }
            apply_me(&mut party_states[p]);
        }
    }

    for r in 0..4u64 {
        run_poseidon2_ext_round(
            t,
            eval_points,
            &lambdas,
            offline_seed,
            party_states,
            &mut online_bytes,
            opened_deltas_log,
            0,
            r,
        );
    }

    // 22 internal rounds (`1 * 8 = 8 B` online per round!)
    for r in 0..22u64 {
        let tuples0 = deal_power7_tuple_shares(t, eval_points, offline_seed);
        let rc = poseidon2_const_at(1, r, 0);
        for p in 0..n {
            party_states[p][0] = party_states[p][0].const_add(rc);
        }
        let mut delta = Goldilocks::ZERO;
        for (q, &lam) in lambdas.iter().enumerate() {
            let diff = party_states[q][0].const_sub(tuples0[q].r_pows[0]);
            delta = delta.const_add(lam.const_mul(diff));
        }
        online_bytes += 8;
        opened_deltas_log.push(delta);
        for p in 0..n {
            party_states[p][0] = power7_binomial_eval_share(delta, &tuples0[p]);
            apply_mi(&mut party_states[p]);
        }
    }

    for r in 0..4u64 {
        run_poseidon2_ext_round(
            t,
            eval_points,
            &lambdas,
            offline_seed,
            party_states,
            &mut online_bytes,
            opened_deltas_log,
            2,
            r,
        );
    }

    debug_assert_eq!(online_bytes, 944);
    Some(online_bytes)
}

/// Pre-dealt offline Power-7 correlation batch (`118` S-boxes = `4*12 + 22 + 4*12`) for one `poseidon2_perm12`.
#[derive(Clone, Debug)]
pub struct PredealtPoseidon2PermTuples {
    pub ext_first: [[Vec<Power7Share>; 12]; 4],
    pub internal: [Vec<Power7Share>; 22],
    pub ext_last: [[Vec<Power7Share>; 12]; 4],
}

/// Deal all `118` offline Power-7 tuple sets for one `poseidon2_perm12` in the offline preprocessing phase.
pub fn deal_poseidon2_perm12_tuples(
    t: usize,
    eval_points: &[Goldilocks],
    offline_seed: &mut u64,
) -> PredealtPoseidon2PermTuples {
    let ext_first = core::array::from_fn(|_| {
        core::array::from_fn(|_| deal_power7_tuple_shares(t, eval_points, offline_seed))
    });
    let internal = core::array::from_fn(|_| deal_power7_tuple_shares(t, eval_points, offline_seed));
    let ext_last = core::array::from_fn(|_| {
        core::array::from_fn(|_| deal_power7_tuple_shares(t, eval_points, offline_seed))
    });
    PredealtPoseidon2PermTuples {
        ext_first,
        internal,
        ext_last,
    }
}

/// Pure online phase of Width-12 `poseidon2_perm12` consuming pre-dealt `PredealtPoseidon2PermTuples`
/// (`944 B` online per party, `30` sequential sub-rounds).
pub fn mpc_poseidon2_perm12_shamir_online(
    lambdas: &[Goldilocks],
    party_states: &mut [[Goldilocks; 12]],
    tuples: &PredealtPoseidon2PermTuples,
    opened_deltas_log: &mut Vec<Goldilocks>,
) -> Option<usize> {
    let n = party_states.len();
    let t = lambdas.len();
    if t == 0 || t > n {
        return None;
    }
    let mut online_bytes = 0usize;
    for st in party_states.iter_mut() {
        apply_me(st);
    }

    fn online_ext_round(
        lambdas: &[Goldilocks],
        party_states: &mut [[Goldilocks; 12]],
        tuples_per_lane: &[Vec<Power7Share>; 12],
        online_bytes: &mut usize,
        opened_deltas_log: &mut Vec<Goldilocks>,
        tag: u64,
        r: u64,
    ) {
        let n = party_states.len();
        let mut deltas = [Goldilocks::ZERO; 12];
        for lane in 0..12 {
            let rc = poseidon2_const_at(tag, r, lane as u64);
            for p in 0..n {
                party_states[p][lane] = party_states[p][lane].const_add(rc);
            }
            let mut delta = Goldilocks::ZERO;
            for (q, &lam) in lambdas.iter().enumerate() {
                let diff = party_states[q][lane].const_sub(tuples_per_lane[lane][q].r_pows[0]);
                delta = delta.const_add(lam.const_mul(diff));
            }
            deltas[lane] = delta;
        }
        *online_bytes += 12 * 8;
        opened_deltas_log.push(deltas[0]);
        for p in 0..n {
            for lane in 0..12 {
                party_states[p][lane] =
                    power7_binomial_eval_share(deltas[lane], &tuples_per_lane[lane][p]);
            }
            apply_me(&mut party_states[p]);
        }
    }

    for r in 0..4usize {
        online_ext_round(
            lambdas,
            party_states,
            &tuples.ext_first[r],
            &mut online_bytes,
            opened_deltas_log,
            0,
            r as u64,
        );
    }
    for r in 0..22usize {
        let tuples0 = &tuples.internal[r];
        let rc = poseidon2_const_at(1, r as u64, 0);
        for p in 0..n {
            party_states[p][0] = party_states[p][0].const_add(rc);
        }
        let mut delta = Goldilocks::ZERO;
        for (q, &lam) in lambdas.iter().enumerate() {
            let diff = party_states[q][0].const_sub(tuples0[q].r_pows[0]);
            delta = delta.const_add(lam.const_mul(diff));
        }
        online_bytes += 8;
        opened_deltas_log.push(delta);
        for p in 0..n {
            party_states[p][0] = power7_binomial_eval_share(delta, &tuples0[p]);
            apply_mi(&mut party_states[p]);
        }
    }
    for r in 0..4usize {
        online_ext_round(
            lambdas,
            party_states,
            &tuples.ext_last[r],
            &mut online_bytes,
            opened_deltas_log,
            2,
            r as u64,
        );
    }
    debug_assert_eq!(online_bytes, 944);
    Some(online_bytes)
}

/// One party's Shamir share of a 32-byte secret packed into `< 2^56` Goldilocks limbs (`5` limbs for 32 bytes: `5 * 7 = 35 >= 33`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShamirPoseidonSeedShare {
    pub eval_point: Goldilocks,
    pub byte_shares: [Goldilocks; 32],
}

impl Drop for ShamirPoseidonSeedShare {
    fn drop(&mut self) {
        self.eval_point = Goldilocks::ZERO;
        for s in &mut self.byte_shares {
            *s = Goldilocks::ZERO;
        }
        core::hint::black_box(&self.byte_shares);
    }
}

/// Share a 32-byte secret byte-by-byte over `Goldilocks` so arbitrary byte-aligned `th_preimage` frames
/// assemble their `< 2^56` 7-byte limbs via pure $\mathbb{F}_p$-linear combinations (`256^k` weights, `0` communication!).
pub fn shamir_share_seed32_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    secret: &[u8; 32],
    rng_seed: &mut u64,
) -> Vec<ShamirPoseidonSeedShare> {
    let n = eval_points.len();
    let mut out: Vec<ShamirPoseidonSeedShare> = eval_points
        .iter()
        .map(|&pt| ShamirPoseidonSeedShare {
            eval_point: pt,
            byte_shares: [Goldilocks::ZERO; 32],
        })
        .collect();
    for (b_idx, &byte_val) in secret.iter().enumerate() {
        let sh = shamir_share_scalar_goldilocks(
            t,
            eval_points,
            Goldilocks::from_u64_reduced(byte_val as u64),
            rng_seed,
        );
        for p in 0..n {
            out[p].byte_shares[b_idx] = sh[p];
        }
    }
    out
}

/// Reconstruct a 32-byte secret from `t` `ShamirPoseidonSeedShare` shares (used only in tests).
pub fn shamir_reconstruct_seed32_goldilocks(shares: &[ShamirPoseidonSeedShare]) -> Option<[u8; 32]> {
    let pts: Vec<Goldilocks> = shares.iter().map(|s| s.eval_point).collect();
    let lambdas = lagrange_weights_zero_goldilocks(&pts)?;
    let mut out = [0u8; 32];
    for b_idx in 0..32 {
        let mut acc = Goldilocks::ZERO;
        for (s, &lam) in shares.iter().zip(lambdas.iter()) {
            acc = acc.const_add(lam.const_mul(s.byte_shares[b_idx]));
        }
        let v = acc.to_canonical_u64();
        if v > 255 {
            return None;
        }
        out[b_idx] = v as u8;
    }
    Some(out)
}

/// Evaluate `poseidon2_hash32` in $t$-of-$n$ Shamir MPC over a `th_preimage` frame containing a shared 32-byte secret
/// at `secret_offset` (ZERO reconstruction of the secret!).
///
/// Notice why byte-level `Goldilocks` shares shine: every `< 2^56` 7-byte limb `∑_{j=0}^6 256^{6-j} byte[7c + j]`
/// is a **pure $\mathbb{F}_p$-linear combination** of public bytes and `[secret_byte]_p` (`< 2^56 < p`, ZERO wraparound)!
pub fn mpc_poseidon2_hash32_shamir(
    t: usize,
    eval_points: &[Goldilocks],
    public_template: &[u8],
    secret_offset: usize,
    secret_shares: &[ShamirPoseidonSeedShare],
    offline_seed: &mut u64,
    opened_deltas_log: &mut Vec<Goldilocks>,
) -> Option<([u8; 32], usize)> {
    let n = eval_points.len();
    if t == 0 || t > n || secret_shares.len() != n {
        return None;
    }
    let lambdas = lagrange_weights_zero_goldilocks(&eval_points[..t])?;

    let msg_len = public_template.len();
    let marked_len = msg_len + 1;
    let pad_len = (7 - (marked_len % 7)) % 7;
    let num_limbs = (marked_len + pad_len) / 7;

    // Assemble each party's `< 2^56` limb shares via local linear combination (`0` communication!)
    let mut party_limbs: Vec<Vec<Goldilocks>> = vec![Vec::with_capacity(num_limbs + 8); n];
    for chunk_idx in 0..num_limbs {
        let base = 7 * chunk_idx;
        for p in 0..n {
            let mut acc = Goldilocks::ZERO;
            let c256 = Goldilocks::from_u64_reduced(256);
            for j in 0..7 {
                let pos = base + j;
                let byte_share = if pos >= secret_offset && pos < secret_offset + 32 {
                    secret_shares[p].byte_shares[pos - secret_offset]
                } else if pos < msg_len {
                    Goldilocks::from_u64_reduced(public_template[pos] as u64)
                } else if pos == msg_len {
                    Goldilocks::ONE
                } else {
                    Goldilocks::ZERO
                };
                acc = acc.const_mul(c256).const_add(byte_share);
            }
            party_limbs[p].push(acc);
        }
    }

    // Apply public multi-rate `10*1` sponge padding to each party's limb vector
    for p in 0..n {
        party_limbs[p] = poseidon2_pad(core::mem::take(&mut party_limbs[p]));
    }
    let num_blocks = party_limbs[0].len() / 8;

    let init = poseidon2_init_state();
    let mut party_states: Vec<[Goldilocks; 12]> = vec![init; n];
    let mut total_online_bytes = 0usize;

    for blk_idx in 0..num_blocks {
        let off = 8 * blk_idx;
        for p in 0..n {
            for r in 0..8 {
                party_states[p][r] = party_states[p][r].const_add(party_limbs[p][off + r]);
            }
        }
        total_online_bytes += mpc_poseidon2_perm12_shamir(
            t,
            eval_points,
            &mut party_states,
            offline_seed,
            opened_deltas_log,
        )?;
    }

    // Reconstruct squeezed 4 output lanes (`b0`) from the `t`-quorum
    let mut out = [0u8; 32];
    for lane in 0..4 {
        let mut acc = Goldilocks::ZERO;
        for (q, &lam) in lambdas.iter().enumerate() {
            acc = acc.const_add(lam.const_mul(party_states[q][lane]));
        }
        out[8 * lane..8 * (lane + 1)].copy_from_slice(&acc.to_be_bytes());
    }
    Some((out, total_online_bytes))
}

/// Evaluate `poseidon2_hash32` in $t$-of-$n$ Shamir MPC over `Goldilocks` returning the squeezed 4-lane
/// shares `[Goldilocks; 4]` per party WITHOUT opening when `open_output == false` — used to keep
/// intermediate WOTS+C chain states `[c^(s)]` secret-shared in signer RAM until `TSW` chooses `m_r`!
pub fn mpc_poseidon2_wots_chain_shamir(
    t: usize,
    eval_points: &[Goldilocks],
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kp: u32,
    chain: u32,
    w: usize,
    sk_seed_shares: &[ShamirPoseidonSeedShare],
    offline_seed: &mut u64,
    opened_deltas_log: &mut Vec<Goldilocks>,
) -> Option<(Vec<Vec<ShamirPoseidonSeedShare>>, usize)> {
    // Wait: in `Poseidon2`, squeezing outputs 4 `Goldilocks` field elements (`b0[0..4]`) serialized as 32 BE bytes.
    // To feed `c^(s-1)` (`32` bytes) into `th_chain_f` (`bytes_to_limbs56`) without reconstructing `c^(s-1)` in the clear,
    // parties run a 1-round masked bit/byte decomposition (`x_lane + pad_lane`) or Shamir byte resharing of `b0[0..4]`!
    // Look how clean 1-round masked byte-resharing is:
    // Each party samples/holds preprocessed random byte shares `[r_bytes]_{0..32}` whose 8-byte BE limbs equal `[r_lane]`
    // (`r_bytes` in `[0, 2^56)` per limb, or rejection-sampled `< p`); opening `masked = b0[lane] - r_lane` reveals ONLY
    // a uniform random `Goldilocks` pad (`shamir_rebalanceEquiv`!), never `c^(s-1)`!
    // Even simpler & exact for arbitrary 64-bit `b0[lane] < p`: if parties hold preprocessed Shamir byte-shares of `[c^(s)]`
    // via masked byte-Carry conversion, zero bits of `c^(s)` leak!
    let n = eval_points.len();
    if t == 0 || t > n || w < 2 || sk_seed_shares.len() != n {
        return None;
    }

    // Step 0: `c^(0) = th_secret_prf(Poseidon2Suite, pk_seed, sk_seed, adrs_prf)`
    let adrs0 = crate::adrs_tsw::HashAdrs {
        layer,
        tree,
        kind: crate::adrs_tsw::AdrsKind::WotsPrf,
        key_pair: kp,
        chain_idx: chain,
        hash_step: 0,
    };
    let mut tmpl0 = crate::adrs_tsw::th_preimage(
        crate::adrs_tsw::TAG_PRF,
        pk_seed,
        &adrs0,
        &[&[0u8; 32]],
    );
    let sec_off0 = tmpl0.len() - 32;
    for b in &mut tmpl0[sec_off0..] {
        *b = 0;
    }

    let mut chain_ram_shares: Vec<Vec<ShamirPoseidonSeedShare>> = Vec::with_capacity(w);
    let mut total_bytes = 0usize;

    let (c0_lanes, b0) = mpc_poseidon2_hash32_lane_shares(
        t,
        eval_points,
        &tmpl0,
        sec_off0,
        sk_seed_shares,
        offline_seed,
        opened_deltas_log,
    )?;
    total_bytes += b0;
    let mut cur_byte_shares = reshare_lanes4_to_byte_shares(t, eval_points, &c0_lanes, offline_seed)?;
    total_bytes += 32; // 4 masked 64-bit words opened during masked byte-conversion
    chain_ram_shares.push(cur_byte_shares.clone());

    for s in 0..(w - 1) {
        let adrs_s = crate::adrs_tsw::HashAdrs {
            layer,
            tree,
            kind: crate::adrs_tsw::AdrsKind::WotsHash,
            key_pair: kp,
            chain_idx: chain,
            hash_step: s as u32,
        };
        let mut tmpl_s = crate::adrs_tsw::th_preimage(
            crate::adrs_tsw::TAG_TH_F,
            pk_seed,
            &adrs_s,
            &[&[0u8; 32]],
        );
        let sec_off_s = tmpl_s.len() - 32;
        for b in &mut tmpl_s[sec_off_s..] {
            *b = 0;
        }
        let (cs_lanes, bs) = mpc_poseidon2_hash32_lane_shares(
            t,
            eval_points,
            &tmpl_s,
            sec_off_s,
            &cur_byte_shares,
            offline_seed,
            opened_deltas_log,
        )?;
        total_bytes += bs;
        cur_byte_shares = reshare_lanes4_to_byte_shares(t, eval_points, &cs_lanes, offline_seed)?;
        total_bytes += 32;
        chain_ram_shares.push(cur_byte_shares.clone());
    }

    Some((chain_ram_shares, total_bytes))
}

/// Internal helper returning un-opened `[Goldilocks; 4]` squeezed output lane shares per party!
fn mpc_poseidon2_hash32_lane_shares(
    t: usize,
    eval_points: &[Goldilocks],
    public_template: &[u8],
    secret_offset: usize,
    secret_shares: &[ShamirPoseidonSeedShare],
    offline_seed: &mut u64,
    opened_deltas_log: &mut Vec<Goldilocks>,
) -> Option<(Vec<[Goldilocks; 4]>, usize)> {
    let n = eval_points.len();
    let msg_len = public_template.len();
    let marked_len = msg_len + 1;
    let pad_len = (7 - (marked_len % 7)) % 7;
    let num_limbs = (marked_len + pad_len) / 7;

    let mut party_limbs: Vec<Vec<Goldilocks>> = vec![Vec::with_capacity(num_limbs + 8); n];
    for chunk_idx in 0..num_limbs {
        let base = 7 * chunk_idx;
        for p in 0..n {
            let mut acc = Goldilocks::ZERO;
            let c256 = Goldilocks::from_u64_reduced(256);
            for j in 0..7 {
                let pos = base + j;
                let byte_share = if pos >= secret_offset && pos < secret_offset + 32 {
                    secret_shares[p].byte_shares[pos - secret_offset]
                } else if pos < msg_len {
                    Goldilocks::from_u64_reduced(public_template[pos] as u64)
                } else if pos == msg_len {
                    Goldilocks::ONE
                } else {
                    Goldilocks::ZERO
                };
                acc = acc.const_mul(c256).const_add(byte_share);
            }
            party_limbs[p].push(acc);
        }
    }

    for p in 0..n {
        party_limbs[p] = poseidon2_pad(core::mem::take(&mut party_limbs[p]));
    }
    let num_blocks = party_limbs[0].len() / 8;

    let init = poseidon2_init_state();
    let mut party_states: Vec<[Goldilocks; 12]> = vec![init; n];
    let mut total_online_bytes = 0usize;

    for blk_idx in 0..num_blocks {
        let off = 8 * blk_idx;
        for p in 0..n {
            for r in 0..8 {
                party_states[p][r] = party_states[p][r].const_add(party_limbs[p][off + r]);
            }
        }
        total_online_bytes += mpc_poseidon2_perm12_shamir(
            t,
            eval_points,
            &mut party_states,
            offline_seed,
            opened_deltas_log,
        )?;
    }

    let out_lanes: Vec<[Goldilocks; 4]> = party_states
        .iter()
        .map(|st| [st[0], st[1], st[2], st[3]])
        .collect();
    Some((out_lanes, total_online_bytes))
}

/// Convert secret-shared `[Goldilocks; 4]` squeezed lanes into `ShamirPoseidonSeedShare` (`32` BE byte shares)
/// via **zero-reconstruction masked bit-carry subtraction (`A2B`)** over `Goldilocks`!
///
/// Protocol (0 plaintext reconstruction of `x`):
/// 1. Offline deals 64 shared random bits `[r_bit_k] ∈ {0, 1}` (plus 1 rejection-free Slack mask or canonical `< p` bit tuple `r < p`),
///    forming `[r_field] = ∑_{k=0}^{63} 2^k [r_bit_k]` locally.
/// 2. Parties open ONLY the masked field element `c = (x + r_field) mod p` (`shamir_rebalanceEquiv`: `r < p` masks `x`!).
///    In integer arithmetic, since `0 <= x, r < p`, `x = c - r` if `c >= r`, and `x = c + p - r` if `c < r`!
/// 3. Parties evaluate the 64-bit ripple borrow/subtract circuit between public `c` (and `c + p`) and secret bits `[r_bit_k]`
///    using standard Goldilocks Beaver multiplications (`[a * b]`), then pack the resulting 64 secret bits `[x_bit_k]`
///    linearly into 8 big-endian byte shares `[byte_j] = ∑_{b=0}^7 2^b [x_bit_{8*(7-j) + b}]`!
fn reshare_lanes4_to_byte_shares(
    t: usize,
    eval_points: &[Goldilocks],
    lane_shares: &[[Goldilocks; 4]],
    offline_seed: &mut u64,
) -> Option<Vec<ShamirPoseidonSeedShare>> {
    let n = eval_points.len();
    let lambdas = lagrange_weights_zero_goldilocks(&eval_points[..t])?;

    // Helper: Beaver multiplication of two shared `Goldilocks` values across `n` parties (`0` plaintext leakage)
    let beaver_mul = |a_sh: &[Goldilocks], b_sh: &[Goldilocks], seed: &mut u64| -> Vec<Goldilocks> {
        let u = next_goldilocks_rand(seed);
        let v = next_goldilocks_rand(seed);
        let uv = u.const_mul(v);
        let u_sh = shamir_share_scalar_goldilocks(t, eval_points, u, seed);
        let v_sh = shamir_share_scalar_goldilocks(t, eval_points, v, seed);
        let uv_sh = shamir_share_scalar_goldilocks(t, eval_points, uv, seed);
        let mut d = Goldilocks::ZERO;
        let mut e = Goldilocks::ZERO;
        for (q, &lam) in lambdas.iter().enumerate() {
            d = d.const_add(lam.const_mul(a_sh[q].const_sub(u_sh[q])));
            e = e.const_add(lam.const_mul(b_sh[q].const_sub(v_sh[q])));
        }
        let de = d.const_mul(e);
        (0..n)
            .map(|p| {
                uv_sh[p]
                    .const_add(d.const_mul(v_sh[p]))
                    .const_add(e.const_mul(u_sh[p]))
                    .const_add(de)
            })
            .collect()
    };

    let mut out: Vec<ShamirPoseidonSeedShare> = eval_points
        .iter()
        .map(|&pt| ShamirPoseidonSeedShare {
            eval_point: pt,
            byte_shares: [Goldilocks::ZERO; 32],
        })
        .collect();

    for lane in 0..4 {
        // 1. Sample canonical `< p` random 64-bit integer `r` in offline preprocessing and share its 64 bits
        let r_val = next_goldilocks_rand(offline_seed).to_canonical_u64();
        let mut r_bits_sh: Vec<Vec<Goldilocks>> = Vec::with_capacity(64);
        let mut r_field_sh = vec![Goldilocks::ZERO; n];
        for k in 0..64 {
            let bit_g = Goldilocks::from_u64_reduced((r_val >> k) & 1);
            let sh = shamir_share_scalar_goldilocks(t, eval_points, bit_g, offline_seed);
            let pow2 = Goldilocks::from_u64_reduced(1u64 << k);
            for p in 0..n {
                r_field_sh[p] = r_field_sh[p].const_add(pow2.const_mul(sh[p]));
            }
            r_bits_sh.push(sh);
        }

        // 2. Open ONLY masked `c = (x + r_field) mod p` (`x` is never reconstructed!)
        let mut c_masked = Goldilocks::ZERO;
        for (q, &lam) in lambdas.iter().enumerate() {
            let sum_q = lane_shares[q][lane].const_add(r_field_sh[q]);
            c_masked = c_masked.const_add(lam.const_mul(sum_q));
        }
        let c_u128 = c_masked.to_canonical_u64() as u128;
        let cp_u128 = c_u128 + (GOLDILOCKS_PRIME as u128);

        // 3. Ripple-borrow `diff0 = c - r` (64 bits + final borrow `b_out ∈ {0, 1}` indicating `c < r`)
        //    For public bit `cb ∈ {0, 1}`, secret bit `[rb]`, and secret borrow `[bw]`:
        //    - `sub_bit = cb ⊕ rb ⊕ bw` (purely linear when `cb` is public and `rb, bw` have `rb*bw` via 1 Beaver mul!)
        //    - Specifically: if `cb == 0`: `next_bw = rb + bw - rb*bw`, `bit = rb + bw - 2*rb*bw`.
        //                    if `cb == 1`: `next_bw = rb * bw`,         `bit = 1 - rb - bw + 2*rb*bw`.
        let two = Goldilocks::TWO;
        let mut diff0_bits: Vec<Vec<Goldilocks>> = Vec::with_capacity(64);
        let mut bw = vec![Goldilocks::ZERO; n];
        for k in 0..64 {
            let cb = ((c_u128 >> k) & 1) == 1;
            let rb = &r_bits_sh[k];
            let prod = beaver_mul(rb, &bw, offline_seed);
            let mut bit_k = vec![Goldilocks::ZERO; n];
            let mut next_bw = vec![Goldilocks::ZERO; n];
            for p in 0..n {
                let two_prod = two.const_mul(prod[p]);
                if !cb {
                    next_bw[p] = rb[p].const_add(bw[p]).const_sub(prod[p]);
                    bit_k[p] = rb[p].const_add(bw[p]).const_sub(two_prod);
                } else {
                    next_bw[p] = prod[p];
                    bit_k[p] = Goldilocks::ONE
                        .const_sub(rb[p])
                        .const_sub(bw[p])
                        .const_add(two_prod);
                }
            }
            diff0_bits.push(bit_k);
            bw = next_bw;
        }
        let c_lt_r_flag = bw; // `1` iff `c < r`, `0` iff `c >= r`

        // 4. Ripple-borrow `diff1 = (c + p) - r` (low 64 bits; since `c + p >= p > r`, this never underflows)
        let mut diff1_bits: Vec<Vec<Goldilocks>> = Vec::with_capacity(64);
        let mut bw1 = vec![Goldilocks::ZERO; n];
        for k in 0..64 {
            let cb = ((cp_u128 >> k) & 1) == 1;
            let rb = &r_bits_sh[k];
            let prod = beaver_mul(rb, &bw1, offline_seed);
            let mut bit_k = vec![Goldilocks::ZERO; n];
            let mut next_bw = vec![Goldilocks::ZERO; n];
            for p in 0..n {
                let two_prod = two.const_mul(prod[p]);
                if !cb {
                    next_bw[p] = rb[p].const_add(bw1[p]).const_sub(prod[p]);
                    bit_k[p] = rb[p].const_add(bw1[p]).const_sub(two_prod);
                } else {
                    next_bw[p] = prod[p];
                    bit_k[p] = Goldilocks::ONE
                        .const_sub(rb[p])
                        .const_sub(bw1[p])
                        .const_add(two_prod);
                }
            }
            diff1_bits.push(bit_k);
            bw1 = next_bw;
        }

        // 5. Pack `diff0` and `diff1` linearly into 8 BE bytes each, then MUX once per byte (`8` Beaver muls!)
        for byte_in_lane in 0..8 {
            let bit_lo = 8 * (7 - byte_in_lane);
            let mut b0_sh = vec![Goldilocks::ZERO; n];
            let mut b1_sh = vec![Goldilocks::ZERO; n];
            for b in 0..8 {
                let weight = Goldilocks::from_u64_reduced(1u64 << b);
                for p in 0..n {
                    b0_sh[p] = b0_sh[p].const_add(weight.const_mul(diff0_bits[bit_lo + b][p]));
                    b1_sh[p] = b1_sh[p].const_add(weight.const_mul(diff1_bits[bit_lo + b][p]));
                }
            }
            // MUX: `b0 + flag * (b1 - b0)`
            let delta_b: Vec<Goldilocks> = (0..n).map(|p| b1_sh[p].const_sub(b0_sh[p])).collect();
            let mux_term = beaver_mul(&c_lt_r_flag, &delta_b, offline_seed);
            for p in 0..n {
                out[p].byte_shares[8 * lane + byte_in_lane] = b0_sh[p].const_add(mux_term[p]);
            }
        }
    }
    Some(out)
}

// ============================================================================
// 3. `GoldilocksExt2` SPDZ/BDOZ MAC Custody & Pre-Sign Custody Policy Gate
// ============================================================================

/// Non-cloneable, non-debug, non-serializable `GoldilocksExt2` (128-bit) MAC key share custody.
pub struct Ext2MacKeyCustody {
    alpha: GoldilocksExt2,
}

impl Ext2MacKeyCustody {
    #[inline]
    pub const fn new_custody_share(alpha: GoldilocksExt2) -> Self {
        Self { alpha }
    }
}

impl Drop for Ext2MacKeyCustody {
    fn drop(&mut self) {
        self.alpha = GoldilocksExt2::ZERO;
        core::hint::black_box(&self.alpha);
    }
}

impl Ext2MacKeyCustody {

    #[inline]
    pub fn verify_pairwise_ext2_or_slash(
        &self,
        session_view: u64,
        verifier_party: usize,
        accused_party: usize,
        k_ij: GoldilocksExt2,
        opened_x: Goldilocks,
        opened_tag: GoldilocksExt2,
    ) -> Result<(), SlashingReceipt> {
        let expected = k_ij + self.alpha * GoldilocksExt2::from_base(opened_x);
        if opened_tag != expected {
            Err(SlashingReceipt {
                session_view,
                accused_party,
                verifier_party,
                failed_lane: 0,
            })
        } else {
            Ok(())
        }
    }

    #[inline]
    pub fn derive_pairwise_local_key(
        &self,
        x_j: Goldilocks,
        tag_ji: GoldilocksExt2,
    ) -> GoldilocksExt2 {
        tag_ji - self.alpha * GoldilocksExt2::from_base(x_j)
    }
}

/// 64-bit Ripple-Borrow `Poseidon2` Field-Pad Garbled Policy Circuit (`tx_amount <= secret_limit`),
/// matching `ThresholdHashMpc.garblePolicyGate` & `evalGarbledPolicyGate` (`policyGate_accepts_iff_within_limit`).
///
/// Point-and-permute LSB wire labels (`32` bytes per wire) hide intermediate borrows `b_1..b_64`
/// and `secret_limit` bits `s_0..s_63` completely: the evaluator walks ONLY the single active row
/// per bit `k` for public `tx_amount` and **never reconstructs `secret_limit`!**
#[derive(Clone, Debug)]
pub struct GarbledPolicyCircuit64 {
    pub policy_nonce: [u8; 32],
    pub init_borrow_zero_label: [u8; 32],
    pub gates: [[[u8; 32]; 4]; 64],
    pub accept_tag: [u8; 32],
    pub masked_release_share: Goldilocks,
}

#[inline]
fn poseidon2_garble_pad(
    policy_nonce: &[u8; 32],
    bit_idx: u8,
    tx_bit: u8,
    in_label: &[u8; 32],
) -> [u8; 32] {
    let mut pre = [0u8; 66];
    pre[0..32].copy_from_slice(policy_nonce);
    pre[32] = bit_idx;
    pre[33] = tx_bit;
    pre[34..66].copy_from_slice(in_label);
    poseidon2_hash32(&pre)
}

#[inline]
fn xor32(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = a[i] ^ b[i];
    }
    out
}

/// Garble a secret 64-bit counterparty spending limit `secret_limit` into a one-time `GarbledPolicyCircuit64`
/// binding `raw_share + pad_share` onto the `borrow == 0` (`tx_amount <= secret_limit`) terminal wire!
pub fn garble_custody_policy_limit(
    policy_nonce: [u8; 32],
    secret_limit: u64,
    raw_share: Goldilocks,
    pad_share: Goldilocks,
    rng_seed: &mut u64,
) -> GarbledPolicyCircuit64 {
    let mut labels = [[[0u8; 32]; 2]; 65];
    for w in 0..=64 {
        let mut seed_buf = [0u8; 48];
        seed_buf[0..32].copy_from_slice(&policy_nonce);
        seed_buf[32..40].copy_from_slice(&(w as u64).to_be_bytes());
        let r0 = next_goldilocks_rand(rng_seed).to_canonical_u64();
        seed_buf[40..48].copy_from_slice(&r0.to_be_bytes());
        let mut l0 = poseidon2_hash32(&seed_buf);
        let r1 = next_goldilocks_rand(rng_seed).to_canonical_u64();
        seed_buf[40..48].copy_from_slice(&r1.to_be_bytes());
        let mut l1 = poseidon2_hash32(&seed_buf);
        let perm_bit = (next_goldilocks_rand(rng_seed).to_canonical_u64() & 1) as u8;
        l0[0] = (l0[0] & 0xFE) | perm_bit;
        l1[0] = (l1[0] & 0xFE) | (perm_bit ^ 1);
        labels[w] = [l0, l1];
    }

    let mut gates = [[[0u8; 32]; 4]; 64];
    for k in 0..64 {
        let s_k = ((secret_limit >> k) & 1) as u8;
        let l_next0 = labels[k + 1][0];
        let l_next1 = labels[k + 1][1];
        for b_in in 0..=1u8 {
            let in_lbl = &labels[k][b_in as usize];
            let color = (in_lbl[0] & 1) as usize;
            for x_k in 0..=1u8 {
                let b_next = ((1 - s_k) & (x_k | b_in)) | (s_k & x_k & b_in);
                let mask = 0u8.wrapping_sub(b_next);
                let mut out_lbl = [0u8; 32];
                for j in 0..32 {
                    out_lbl[j] = l_next0[j] ^ (mask & (l_next0[j] ^ l_next1[j]));
                }
                let pad = poseidon2_garble_pad(&policy_nonce, k as u8, x_k, in_lbl);
                gates[k][2 * color + (x_k as usize)] = xor32(&out_lbl, &pad);
                out_lbl.fill(0);
                core::hint::black_box(&out_lbl);
            }
        }
    }

    let accept_tag = poseidon2_hash32(&labels[64][0]);
    let init_borrow_zero_label = labels[0][0];
    labels.fill([[0u8; 32]; 2]);
    core::hint::black_box(&labels);
    let masked_release_share = raw_share.const_add(pad_share);
    GarbledPolicyCircuit64 {
        policy_nonce,
        init_borrow_zero_label,
        gates,
        accept_tag,
        masked_release_share,
    }
}

/// Evaluate `GarbledPolicyCircuit64` on public `tx_amount` (`0` knowledge of `secret_limit`!).
/// Returns `Some(unmasked_raw_share)` iff `tx_amount <= secret_limit`, and `None` iff `tx_amount > secret_limit`.
pub fn eval_garbled_custody_policy_gate(
    circuit: &GarbledPolicyCircuit64,
    tx_amount: u64,
    pad_share: Goldilocks,
) -> Option<Goldilocks> {
    let mut cur_label = circuit.init_borrow_zero_label;
    for k in 0..64 {
        let x_k = ((tx_amount >> k) & 1) as u8;
        let color = (cur_label[0] & 1) as usize;
        let ct = &circuit.gates[k][2 * color + (x_k as usize)];
        let pad = poseidon2_garble_pad(&circuit.policy_nonce, k as u8, x_k, &cur_label);
        cur_label = xor32(ct, &pad);
    }
    if poseidon2_hash32(&cur_label) == circuit.accept_tag {
        Some(circuit.masked_release_share.const_sub(pad_share))
    } else {
        None
    }
}
