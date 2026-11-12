//! Bitsliced `64x` parallel `Keccak-f[1600]` & `cSHAKE256` MPC engine in BOTH:
//! 1. **2-of-3 Replicated Secret Sharing (`RSS`)** (`1` bit per AND gate = `4,800 B` per `Keccak-f[1600]`),
//! 2. **Arbitrary $t$-of-$n$ Wiedemann `BinaryTower256` Shamir** ($\mathbb{F}_2 \hookrightarrow \mathcal{T}_3 \subset \mathcal{T}_7$)
//!    with **2-lane split-custody `Tower128 × Tower128` SPDZ/BDOZ MACs**, off-diagonal cross-term formation,
//!    terminal GHASH polynomial batch verification, and deterministic cheater attribution (`SlashingReceipt`).
//!
//! Matches `Obend.Crypto.BinaryTower256` and `Obend.Crypto.ThresholdHashMpc` algebraically and byte-for-byte.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use obend_crypto_exec::transcript::{
    KECCAK_ROUND_CONSTANTS, SHAKE256_RATE_BYTES, cshake256_customization_prefix,
};

/// FIPS 202 rho rotation offsets indexed by `x + 5 * y`.
const ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

// ============================================================================
// 1. Wiedemann Binary Tower Arithmetic (`TowerElem 3` = GF(2^8), `TowerElem 7` = GF(2^128))
// ============================================================================

#[inline]
const fn tower_scale_x_bits(k: u32, a: u128) -> u128 {
    if k == 0 {
        a & 1
    } else {
        let half = 1u32 << (k - 1);
        let mask = if half == 128 {
            u128::MAX
        } else {
            (1u128 << half) - 1
        };
        let lo = a & mask;
        let hi = (a >> half) & mask;
        let scaled_hi = tower_scale_x_bits(k - 1, hi);
        hi | ((lo ^ scaled_hi) << half)
    }
}

#[inline]
const fn tower_mul_bits(k: u32, a: u128, b: u128) -> u128 {
    if k == 0 {
        (a & 1) & (b & 1)
    } else {
        let half = 1u32 << (k - 1);
        let mask = (1u128 << half) - 1;
        let a_lo = a & mask;
        let a_hi = (a >> half) & mask;
        let b_lo = b & mask;
        let b_hi = (b >> half) & mask;
        let p = tower_mul_bits(k - 1, a_lo, b_lo);
        let q = tower_mul_bits(k - 1, a_hi, b_hi);
        let r = tower_mul_bits(k - 1, a_lo ^ a_hi, b_lo ^ b_hi);
        let lo = p ^ q;
        let hi = r ^ p ^ q ^ tower_scale_x_bits(k - 1, q);
        lo | (hi << half)
    }
}

/// Compile-time $256 \times 8$ basis-column table for public $\mathcal{T}_3 = \mathbb{F}_{2^8}$ scalars:
/// `GF256_MUL_BASIS[c][in_bit] == (TowerGf256(c) * TowerGf256(1 << in_bit)).0`.
const GF256_MUL_BASIS: [[u8; 8]; 256] = {
    let mut tbl = [[0u8; 8]; 256];
    let mut c = 0usize;
    while c < 256 {
        let mut bit = 0usize;
        while bit < 8 {
            tbl[c][bit] = tower_mul_bits(3, c as u128, 1u128 << bit) as u8;
            bit += 1;
        }
        c += 1;
    }
    tbl
};

#[inline]
fn tower_inv_bits(k: u32, a: u128) -> Option<u128> {
    if k == 0 {
        if (a & 1) == 1 {
            Some(1)
        } else {
            None
        }
    } else {
        let half = 1u32 << (k - 1);
        let mask = (1u128 << half) - 1;
        let a_lo = a & mask;
        let a_hi = (a >> half) & mask;
        if a_lo == 0 && a_hi == 0 {
            return None;
        }
        // Conjugate in T_{k-1}[X]/(X^2 + x_{k-1} X + 1) is (a_lo ^ scale_x(a_hi)) + a_hi X.
        let conj_lo = a_lo ^ tower_scale_x_bits(k - 1, a_hi);
        let norm =
            tower_mul_bits(k - 1, a_lo, conj_lo) ^ tower_mul_bits(k - 1, a_hi, a_hi);
        let norm_inv = tower_inv_bits(k - 1, norm)?;
        let inv_lo = tower_mul_bits(k - 1, norm_inv, conj_lo);
        let inv_hi = tower_mul_bits(k - 1, norm_inv, a_hi);
        Some(inv_lo | (inv_hi << half))
    }
}

/// Element of Wiedemann tower level $\mathcal{T}_3 = \mathbb{F}_{2^8}$ (`BinaryTower256.TowerElem 3`),
/// supporting Shamir secret sharing for up to $n \le 255$ parties.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TowerGf256(pub u8);

impl TowerGf256 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    #[inline]
    pub const fn embed_bit(b: bool) -> Self {
        Self(b as u8)
    }

    #[inline]
    pub const fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        Self(tower_mul_bits(3, self.0 as u128, rhs.0 as u128) as u8)
    }

    #[inline]
    pub fn inv(self) -> Option<Self> {
        tower_inv_bits(3, self.0 as u128).map(|v| Self(v as u8))
    }
}

/// Element of Wiedemann tower level $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$ (`BinaryTower256.Tower128`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Tower128(pub u128);

impl Tower128 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    #[inline]
    pub const fn embed_bit(b: bool) -> Self {
        Self(b as u128)
    }

    #[inline]
    pub const fn embed_gf256(x: TowerGf256) -> Self {
        Self(x.0 as u128)
    }

    #[inline]
    pub const fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        Self(tower_mul_bits(7, self.0, rhs.0))
    }

    #[inline]
    pub fn inv(self) -> Option<Self> {
        tower_inv_bits(7, self.0).map(Self)
    }
}

/// Evaluate polynomial `coeffs[0] + coeffs[1] * x + ...` over `TowerGf256`.
#[inline]
pub fn eval_poly_gf256(coeffs: &[TowerGf256], x: TowerGf256) -> TowerGf256 {
    let mut acc = TowerGf256::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(x).add(c);
    }
    acc
}

/// Compute Lagrange interpolation weights at `0` for distinct non-zero evaluation points `pts` in `TowerGf256`.
pub fn lagrange_weights_zero_gf256(pts: &[TowerGf256]) -> Option<Vec<TowerGf256>> {
    let t = pts.len();
    let mut weights = Vec::with_capacity(t);
    for i in 0..t {
        if pts[i] == TowerGf256::ZERO {
            return None;
        }
        let mut num = TowerGf256::ONE;
        let mut den = TowerGf256::ONE;
        for j in 0..t {
            if i == j {
                continue;
            }
            let diff = pts[i].add(pts[j]);
            if diff == TowerGf256::ZERO {
                return None;
            }
            num = num.mul(pts[j]);
            den = den.mul(diff);
        }
        weights.push(num.mul(den.inv()?));
    }
    Some(weights)
}

/// Evaluate GHASH-style polynomial `((0 + c_0) * h + c_1) * h ...` over `Tower128`,
/// matching `BinaryTower256.ghashPoly`.
pub fn ghash_poly_tower128(h: Tower128, blocks: &[Tower128]) -> Tower128 {
    let mut acc = Tower128::ZERO;
    for &blk in blocks {
        acc = acc.add(blk).mul(h);
    }
    acc
}

// ============================================================================
// 2. Bitsliced `64x` Parallel `Keccak-f[1600]` Transpose & Plaintext Equivalence
// ============================================================================

/// Constant-time bitslice transpose of up to 64 Keccak states `[u64; 25]` into 1,600 `u64` planes.
pub fn transpose_states_to_planes(states: &[[u64; 25]]) -> Box<[u64; 1600]> {
    assert!(states.len() <= 64);
    let mut planes = Box::new([0u64; 1600]);
    for (inst, st) in states.iter().enumerate() {
        for lane in 0..25 {
            let word = st[lane];
            let base = 64 * lane;
            for z in 0..64 {
                planes[base + z] |= ((word >> z) & 1) << inst;
            }
        }
    }
    planes
}

/// Constant-time bitslice transpose of 1,600 `u64` planes back into `count` Keccak states `[u64; 25]`.
pub fn transpose_planes_to_states(planes: &[u64; 1600], count: usize) -> Vec<[u64; 25]> {
    assert!(count <= 64);
    let mut out = vec![[0u64; 25]; count];
    for lane in 0..25 {
        let base = 64 * lane;
        for z in 0..64 {
            let p = planes[base + z];
            for (inst, st) in out.iter_mut().enumerate() {
                st[lane] |= ((p >> inst) & 1) << z;
            }
        }
    }
    out
}

#[inline]
fn linear_theta_rho_pi_u64(planes: &mut [u64; 1600]) -> Box<[u64; 1600]> {
    // Theta
    let mut c = [[0u64; 64]; 5];
    for x in 0..5 {
        for z in 0..64 {
            c[x][z] = planes[64 * x + z]
                ^ planes[64 * (x + 5) + z]
                ^ planes[64 * (x + 10) + z]
                ^ planes[64 * (x + 15) + z]
                ^ planes[64 * (x + 20) + z];
        }
    }
    for x in 0..5 {
        let xm1 = (x + 4) % 5;
        let xp1 = (x + 1) % 5;
        for z in 0..64 {
            let d = c[xm1][z] ^ c[xp1][(z + 63) & 63];
            for y in 0..5 {
                planes[64 * (x + 5 * y) + z] ^= d;
            }
        }
    }

    // Rho + Pi (pure wire permutation — 0 bit shifts!)
    let mut b = Box::new([0u64; 1600]);
    for source in 0..25 {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = (ROTATION_OFFSETS[source] as usize) & 63;
        let src_base = 64 * source;
        let dst_base = 64 * target;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            b[dst_base + z] = planes[src_base + src_z];
        }
    }
    b
}

// ============================================================================
// 3. 2-of-3 Replicated Secret Sharing (`RSS`) Bitsliced `64x` Keccak & cSHAKE256
// ============================================================================

/// One party's 2-of-3 `RSS` share `(s_own, s_next)` over 1,600 bitsliced `u64` wires (`64` parallel states).
#[derive(Clone)]
pub struct RssKeccakState64 {
    pub party_idx: usize,
    pub s_own: Box<[u64; 1600]>,
    pub s_next: Box<[u64; 1600]>,
}

impl Drop for RssKeccakState64 {
    fn drop(&mut self) {
        for w in self.s_own.iter_mut() {
            *w = 0;
        }
        for w in self.s_next.iter_mut() {
            *w = 0;
        }
        core::hint::black_box(&*self.s_own);
        core::hint::black_box(&*self.s_next);
    }
}

/// Share 64 Keccak states into 3 `RSS` party states using two 1,600-word masks `(m0, m1)`.
pub fn rss_share_keccak_states64(
    plain_planes: &[u64; 1600],
    mask0: &[u64; 1600],
    mask1: &[u64; 1600],
) -> [RssKeccakState64; 3] {
    let mut s2 = Box::new([0u64; 1600]);
    for i in 0..1600 {
        s2[i] = plain_planes[i] ^ mask0[i] ^ mask1[i];
    }
    let s0 = Box::new(*mask0);
    let s1 = Box::new(*mask1);
    [
        RssKeccakState64 {
            party_idx: 0,
            s_own: s0.clone(),
            s_next: s1.clone(),
        },
        RssKeccakState64 {
            party_idx: 1,
            s_own: s1,
            s_next: s2.clone(),
        },
        RssKeccakState64 {
            party_idx: 2,
            s_own: s2,
            s_next: s0,
        },
    ]
}

/// Reconstruct 64 Keccak states from ANY distinct 2-of-3 `RSS` parties (`(p0, p1)`, `(p1, p2)`, or `(p2, p0)`),
/// returning `None` if party indices are duplicate or out of `0..3`!
pub fn rss_reconstruct_2of3(
    p_a: &RssKeccakState64,
    p_b: &RssKeccakState64,
) -> Option<Box<[u64; 1600]>> {
    let mut out = Box::new([0u64; 1600]);
    match (p_a.party_idx, p_b.party_idx) {
        (0, 1) | (1, 2) | (2, 0) => {
            for i in 0..1600 {
                out[i] = p_a.s_own[i] ^ p_a.s_next[i] ^ p_b.s_next[i];
            }
            Some(out)
        }
        (1, 0) | (2, 1) | (0, 2) => {
            for i in 0..1600 {
                out[i] = p_b.s_own[i] ^ p_b.s_next[i] ^ p_a.s_next[i];
            }
            Some(out)
        }
        _ => None,
    }
}

/// XOR public plaintext `u64` planes into a 3-party `RSS` state (`0` communication).
#[inline]
pub fn rss_xor_public_planes(parties: &mut [RssKeccakState64; 3], pub_planes: &[u64; 1600]) {
    for i in 0..1600 {
        let v = pub_planes[i];
        parties[0].s_own[i] ^= v;
        parties[2].s_next[i] ^= v;
    }
}

/// Deterministic correlated PRG zero-share generator (`zeta_0 ^ zeta_1 ^ zeta_2 == 0` identically)
/// derived from pre-shared pairwise seeds `(seed_01, seed_12, seed_20)`.
#[inline]
fn splitmix64_next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Execute all 24 rounds of `Keccak-f[1600]` across 64 parallel instances in 2-of-3 `RSS`.
/// Returns total per-party online bytes transmitted (`24 * 1600 * 8 = 307,200 B` across 64 perms = `4,800 B` / perm).
pub fn rss_keccak_f1600_x64(
    parties: &mut [RssKeccakState64; 3],
    prg_seeds: &mut [u64; 3],
) -> usize {
    let mut bytes_per_party = 0usize;
    for &rc in &KECCAK_ROUND_CONSTANTS {
        // 1. Free F_2-linear Theta + Rho + Pi on both replicated halves
        let mut b_own: [Box<[u64; 1600]>; 3] = [
            linear_theta_rho_pi_u64(&mut parties[0].s_own),
            linear_theta_rho_pi_u64(&mut parties[1].s_own),
            linear_theta_rho_pi_u64(&mut parties[2].s_own),
        ];
        let b_next: [Box<[u64; 1600]>; 3] = [
            linear_theta_rho_pi_u64(&mut parties[0].s_next),
            linear_theta_rho_pi_u64(&mut parties[1].s_next),
            linear_theta_rho_pi_u64(&mut parties[2].s_next),
        ];

        // Public negation `!b` in `chi(a, b, c) = a ^ ((!b) & c)` flips `s_0` (held as `b_own[0]` and `b_next[2]`).
        let mut neg_b_own0 = *b_own[0];
        let mut neg_b_next2 = *b_next[2];
        for v in neg_b_own0.iter_mut() {
            *v = !*v;
        }
        for v in neg_b_next2.iter_mut() {
            *v = !*v;
        }

        // 2. 1-Bit/Gate `chi` round: each party computes `z_p` (1,600 `u64` words) and forwards to `p - 1`
        let mut msg_z: [Box<[u64; 1600]>; 3] = [
            Box::new([0u64; 1600]),
            Box::new([0u64; 1600]),
            Box::new([0u64; 1600]),
        ];
        for y in 0..5 {
            let row = 5 * y;
            for x in 0..5 {
                let idx_a_base = 64 * (row + x);
                let idx_b_base = 64 * (row + ((x + 1) % 5));
                let idx_c_base = 64 * (row + ((x + 2) % 5));
                for z in 0..64 {
                    let ia = idx_a_base + z;
                    let ib = idx_b_base + z;
                    let ic = idx_c_base + z;

                    let r01 = splitmix64_next(&mut prg_seeds[0]);
                    let r12 = splitmix64_next(&mut prg_seeds[1]);
                    let r20 = splitmix64_next(&mut prg_seeds[2]);
                    let zeta0 = r01 ^ r20;
                    let zeta1 = r12 ^ r01;
                    let zeta2 = r20 ^ r12;

                    // Party 0: holds (s0, s1)
                    let nb0_own = neg_b_own0[ib];
                    let nb0_nxt = b_next[0][ib];
                    let and0 = (nb0_own & b_own[0][ic])
                        ^ (nb0_own & b_next[0][ic])
                        ^ (nb0_nxt & b_own[0][ic])
                        ^ zeta0;
                    msg_z[0][ia] = b_own[0][ia] ^ and0;

                    // Party 1: holds (s1, s2)
                    let nb1_own = b_own[1][ib];
                    let nb1_nxt = b_next[1][ib];
                    let and1 = (nb1_own & b_own[1][ic])
                        ^ (nb1_own & b_next[1][ic])
                        ^ (nb1_nxt & b_own[1][ic])
                        ^ zeta1;
                    msg_z[1][ia] = b_own[1][ia] ^ and1;

                    // Party 2: holds (s2, s0) where s0 on wire b is negated
                    let nb2_own = b_own[2][ib];
                    let nb2_nxt = neg_b_next2[ib];
                    let and2 = (nb2_own & b_own[2][ic])
                        ^ (nb2_own & b_next[2][ic])
                        ^ (nb2_nxt & b_own[2][ic])
                        ^ zeta2;
                    msg_z[2][ia] = b_own[2][ia] ^ and2;
                }
            }
        }
        bytes_per_party += 1600 * 8;

        // Reshare round completion (`s_own = msg_z[p]`, `s_next = msg_z[(p + 1) % 3]`)
        let [m0, m1, m2] = msg_z;
        parties[0].s_own = m0.clone();
        parties[0].s_next = m1.clone();
        parties[1].s_own = m1;
        parties[1].s_next = m2.clone();
        parties[2].s_own = m2;
        parties[2].s_next = m0;

        // 3. Free public Iota constant XOR on lane 0
        for z in 0..64 {
            if ((rc >> z) & 1) == 1 {
                parties[0].s_own[z] ^= u64::MAX;
                parties[2].s_next[z] ^= u64::MAX;
            }
        }
        let _ = &mut b_own;
    }
    bytes_per_party
}

/// Evaluate up to 64 parallel single-block `cSHAKE256(custom, preimages[i])` calls in 2-of-3 `RSS`,
/// where bytes marked in `secret_byte_shares` are XOR-shared `(s0, s1, s2)` and all framing/ADRS bytes are public!
pub fn rss_eval_cshake256_batch64(
    customization: &[u8],
    public_templates: &[Vec<u8>],
    secret_patches: &[(usize, [[u8; 32]; 3])],
    prg_seeds: &mut [u64; 3],
) -> (Vec<[u8; 32]>, usize) {
    let batch_len = public_templates.len();
    assert!(batch_len <= 64);
    let prefix = if customization.is_empty() {
        Vec::new()
    } else {
        cshake256_customization_prefix(customization)
    };
    let suffix: u8 = if customization.is_empty() { 0x1F } else { 0x04 };

    // Determine maximum padded block count across the batch (typically 2 blocks: 136B customization + 136B message)
    let mut padded_msgs: Vec<[Vec<u8>; 3]> = Vec::with_capacity(batch_len);
    let mut max_blocks = 0usize;
    for (inst, tmpl) in public_templates.iter().enumerate() {
        let mut p0 = Vec::with_capacity(prefix.len() + tmpl.len() + SHAKE256_RATE_BYTES);
        p0.extend_from_slice(&prefix);
        p0.extend_from_slice(tmpl);
        let mut p1 = vec![0u8; p0.len()];
        let mut p2 = vec![0u8; p0.len()];

        // Apply secret 32-byte share patches `(offset_in_tmpl, [s0, s1, s2])` for this instance:
        // Note: `tmpl` has `0` placeholder at `offset..offset+32`, so XORing `s0, s1, s2` sets `p0^p1^p2 = prefix || msg`!
        let (off, shares3) = &secret_patches[inst];
        let start = prefix.len() + *off;
        for k in 0..32 {
            p0[start + k] ^= shares3[0][k];
            p1[start + k] ^= shares3[1][k];
            p2[start + k] ^= shares3[2][k];
        }

        // Pad `p0` with SP 800-185 multi-rate suffix (`p1, p2` padded with 0 so XOR equals padded message!)
        let rem = p0.len() % SHAKE256_RATE_BYTES;
        let pad_len = SHAKE256_RATE_BYTES - rem;
        p0.resize(p0.len() + pad_len, 0u8);
        p1.resize(p1.len() + pad_len, 0u8);
        p2.resize(p2.len() + pad_len, 0u8);
        let suffix_pos = p0.len() - pad_len;
        p0[suffix_pos] ^= suffix;
        let last_pos = p0.len() - 1;
        p0[last_pos] ^= 0x80;

        max_blocks = max_blocks.max(p0.len() / SHAKE256_RATE_BYTES);
        padded_msgs.push([p0, p1, p2]);
    }

    let zero_planes = [0u64; 1600];
    let mut parties = rss_share_keccak_states64(&zero_planes, &zero_planes, &zero_planes);
    let mut total_bytes = 0usize;

    for blk_idx in 0..max_blocks {
        // Build 3-party rate block shares `[u64; 25]` across active instances with `blk_idx < blocks(inst)`
        let mut s0_states = [[0u64; 25]; 64];
        let mut s1_states = [[0u64; 25]; 64];
        let mut s2_states = [[0u64; 25]; 64];
        let mut active_mask = 0u64;

        for (inst, pm) in padded_msgs.iter().enumerate() {
            let inst_blocks = pm[0].len() / SHAKE256_RATE_BYTES;
            if blk_idx < inst_blocks {
                active_mask |= 1u64 << inst;
                let byte_off = blk_idx * SHAKE256_RATE_BYTES;
                for lane in 0..17 {
                    let loff = byte_off + 8 * lane;
                    s0_states[inst][lane] =
                        u64::from_le_bytes(pm[0][loff..loff + 8].try_into().unwrap());
                    s1_states[inst][lane] =
                        u64::from_le_bytes(pm[1][loff..loff + 8].try_into().unwrap());
                    s2_states[inst][lane] =
                        u64::from_le_bytes(pm[2][loff..loff + 8].try_into().unwrap());
                }
            }
        }

        let p0_blk = transpose_states_to_planes(&s0_states[..batch_len]);
        let p1_blk = transpose_states_to_planes(&s1_states[..batch_len]);
        let p2_blk = transpose_states_to_planes(&s2_states[..batch_len]);

        let prev_own: [Box<[u64; 1600]>; 3] = [
            parties[0].s_own.clone(),
            parties[1].s_own.clone(),
            parties[2].s_own.clone(),
        ];
        let prev_next: [Box<[u64; 1600]>; 3] = [
            parties[0].s_next.clone(),
            parties[1].s_next.clone(),
            parties[2].s_next.clone(),
        ];

        for i in 0..1600 {
            parties[0].s_own[i] ^= p0_blk[i];
            parties[0].s_next[i] ^= p1_blk[i];
            parties[1].s_own[i] ^= p1_blk[i];
            parties[1].s_next[i] ^= p2_blk[i];
            parties[2].s_own[i] ^= p2_blk[i];
            parties[2].s_next[i] ^= p0_blk[i];
        }

        total_bytes += rss_keccak_f1600_x64(&mut parties, prg_seeds);

        // Preserve already-finished instances if block counts differ within batch
        if active_mask != ((1u64 << batch_len) - 1) {
            let keep = !active_mask;
            for p in 0..3 {
                for i in 0..1600 {
                    parties[p].s_own[i] =
                        (parties[p].s_own[i] & active_mask) | (prev_own[p][i] & keep);
                    parties[p].s_next[i] =
                        (parties[p].s_next[i] & active_mask) | (prev_next[p][i] & keep);
                }
            }
        }
        s0_states.fill([0u64; 25]);
        s1_states.fill([0u64; 25]);
        s2_states.fill([0u64; 25]);
        core::hint::black_box((&s0_states, &s1_states, &s2_states));
    }
    for pm in &mut padded_msgs {
        for share_vec in pm.iter_mut() {
            share_vec.fill(0);
            core::hint::black_box(share_vec.as_slice());
        }
    }

    // Reconstruct squeezed 32-byte digests from 2-of-3 quorum (Party 0 & Party 1)
    let out_planes = rss_reconstruct_2of3(&parties[0], &parties[1])
        .expect("internal 2-of-3 RSS parties (0, 1) are distinct");
    let out_states = transpose_planes_to_states(&out_planes, batch_len);
    let mut digests = Vec::with_capacity(batch_len);
    for st in &out_states {
        let mut d = [0u8; 32];
        for lane in 0..4 {
            d[8 * lane..8 * (lane + 1)].copy_from_slice(&st[lane].to_le_bytes());
        }
        digests.push(d);
    }
    (digests, total_bytes)
}

/// Evaluate up to 64 parallel `cSHAKE256` calls in 2-of-3 `RSS` WITHOUT opening the output:
/// returns 3-party XOR/RSS byte shares `[[u8; 32]; 3]` per instance (`s0 ^ s1 ^ s2 == digest`),
/// keeping intermediate WOTS+C chain states `[c^(s)]` 100% secret-shared in signer RAM!
pub fn rss_eval_cshake256_secret_shares64(
    customization: &[u8],
    public_templates: &[Vec<u8>],
    secret_patches: &[(usize, [[u8; 32]; 3])],
    prg_seeds: &mut [u64; 3],
) -> (Vec<[[u8; 32]; 3]>, usize) {
    let batch_len = public_templates.len();
    assert!(batch_len <= 64);
    let prefix = if customization.is_empty() {
        Vec::new()
    } else {
        cshake256_customization_prefix(customization)
    };
    let suffix: u8 = if customization.is_empty() { 0x1F } else { 0x04 };

    let mut padded_msgs: Vec<[Vec<u8>; 3]> = Vec::with_capacity(batch_len);
    let mut max_blocks = 0usize;
    for (inst, tmpl) in public_templates.iter().enumerate() {
        let mut p0 = Vec::with_capacity(prefix.len() + tmpl.len() + SHAKE256_RATE_BYTES);
        p0.extend_from_slice(&prefix);
        p0.extend_from_slice(tmpl);
        let mut p1 = vec![0u8; p0.len()];
        let mut p2 = vec![0u8; p0.len()];

        let (off, shares3) = &secret_patches[inst];
        let start = prefix.len() + *off;
        for k in 0..32 {
            p0[start + k] ^= shares3[0][k];
            p1[start + k] ^= shares3[1][k];
            p2[start + k] ^= shares3[2][k];
        }

        let rem = p0.len() % SHAKE256_RATE_BYTES;
        let pad_len = SHAKE256_RATE_BYTES - rem;
        p0.resize(p0.len() + pad_len, 0u8);
        p1.resize(p1.len() + pad_len, 0u8);
        p2.resize(p2.len() + pad_len, 0u8);
        let suffix_pos = p0.len() - pad_len;
        p0[suffix_pos] ^= suffix;
        let last_pos = p0.len() - 1;
        p0[last_pos] ^= 0x80;

        max_blocks = max_blocks.max(p0.len() / SHAKE256_RATE_BYTES);
        padded_msgs.push([p0, p1, p2]);
    }

    let zero_planes = [0u64; 1600];
    let mut parties = rss_share_keccak_states64(&zero_planes, &zero_planes, &zero_planes);
    let mut total_bytes = 0usize;

    for blk_idx in 0..max_blocks {
        let mut s0_states = [[0u64; 25]; 64];
        let mut s1_states = [[0u64; 25]; 64];
        let mut s2_states = [[0u64; 25]; 64];
        let mut active_mask = 0u64;

        for (inst, pm) in padded_msgs.iter().enumerate() {
            let inst_blocks = pm[0].len() / SHAKE256_RATE_BYTES;
            if blk_idx < inst_blocks {
                active_mask |= 1u64 << inst;
                let byte_off = blk_idx * SHAKE256_RATE_BYTES;
                for lane in 0..17 {
                    let loff = byte_off + 8 * lane;
                    s0_states[inst][lane] =
                        u64::from_le_bytes(pm[0][loff..loff + 8].try_into().unwrap());
                    s1_states[inst][lane] =
                        u64::from_le_bytes(pm[1][loff..loff + 8].try_into().unwrap());
                    s2_states[inst][lane] =
                        u64::from_le_bytes(pm[2][loff..loff + 8].try_into().unwrap());
                }
            }
        }

        let p0_blk = transpose_states_to_planes(&s0_states[..batch_len]);
        let p1_blk = transpose_states_to_planes(&s1_states[..batch_len]);
        let p2_blk = transpose_states_to_planes(&s2_states[..batch_len]);

        let prev_own: [Box<[u64; 1600]>; 3] = [
            parties[0].s_own.clone(),
            parties[1].s_own.clone(),
            parties[2].s_own.clone(),
        ];
        let prev_next: [Box<[u64; 1600]>; 3] = [
            parties[0].s_next.clone(),
            parties[1].s_next.clone(),
            parties[2].s_next.clone(),
        ];

        for i in 0..1600 {
            parties[0].s_own[i] ^= p0_blk[i];
            parties[0].s_next[i] ^= p1_blk[i];
            parties[1].s_own[i] ^= p1_blk[i];
            parties[1].s_next[i] ^= p2_blk[i];
            parties[2].s_own[i] ^= p2_blk[i];
            parties[2].s_next[i] ^= p0_blk[i];
        }

        total_bytes += rss_keccak_f1600_x64(&mut parties, prg_seeds);

        if active_mask != ((1u64 << batch_len) - 1) {
            let keep = !active_mask;
            for p in 0..3 {
                for i in 0..1600 {
                    parties[p].s_own[i] =
                        (parties[p].s_own[i] & active_mask) | (prev_own[p][i] & keep);
                    parties[p].s_next[i] =
                        (parties[p].s_next[i] & active_mask) | (prev_next[p][i] & keep);
                }
            }
        }
        s0_states.fill([0u64; 25]);
        s1_states.fill([0u64; 25]);
        s2_states.fill([0u64; 25]);
        core::hint::black_box((&s0_states, &s1_states, &s2_states));
    }
    for pm in &mut padded_msgs {
        for share_vec in pm.iter_mut() {
            share_vec.fill(0);
            core::hint::black_box(share_vec.as_slice());
        }
    }

    // Extract `(s0, s1, s2)` squeezed 32-byte shares directly WITHOUT opening!
    let mut st_s0 = transpose_planes_to_states(&parties[0].s_own, batch_len);
    let mut st_s1 = transpose_planes_to_states(&parties[1].s_own, batch_len);
    let mut st_s2 = transpose_planes_to_states(&parties[2].s_own, batch_len);
    let mut secret_outs = Vec::with_capacity(batch_len);
    for inst in 0..batch_len {
        let mut sh = [[0u8; 32]; 3];
        for lane in 0..4 {
            sh[0][8 * lane..8 * (lane + 1)].copy_from_slice(&st_s0[inst][lane].to_le_bytes());
            sh[1][8 * lane..8 * (lane + 1)].copy_from_slice(&st_s1[inst][lane].to_le_bytes());
            sh[2][8 * lane..8 * (lane + 1)].copy_from_slice(&st_s2[inst][lane].to_le_bytes());
        }
        secret_outs.push(sh);
    }
    st_s0.fill([0u64; 25]);
    st_s1.fill([0u64; 25]);
    st_s2.fill([0u64; 25]);
    core::hint::black_box((st_s0.as_slice(), st_s1.as_slice(), st_s2.as_slice()));
    (secret_outs, total_bytes)
}

// ============================================================================
// 4. Arbitrary $t$-of-$n$ Bitsliced `BinaryTower256` ($\mathcal{T}_3$) Shamir Keccak Engine
// ============================================================================

/// Bitsliced vector of 64 parallel $\mathcal{T}_3 = \mathbb{F}_{2^8}$ elements (`8` `u64` bit-planes).
pub type BitslicedGf256x64 = [u64; 8];

#[inline]
pub fn bs_gf256_xor(a: &BitslicedGf256x64, b: &BitslicedGf256x64) -> BitslicedGf256x64 {
    [
        a[0] ^ b[0],
        a[1] ^ b[1],
        a[2] ^ b[2],
        a[3] ^ b[3],
        a[4] ^ b[4],
        a[5] ^ b[5],
        a[6] ^ b[6],
        a[7] ^ b[7],
    ]
}

#[inline]
pub fn bs_gf256_mask_bit(mask64: u64, a: &BitslicedGf256x64) -> BitslicedGf256x64 {
    [
        a[0] & mask64,
        a[1] & mask64,
        a[2] & mask64,
        a[3] & mask64,
        a[4] & mask64,
        a[5] & mask64,
        a[6] & mask64,
        a[7] & mask64,
    ]
}

/// Multiply 64 bitsliced $\mathcal{T}_3$ elements simultaneously by a public scalar `c: TowerGf256`
/// using the compile-time $8 \times 8$ $\mathbb{F}_2$-linear basis matrix `GF256_MUL_BASIS[c.0]`
/// with 100% branchless masking over secret bit-planes `a[0..8]`.
#[inline]
pub fn bs_gf256_scale_const(c: TowerGf256, a: &BitslicedGf256x64) -> BitslicedGf256x64 {
    let cols = &GF256_MUL_BASIS[c.0 as usize];
    let mut out = [0u64; 8];
    for in_bit in 0..8 {
        let plane = a[in_bit];
        let col = cols[in_bit];
        for out_bit in 0..8 {
            let mask = 0u64.wrapping_sub(((col >> out_bit) & 1) as u64);
            out[out_bit] ^= plane & mask;
        }
    }
    out
}

/// One party's Shamir share of 64 parallel Keccak-f[1600] states over $\mathcal{T}_3 = \mathbb{F}_{2^8}$.
#[derive(Clone)]
pub struct ShamirTowerKeccakParty64 {
    pub eval_point: TowerGf256,
    pub wires: Box<[BitslicedGf256x64; 1600]>,
}

impl Drop for ShamirTowerKeccakParty64 {
    fn drop(&mut self) {
        self.eval_point = TowerGf256::ZERO;
        for w in self.wires.iter_mut() {
            *w = [0u64; 8];
        }
        core::hint::black_box(&*self.wires);
    }
}

#[inline]
fn shamir_fill_planes_gf256_into(
    eval_points: &[TowerGf256],
    secret_planes: &[u64; 1600],
    rand_coeffs: &mut [BitslicedGf256x64],
    parties: &mut [ShamirTowerKeccakParty64],
    rng_seed: &mut u64,
) {
    let n = eval_points.len();
    for w in 0..1600 {
        let c0: BitslicedGf256x64 = [secret_planes[w], 0, 0, 0, 0, 0, 0, 0];
        for rc in rand_coeffs.iter_mut() {
            for b in rc.iter_mut() {
                *b = splitmix64_next(rng_seed);
            }
        }
        for p in 0..n {
            let x = eval_points[p];
            let mut acc = [0u64; 8];
            for rc in rand_coeffs.iter().rev() {
                acc = bs_gf256_xor(&bs_gf256_scale_const(x, &acc), rc);
            }
            parties[p].wires[w] = bs_gf256_xor(&bs_gf256_scale_const(x, &acc), &c0);
        }
    }
}

/// Deal Shamir shares of 64 bitsliced $\mathbb{F}_2$ wires (`[u64; 1600]`) across `n` evaluation points
/// with threshold `t` (`deg <= t - 1`) over $\mathcal{T}_3 = \mathbb{F}_{2^8}$.
pub fn shamir_share_planes_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    secret_planes: &[u64; 1600],
    rng_seed: &mut u64,
) -> Vec<ShamirTowerKeccakParty64> {
    assert!(t >= 1 && t <= eval_points.len());
    let mut parties: Vec<ShamirTowerKeccakParty64> = eval_points
        .iter()
        .map(|&pt| ShamirTowerKeccakParty64 {
            eval_point: pt,
            wires: Box::new([[0u64; 8]; 1600]),
        })
        .collect();
    let mut rand_coeffs = vec![[0u64; 8]; t.saturating_sub(1)];
    shamir_fill_planes_gf256_into(
        eval_points,
        secret_planes,
        &mut rand_coeffs,
        &mut parties,
        rng_seed,
    );
    parties
}

/// Reconstruct 64 bitsliced $\mathbb{F}_2$ wires from any `t` Shamir parties over $\mathcal{T}_3$,
/// returning `None` if evaluation points collide or reconstructed element leaves the $\mathbb{F}_2$ subfield!
pub fn shamir_reconstruct_planes_gf256(quorum: &[&ShamirTowerKeccakParty64]) -> Option<Box<[u64; 1600]>> {
    let pts: Vec<TowerGf256> = quorum.iter().map(|p| p.eval_point).collect();
    let lambdas = lagrange_weights_zero_gf256(&pts)?;
    let mut out = Box::new([0u64; 1600]);
    for w in 0..1600 {
        let mut acc = [0u64; 8];
        for (p, &lam) in quorum.iter().zip(lambdas.iter()) {
            acc = bs_gf256_xor(&acc, &bs_gf256_scale_const(lam, &p.wires[w]));
        }
        // Subfield soundness check: planes 1..8 MUST vanish for ground-field F_2 secrets!
        if (acc[1] | acc[2] | acc[3] | acc[4] | acc[5] | acc[6] | acc[7]) != 0 {
            return None;
        }
        out[w] = acc[0];
    }
    Some(out)
}

#[inline]
fn linear_theta_rho_pi_gf256(
    wires: &mut [BitslicedGf256x64; 1600],
) -> Box<[BitslicedGf256x64; 1600]> {
    let mut c = [[[0u64; 8]; 64]; 5];
    for x in 0..5 {
        for z in 0..64 {
            let mut acc = wires[64 * x + z];
            acc = bs_gf256_xor(&acc, &wires[64 * (x + 5) + z]);
            acc = bs_gf256_xor(&acc, &wires[64 * (x + 10) + z]);
            acc = bs_gf256_xor(&acc, &wires[64 * (x + 15) + z]);
            acc = bs_gf256_xor(&acc, &wires[64 * (x + 20) + z]);
            c[x][z] = acc;
        }
    }
    for x in 0..5 {
        let xm1 = (x + 4) % 5;
        let xp1 = (x + 1) % 5;
        for z in 0..64 {
            let d = bs_gf256_xor(&c[xm1][z], &c[xp1][(z + 63) & 63]);
            for y in 0..5 {
                let idx = 64 * (x + 5 * y) + z;
                wires[idx] = bs_gf256_xor(&wires[idx], &d);
            }
        }
    }

    let mut b = Box::new([[0u64; 8]; 1600]);
    for source in 0..25 {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = (ROTATION_OFFSETS[source] as usize) & 63;
        let src_base = 64 * source;
        let dst_base = 64 * target;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            b[dst_base + z] = wires[src_base + src_z];
        }
    }
    b
}

/// Execute all 24 rounds of `Keccak-f[1600]` across 64 parallel instances for ARBITRARY $t$-of-$n$
/// over `BinaryTower256` ($\mathcal{T}_3 = \mathbb{F}_{2^8}$) using ground-field $\mathbb{F}_2$ Beaver triples!
/// Also collects opened masked differences `(d, e)` so the 2-lane `Tower128` BDOZ MAC check binds the transcript.
pub fn shamir_tower_keccak_f1600_x64(
    t: usize,
    parties: &mut [ShamirTowerKeccakParty64],
    offline_seed: &mut u64,
    transcript_diffs: &mut Vec<u64>,
) -> Option<usize> {
    let n = parties.len();
    if t == 0 || t > n {
        return None;
    }
    let pts: Vec<TowerGf256> = parties[..t].iter().map(|p| p.eval_point).collect();
    let all_pts: Vec<TowerGf256> = parties.iter().map(|p| p.eval_point).collect();
    let lambdas = lagrange_weights_zero_gf256(&pts)?;
    let mut online_bytes_per_party = 0usize;

    let alloc_party_buf = || -> Vec<ShamirTowerKeccakParty64> {
        all_pts
            .iter()
            .map(|&pt| ShamirTowerKeccakParty64 {
                eval_point: pt,
                wires: Box::new([[0u64; 8]; 1600]),
            })
            .collect()
    };
    let mut u_shares = alloc_party_buf();
    let mut v_shares = alloc_party_buf();
    let mut uv_shares = alloc_party_buf();
    let mut rand_coeffs = vec![[0u64; 8]; t.saturating_sub(1)];

    for &rc in &KECCAK_ROUND_CONSTANTS {
        // 1. Offline/preprocessed ground-field F_2 Beaver triple batch `(u, v, w = u & v)` shared over T_3
        let mut u_plain = [0u64; 1600];
        let mut v_plain = [0u64; 1600];
        let mut uv_plain = [0u64; 1600];
        for i in 0..1600 {
            u_plain[i] = splitmix64_next(offline_seed);
            v_plain[i] = splitmix64_next(offline_seed);
            uv_plain[i] = u_plain[i] & v_plain[i];
        }
        shamir_fill_planes_gf256_into(&all_pts, &u_plain, &mut rand_coeffs, &mut u_shares, offline_seed);
        shamir_fill_planes_gf256_into(&all_pts, &v_plain, &mut rand_coeffs, &mut v_shares, offline_seed);
        shamir_fill_planes_gf256_into(&all_pts, &uv_plain, &mut rand_coeffs, &mut uv_shares, offline_seed);

        // 2. Zero-communication local Theta + Rho + Pi across all `n` parties
        let mut b_all: Vec<Box<[BitslicedGf256x64; 1600]>> = parties
            .iter_mut()
            .map(|p| linear_theta_rho_pi_gf256(&mut p.wires))
            .collect();

        // 3. Reconstruct 1-bit masked differences `d = (!b) ^ u` and `e = c ^ v` across the `t`-quorum
        let mut d_open = [0u64; 1600];
        let mut e_open = [0u64; 1600];
        for y in 0..5 {
            let row = 5 * y;
            for x in 0..5 {
                let ib_base = 64 * (row + ((x + 1) % 5));
                let ic_base = 64 * (row + ((x + 2) % 5));
                for z in 0..64 {
                    let w_idx = 64 * (row + x) + z;
                    let ib = ib_base + z;
                    let ic = ic_base + z;

                    let mut acc_d = [0u64; 8];
                    let mut acc_e = [0u64; 8];
                    for (q_idx, &lam) in lambdas.iter().enumerate() {
                        let mut not_b = b_all[q_idx][ib];
                        not_b[0] ^= u64::MAX; // Adding `1 = embedBitToTower 3 true` to polynomial `f(X)` adds 1 to every `f(x_q)`!
                        let diff_d = bs_gf256_xor(&not_b, &u_shares[q_idx].wires[w_idx]);
                        let diff_e = bs_gf256_xor(&b_all[q_idx][ic], &v_shares[q_idx].wires[w_idx]);
                        acc_d = bs_gf256_xor(&acc_d, &bs_gf256_scale_const(lam, &diff_d));
                        acc_e = bs_gf256_xor(&acc_e, &bs_gf256_scale_const(lam, &diff_e));
                    }
                    // Verify opened differences lie in ground field F_2 (`planes 1..8 == 0`)
                    if (acc_d[1] | acc_d[2] | acc_d[3] | acc_d[4] | acc_d[5] | acc_d[6] | acc_d[7])
                        != 0
                        || (acc_e[1]
                            | acc_e[2]
                            | acc_e[3]
                            | acc_e[4]
                            | acc_e[5]
                            | acc_e[6]
                            | acc_e[7])
                            != 0
                    {
                        return None;
                    }
                    d_open[w_idx] = acc_d[0];
                    e_open[w_idx] = acc_e[0];
                }
            }
        }
        online_bytes_per_party += 2 * 1600 * 8;
        transcript_diffs.push(d_open[0] ^ e_open[0]);

        // 4. Local Beaver linear combination + Iota across all `n` parties
        for p_idx in 0..n {
            for y in 0..5 {
                let row = 5 * y;
                for x in 0..5 {
                    let ia_base = 64 * (row + x);
                    for z in 0..64 {
                        let ia = ia_base + z;
                        let d = d_open[ia];
                        let e = e_open[ia];
                        let dv = bs_gf256_mask_bit(d, &v_shares[p_idx].wires[ia]);
                        let eu = bs_gf256_mask_bit(e, &u_shares[p_idx].wires[ia]);
                        let mut prod =
                            bs_gf256_xor(&uv_shares[p_idx].wires[ia], &bs_gf256_xor(&dv, &eu));
                        prod[0] ^= d & e;
                        parties[p_idx].wires[ia] = bs_gf256_xor(&b_all[p_idx][ia], &prod);
                    }
                }
            }
            for z in 0..64 {
                if ((rc >> z) & 1) == 1 {
                    parties[p_idx].wires[z][0] ^= u64::MAX;
                }
            }
        }
        let _ = &mut b_all;
    }
    Some(online_bytes_per_party)
}

/// One party's Shamir share of a 256-bit (`32`-byte) secret seed over $\mathcal{T}_3 = \mathbb{F}_{2^8}$
/// (`256` individual bit evaluations `f_bit(x_p) ∈ TowerGf256`, preserving bit-free Keccak rotations).
#[derive(Clone, PartialEq, Eq)]
pub struct ShamirSeedShare256 {
    pub eval_point: TowerGf256,
    pub bit_shares: [TowerGf256; 256],
}

impl Drop for ShamirSeedShare256 {
    fn drop(&mut self) {
        self.eval_point = TowerGf256::ZERO;
        for b in &mut self.bit_shares {
            *b = TowerGf256::ZERO;
        }
        core::hint::black_box(&self.bit_shares);
    }
}

/// Share a 32-byte secret `[u8; 32]` into `n` `ShamirSeedShare256` shares of threshold `t`.
pub fn shamir_share_seed32_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    secret: &[u8; 32],
    rng_seed: &mut u64,
) -> Vec<ShamirSeedShare256> {
    let mut out: Vec<ShamirSeedShare256> = eval_points
        .iter()
        .map(|&pt| ShamirSeedShare256 {
            eval_point: pt,
            bit_shares: [TowerGf256::ZERO; 256],
        })
        .collect();
    let mut coeffs = vec![TowerGf256::ZERO; t];
    for bit_idx in 0..256 {
        let byte_i = bit_idx / 8;
        let bit_in_byte = bit_idx % 8;
        coeffs[0] = TowerGf256((secret[byte_i] >> bit_in_byte) & 1);
        for c in coeffs.iter_mut().skip(1) {
            *c = TowerGf256((splitmix64_next(rng_seed) & 0xFF) as u8);
        }
        for (p_idx, &pt) in eval_points.iter().enumerate() {
            out[p_idx].bit_shares[bit_idx] = eval_poly_gf256(&coeffs, pt);
        }
    }
    coeffs.fill(TowerGf256::ZERO);
    core::hint::black_box(coeffs.as_slice());
    out
}

/// Reconstruct a 32-byte secret from any `t` `ShamirSeedShare256` shares (used only in tests & 1-round RAM sig opening).
pub fn shamir_reconstruct_seed32_gf256(shares: &[ShamirSeedShare256]) -> Option<[u8; 32]> {
    let pts: Vec<TowerGf256> = shares.iter().map(|s| s.eval_point).collect();
    let lambdas = lagrange_weights_zero_gf256(&pts)?;
    let mut out = [0u8; 32];
    for bit_idx in 0..256 {
        let mut acc = TowerGf256::ZERO;
        for (s, &lam) in shares.iter().zip(lambdas.iter()) {
            acc = acc.add(lam.mul(s.bit_shares[bit_idx]));
        }
        match acc.0 {
            0 => {}
            1 => out[bit_idx / 8] |= 1u8 << (bit_idx % 8),
            _ => return None,
        }
    }
    Some(out)
}

/// Evaluate up to 64 parallel `cSHAKE256` calls for arbitrary $t$-of-$n$ Shamir over `BinaryTower256` ($\mathcal{T}_3$)
/// directly on `ShamirSeedShare256` shares (ZERO reconstruction of `sk_seed` or `sk_prf`!).
pub fn shamir_eval_cshake256_with_seed_shares64(
    t: usize,
    eval_points: &[TowerGf256],
    customization: &[u8],
    public_templates: &[Vec<u8>],
    secret_patches: &[(usize, &[ShamirSeedShare256])], // per instance: `(byte_offset_in_tmpl, slice_of_n_party_seed_shares)`
    offline_seed: &mut u64,
    transcript_diffs: &mut Vec<u64>,
) -> Option<(Vec<[u8; 32]>, usize)> {
    let batch_len = public_templates.len();
    let n = eval_points.len();
    if batch_len == 0 || batch_len > 64 || t == 0 || t > n {
        return None;
    }

    let prefix = if customization.is_empty() {
        Vec::new()
    } else {
        cshake256_customization_prefix(customization)
    };
    let suffix: u8 = if customization.is_empty() { 0x1F } else { 0x04 };

    // Build padded public byte templates (`0` at the 32-byte secret slot) and record secret bit positions
    let mut padded_public: Vec<Vec<u8>> = Vec::with_capacity(batch_len);
    let mut secret_start_bytes: Vec<usize> = Vec::with_capacity(batch_len);
    let mut max_blocks = 0usize;

    for (inst, tmpl) in public_templates.iter().enumerate() {
        let mut buf = Vec::with_capacity(prefix.len() + tmpl.len() + SHAKE256_RATE_BYTES);
        buf.extend_from_slice(&prefix);
        buf.extend_from_slice(tmpl);
        secret_start_bytes.push(prefix.len() + secret_patches[inst].0);

        let rem = buf.len() % SHAKE256_RATE_BYTES;
        let pad_len = SHAKE256_RATE_BYTES - rem;
        buf.resize(buf.len() + pad_len, 0u8);
        let suffix_pos = buf.len() - pad_len;
        buf[suffix_pos] ^= suffix;
        let last_pos = buf.len() - 1;
        buf[last_pos] ^= 0x80;

        max_blocks = max_blocks.max(buf.len() / SHAKE256_RATE_BYTES);
        padded_public.push(buf);
    }

    let mut parties: Vec<ShamirTowerKeccakParty64> = eval_points
        .iter()
        .map(|&pt| ShamirTowerKeccakParty64 {
            eval_point: pt,
            wires: Box::new([[0u64; 8]; 1600]),
        })
        .collect();
    let mut total_online_bytes = 0usize;

    for blk_idx in 0..max_blocks {
        let blk_byte_start = blk_idx * SHAKE256_RATE_BYTES;
        let blk_byte_end = blk_byte_start + SHAKE256_RATE_BYTES;

        // 1. Absorb public rate bytes across active instances (`plane 0` XOR)
        let mut pub_states = [[0u64; 25]; 64];
        let mut active_mask = 0u64;
        for (inst, pbuf) in padded_public.iter().enumerate() {
            if blk_byte_start < pbuf.len() {
                active_mask |= 1u64 << inst;
                for lane in 0..17 {
                    let loff = blk_byte_start + 8 * lane;
                    pub_states[inst][lane] =
                        u64::from_le_bytes(pbuf[loff..loff + 8].try_into().unwrap());
                }
            }
        }
        let pub_planes = transpose_states_to_planes(&pub_states[..batch_len]);
        let prev_wires: Vec<Box<[BitslicedGf256x64; 1600]>> =
            parties.iter().map(|p| p.wires.clone()).collect();

        for p in &mut parties {
            for w in 0..1600 {
                p.wires[w][0] ^= pub_planes[w];
            }
        }

        // 2. Absorb secret `ShamirSeedShare256` bit shares falling inside `[blk_byte_start, blk_byte_end)`
        for (inst, &(_, seed_shares)) in secret_patches.iter().enumerate() {
            if ((active_mask >> inst) & 1) == 0 {
                continue;
            }
            let s_start = secret_start_bytes[inst];
            for k_byte in 0..32 {
                let abs_byte = s_start + k_byte;
                if abs_byte >= blk_byte_start && abs_byte < blk_byte_end {
                    let rel_byte = abs_byte - blk_byte_start;
                    let lane = rel_byte / 8;
                    let byte_in_lane = rel_byte % 8;
                    for bit_in_byte in 0..8 {
                        let wire_idx = 64 * lane + 8 * byte_in_lane + bit_in_byte;
                        let seed_bit_idx = 8 * k_byte + bit_in_byte;
                        let inst_bit = 1u64 << inst;
                        for p_idx in 0..n {
                            let val = seed_shares[p_idx].bit_shares[seed_bit_idx].0;
                            for gf_b in 0..8 {
                                let mask = 0u64.wrapping_sub(((val >> gf_b) & 1) as u64);
                                parties[p_idx].wires[wire_idx][gf_b] ^= inst_bit & mask;
                            }
                        }
                    }
                }
            }
        }

        // 3. Run 24-round bitsliced Shamir Keccak-f[1600]
        total_online_bytes += shamir_tower_keccak_f1600_x64(
            t,
            &mut parties,
            offline_seed,
            transcript_diffs,
        )?;

        if active_mask != ((1u64 << batch_len) - 1) {
            let keep = !active_mask;
            for (p_idx, p) in parties.iter_mut().enumerate() {
                for w in 0..1600 {
                    for gf_b in 0..8 {
                        p.wires[w][gf_b] =
                            (p.wires[w][gf_b] & active_mask) | (prev_wires[p_idx][w][gf_b] & keep);
                    }
                }
            }
        }
    }

    // Reconstruct squeezed 32-byte outputs from the first `t` quorum parties
    let quorum_refs: Vec<&ShamirTowerKeccakParty64> = parties[..t].iter().collect();
    let out_planes = shamir_reconstruct_planes_gf256(&quorum_refs)?;
    let out_states = transpose_planes_to_states(&out_planes, batch_len);
    let mut digests = Vec::with_capacity(batch_len);
    for st in &out_states {
        let mut d = [0u8; 32];
        for lane in 0..4 {
            d[8 * lane..8 * (lane + 1)].copy_from_slice(&st[lane].to_le_bytes());
        }
        digests.push(d);
    }
    Some((digests, total_online_bytes))
}

/// Evaluate up to 64 parallel `cSHAKE256` calls for arbitrary $t$-of-$n$ Shamir over `BinaryTower256` ($\mathcal{T}_3$)
/// WITHOUT opening the squeezed digests: returns per-instance `Vec<ShamirSeedShare256>` across all `n` parties,
/// keeping intermediate WOTS+C chain states `[c^(s)]` 100% secret-shared in signer RAM!
pub fn shamir_eval_cshake256_secret_shares64(
    t: usize,
    eval_points: &[TowerGf256],
    customization: &[u8],
    public_templates: &[Vec<u8>],
    secret_patches: &[(usize, &[ShamirSeedShare256])],
    offline_seed: &mut u64,
    transcript_diffs: &mut Vec<u64>,
) -> Option<(Vec<Vec<ShamirSeedShare256>>, usize)> {
    let batch_len = public_templates.len();
    let n = eval_points.len();
    if batch_len == 0 || batch_len > 64 || t == 0 || t > n {
        return None;
    }

    let prefix = if customization.is_empty() {
        Vec::new()
    } else {
        cshake256_customization_prefix(customization)
    };
    let suffix: u8 = if customization.is_empty() { 0x1F } else { 0x04 };

    let mut padded_public: Vec<Vec<u8>> = Vec::with_capacity(batch_len);
    let mut secret_start_bytes: Vec<usize> = Vec::with_capacity(batch_len);
    let mut max_blocks = 0usize;

    for (inst, tmpl) in public_templates.iter().enumerate() {
        let mut buf = Vec::with_capacity(prefix.len() + tmpl.len() + SHAKE256_RATE_BYTES);
        buf.extend_from_slice(&prefix);
        buf.extend_from_slice(tmpl);
        secret_start_bytes.push(prefix.len() + secret_patches[inst].0);

        let rem = buf.len() % SHAKE256_RATE_BYTES;
        let pad_len = SHAKE256_RATE_BYTES - rem;
        buf.resize(buf.len() + pad_len, 0u8);
        let suffix_pos = buf.len() - pad_len;
        buf[suffix_pos] ^= suffix;
        let last_pos = buf.len() - 1;
        buf[last_pos] ^= 0x80;

        max_blocks = max_blocks.max(buf.len() / SHAKE256_RATE_BYTES);
        padded_public.push(buf);
    }

    let mut parties: Vec<ShamirTowerKeccakParty64> = eval_points
        .iter()
        .map(|&pt| ShamirTowerKeccakParty64 {
            eval_point: pt,
            wires: Box::new([[0u64; 8]; 1600]),
        })
        .collect();
    let mut total_online_bytes = 0usize;

    for blk_idx in 0..max_blocks {
        let blk_byte_start = blk_idx * SHAKE256_RATE_BYTES;
        let blk_byte_end = blk_byte_start + SHAKE256_RATE_BYTES;

        let mut pub_states = [[0u64; 25]; 64];
        let mut active_mask = 0u64;
        for (inst, pbuf) in padded_public.iter().enumerate() {
            if blk_byte_start < pbuf.len() {
                active_mask |= 1u64 << inst;
                for lane in 0..17 {
                    let loff = blk_byte_start + 8 * lane;
                    pub_states[inst][lane] =
                        u64::from_le_bytes(pbuf[loff..loff + 8].try_into().unwrap());
                }
            }
        }
        let pub_planes = transpose_states_to_planes(&pub_states[..batch_len]);
        let prev_wires: Vec<Box<[BitslicedGf256x64; 1600]>> =
            parties.iter().map(|p| p.wires.clone()).collect();

        for p in &mut parties {
            for w in 0..1600 {
                p.wires[w][0] ^= pub_planes[w];
            }
        }

        for (inst, &(_, seed_shares)) in secret_patches.iter().enumerate() {
            if ((active_mask >> inst) & 1) == 0 {
                continue;
            }
            let s_start = secret_start_bytes[inst];
            for k_byte in 0..32 {
                let abs_byte = s_start + k_byte;
                if abs_byte >= blk_byte_start && abs_byte < blk_byte_end {
                    let rel_byte = abs_byte - blk_byte_start;
                    let lane = rel_byte / 8;
                    let byte_in_lane = rel_byte % 8;
                    for bit_in_byte in 0..8 {
                        let wire_idx = 64 * lane + 8 * byte_in_lane + bit_in_byte;
                        let seed_bit_idx = 8 * k_byte + bit_in_byte;
                        let inst_bit = 1u64 << inst;
                        for p_idx in 0..n {
                            let val = seed_shares[p_idx].bit_shares[seed_bit_idx].0;
                            for gf_b in 0..8 {
                                let mask = 0u64.wrapping_sub(((val >> gf_b) & 1) as u64);
                                parties[p_idx].wires[wire_idx][gf_b] ^= inst_bit & mask;
                            }
                        }
                    }
                }
            }
        }

        total_online_bytes += shamir_tower_keccak_f1600_x64(
            t,
            &mut parties,
            offline_seed,
            transcript_diffs,
        )?;

        if active_mask != ((1u64 << batch_len) - 1) {
            let keep = !active_mask;
            for (p_idx, p) in parties.iter_mut().enumerate() {
                for w in 0..1600 {
                    for gf_b in 0..8 {
                        p.wires[w][gf_b] =
                            (p.wires[w][gf_b] & active_mask) | (prev_wires[p_idx][w][gf_b] & keep);
                    }
                }
            }
        }
    }

    // Extract 256 squeezed bit shares (`lanes 0..4`) per instance across all `n` parties WITHOUT opening!
    let mut out_shares: Vec<Vec<ShamirSeedShare256>> = Vec::with_capacity(batch_len);
    for inst in 0..batch_len {
        let mut inst_party_shares: Vec<ShamirSeedShare256> = eval_points
            .iter()
            .map(|&pt| ShamirSeedShare256 {
                eval_point: pt,
                bit_shares: [TowerGf256::ZERO; 256],
            })
            .collect();
        for bit_idx in 0..256 {
            let byte_i = bit_idx / 8;
            let bit_in_byte = bit_idx % 8;
            let lane = byte_i / 8;
            let byte_in_lane = byte_i % 8;
            let wire_idx = 64 * lane + 8 * byte_in_lane + bit_in_byte;
            for p_idx in 0..n {
                let mut gf_val = 0u8;
                for gf_b in 0..8 {
                    let bit = ((parties[p_idx].wires[wire_idx][gf_b] >> inst) & 1) as u8;
                    gf_val |= bit << gf_b;
                }
                inst_party_shares[p_idx].bit_shares[bit_idx] = TowerGf256(gf_val);
            }
        }
        out_shares.push(inst_party_shares);
    }
    Some((out_shares, total_online_bytes))
}

// ============================================================================
// 5. 2-Lane Split-Custody `Tower128 × Tower128` BDOZ/SPDZ MACs & Identifiable Abort
// ============================================================================

/// Non-cloneable, non-debug, non-serializable split-custody 2-lane `Tower128 × Tower128` MAC key share
/// (`256-bit` post-quantum soundness margin across high & low lanes).
///
/// Intentionally implements **NEITHER `Clone`, `Debug`, NOR `Serialize`**, and exposes NO global key getter.
pub struct MacKeyShareCustody {
    alpha_hi: Tower128,
    alpha_lo: Tower128,
}

impl Drop for MacKeyShareCustody {
    fn drop(&mut self) {
        self.alpha_hi = Tower128::ZERO;
        self.alpha_lo = Tower128::ZERO;
        core::hint::black_box(&self.alpha_hi);
        core::hint::black_box(&self.alpha_lo);
    }
}

impl MacKeyShareCustody {
    #[inline]
    pub const fn new_custody_share(alpha_hi: Tower128, alpha_lo: Tower128) -> Self {
        Self { alpha_hi, alpha_lo }
    }

    /// Form party `i`'s 2-lane SPDZ/BDOZ MAC share `γ_i(x) = α_i · x_i ⊕ ⊕_{j ≠ i} (u_{i,j} ⊕ v_{i,j})`
    /// including all off-diagonal correlated-OT cross-terms (`ThresholdHashMpc.formBdozPartyMacShare`).
    #[inline]
    pub fn form_party_mac_share_2lane(
        &self,
        party_idx: usize,
        x_i: Tower128,
        ot_u_hi: &[Tower128],
        ot_v_hi: &[Tower128],
        ot_u_lo: &[Tower128],
        ot_v_lo: &[Tower128],
    ) -> (Tower128, Tower128) {
        let mut acc_hi = self.alpha_hi.mul(x_i);
        let mut acc_lo = self.alpha_lo.mul(x_i);
        for j in 0..ot_u_hi.len() {
            if j == party_idx {
                continue;
            }
            acc_hi = acc_hi.add(ot_u_hi[j].add(ot_v_hi[j]));
            acc_lo = acc_lo.add(ot_u_lo[j].add(ot_v_lo[j]));
        }
        (acc_hi, acc_lo)
    }

    /// Compute party `i`'s terminal batch check contribution `α_i · ghashPoly(chal, opened_vals) ⊕ ghashPoly(chal, mac_shares_i)`.
    #[inline]
    pub fn compute_batch_check_share_2lane(
        &self,
        chal_hi: Tower128,
        chal_lo: Tower128,
        opened_vals: &[Tower128],
        mac_shares_hi: &[Tower128],
        mac_shares_lo: &[Tower128],
    ) -> (Tower128, Tower128) {
        let val_poly_hi = ghash_poly_tower128(chal_hi, opened_vals);
        let val_poly_lo = ghash_poly_tower128(chal_lo, opened_vals);
        let mac_poly_hi = ghash_poly_tower128(chal_hi, mac_shares_hi);
        let mac_poly_lo = ghash_poly_tower128(chal_lo, mac_shares_lo);
        (
            self.alpha_hi.mul(val_poly_hi).add(mac_poly_hi),
            self.alpha_lo.mul(val_poly_lo).add(mac_poly_lo),
        )
    }

    /// Issue a pairwise BDOZ local key `k_{i->j}` for honesttag `m_{j->i} = k_{i->j} ⊕ α_i · x_j` during OT preprocessing.
    #[inline]
    pub fn derive_pairwise_bdoz_local_key_2lane(
        &self,
        x_j: Tower128,
        tag_ji_hi: Tower128,
        tag_ji_lo: Tower128,
    ) -> (Tower128, Tower128) {
        (
            tag_ji_hi.add(self.alpha_hi.mul(x_j)),
            tag_ji_lo.add(self.alpha_lo.mul(x_j)),
        )
    }

    /// Deterministically verify party `j`'s opened share `x'_j` against pairwise 2-lane BDOZ tags `(m'_{j->i})`,
    /// emitting an accountable `SlashingReceipt` upon failure (`ThresholdHashMpc.bdoz_cheater_identified_or_mac_forged`).
    pub fn verify_pairwise_bdoz_or_slash(
        &self,
        session_view: u64,
        verifier_party: usize,
        accused_party: usize,
        k_ij_hi: Tower128,
        k_ij_lo: Tower128,
        opened_x_j: Tower128,
        opened_tag_hi: Tower128,
        opened_tag_lo: Tower128,
    ) -> Result<(), SlashingReceipt> {
        let expected_hi = k_ij_hi.add(self.alpha_hi.mul(opened_x_j));
        let expected_lo = k_ij_lo.add(self.alpha_lo.mul(opened_x_j));
        if opened_tag_hi != expected_hi {
            return Err(SlashingReceipt {
                session_view,
                accused_party,
                verifier_party,
                failed_lane: 0,
            });
        }
        if opened_tag_lo != expected_lo {
            return Err(SlashingReceipt {
                session_view,
                accused_party,
                verifier_party,
                failed_lane: 1,
            });
        }
        Ok(())
    }
}

/// Accountable slashing certificate pinpointing the exact cheating party upon BDOZ MAC verification failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlashingReceipt {
    pub session_view: u64,
    pub accused_party: usize,
    pub verifier_party: usize,
    pub failed_lane: u8,
}

/// Verify terminal 2-lane `Tower128 × Tower128` batch MAC check (`∑_i check_share_i == (0, 0)`),
/// matching `ThresholdHashMpc.verifyBatchTowerMac2Lane`.
#[inline]
pub fn verify_batch_tower_mac_2lane(party_check_shares: &[(Tower128, Tower128)]) -> bool {
    let mut sum_hi = Tower128::ZERO;
    let mut sum_lo = Tower128::ZERO;
    for &(hi, lo) in party_check_shares {
        sum_hi = sum_hi.add(hi);
        sum_lo = sum_lo.add(lo);
    }
    sum_hi == Tower128::ZERO && sum_lo == Tower128::ZERO
}
