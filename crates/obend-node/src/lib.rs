//! `obend-node` — Live Multi-Node Rust Runner (`WS 26`)
//!
//! Binds symbolic `Obend.Consensus.Simplex` BFT consensus (`PropCert`, `SkipCert`, `FinCert`, and
//! accountable equivocation slashing), `Obend.Vault.Projection` (`FogOfWar` blinded Merkle multiproofs),
//! and `Obend.Judge.Clearing` (`drex-clearing@1` primal-dual LP orderbook clearing) to concrete
//! cryptographic primitives (FIPS 180-4 SHA-256, NIST FIPS 202 / SP 800-185 Keccak-f[1600] cSHAKE256
//! sponge, and twisted Edwards Curve25519 / Ed25519 signing & verification) and verifies emitted
//! certificates through `crates/obend-ffi` (`ObendSession`).

use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};

pub mod net;
pub use net::*;

// ============================================================================
// 1. Concrete Cryptographic Primitives (SHA-256, Keccak-f[1600] cSHAKE256, Ed25519)
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

/// Standard 24-round Keccak-f[1600] iota round constants (NIST FIPS 202).
const KECCAK_RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Keccak-f[1600] rho rotation offsets.
const KECCAK_RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
    27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

/// Keccak-f[1600] pi lane permutation indices.
const KECCAK_PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// Execute the 24-round Keccak-f[1600] permutation in-place on `state`.
pub fn keccak_f1600(state: &mut [u64; 25]) {
    for &rc in &KECCAK_RC {
        // Theta
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in (0..25).step_by(5) {
                state[x + y] ^= d;
            }
        }
        // Rho and Pi
        let mut current = state[1];
        for i in 0..24 {
            let j = KECCAK_PI[i];
            let temp = state[j];
            state[j] = current.rotate_left(KECCAK_RHO[i]);
            current = temp;
        }
        // Chi
        for y in (0..25).step_by(5) {
            let row = [state[y], state[y + 1], state[y + 2], state[y + 3], state[y + 4]];
            for x in 0..5 {
                state[y + x] = row[x] ^ ((!row[(x + 1) % 5]) & row[(x + 2) % 5]);
            }
        }
        // Iota
        state[0] ^= rc;
    }
}

/// Absorb arbitrary bytes into a rate-136-byte (1088-bit, 256-bit security capacity) Keccak sponge
/// with domain suffix `domain_sep` (`0x04` for NIST SP 800-185 cSHAKE256, `0x1F` for SHAKE256)
/// and squeeze 32 bytes.
pub fn keccak256_sponge(domain_sep: u8, chunks: &[&[u8]]) -> [u8; 32] {
    const RATE: usize = 136;
    let mut state = [0u64; 25];
    let mut block = [0u8; RATE];
    let mut offset = 0usize;

    for &chunk in chunks {
        for &byte in chunk {
            block[offset] ^= byte;
            offset += 1;
            if offset == RATE {
                for i in 0..17 {
                    state[i] ^= u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap());
                }
                keccak_f1600(&mut state);
                block = [0u8; RATE];
                offset = 0;
            }
        }
    }

    block[offset] ^= domain_sep;
    block[RATE - 1] ^= 0x80;
    for i in 0..17 {
        state[i] ^= u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap());
    }
    keccak_f1600(&mut state);

    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&state[i].to_le_bytes());
    }
    out
}

/// Domain-separated cSHAKE256 (NIST SP 800-185 Keccak-f[1600] sponge) 256-bit commitment digest
/// with customization string `custom`.
pub fn cshake256_domain(custom: &[u8], left: &[u8], right: &[u8]) -> [u8; 32] {
    let custom_len = (custom.len() as u64).to_le_bytes();
    let left_len = (left.len() as u64).to_le_bytes();
    let right_len = (right.len() as u64).to_le_bytes();
    let domain_sep = if custom.is_empty() { 0x1Fu8 } else { 0x04u8 };
    keccak256_sponge(
        domain_sep,
        &[
            b"OBEND-cSHAKE256:",
            &custom_len,
            custom,
            &left_len,
            left,
            &right_len,
            right,
        ],
    )
}

// ============================================================================
// 1b. Twisted Edwards Curve25519 (-x^2 + y^2 = 1 + d*x^2*y^2 mod 2^255 - 19)
// ============================================================================

/// Field element in GF(2^255 - 19) represented in radix 2^51 (`[u64; 5]`).
#[derive(Clone, Copy, Debug)]
struct Fe([u64; 5]);

const MASK51: u64 = (1u64 << 51) - 1;

impl Fe {
    const ZERO: Self = Self([0, 0, 0, 0, 0]);
    const ONE: Self = Self([1, 0, 0, 0, 0]);

    fn from_u64(v: u64) -> Self {
        Self([v & MASK51, v >> 51, 0, 0, 0])
    }

    fn carry(mut h: [u64; 5]) -> Self {
        for _ in 0..2 {
            let c0 = h[0] >> 51;
            h[0] &= MASK51;
            h[1] += c0;
            let c1 = h[1] >> 51;
            h[1] &= MASK51;
            h[2] += c1;
            let c2 = h[2] >> 51;
            h[2] &= MASK51;
            h[3] += c2;
            let c3 = h[3] >> 51;
            h[3] &= MASK51;
            h[4] += c3;
            let c4 = h[4] >> 51;
            h[4] &= MASK51;
            h[0] += c4 * 19;
        }
        Self(h)
    }

    fn add(self, rhs: Self) -> Self {
        Self::carry([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ])
    }

    fn sub(self, rhs: Self) -> Self {
        // Add 2*p in radix 2^51 before subtracting to avoid underflow
        Self::carry([
            (self.0[0] + 0xfffffffffffda) - rhs.0[0],
            (self.0[1] + 0xffffffffffffe) - rhs.0[1],
            (self.0[2] + 0xffffffffffffe) - rhs.0[2],
            (self.0[3] + 0xffffffffffffe) - rhs.0[3],
            (self.0[4] + 0xffffffffffffe) - rhs.0[4],
        ])
    }

    fn neg(self) -> Self {
        Self::ZERO.sub(self)
    }

    fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;
        let a0 = a[0] as u128;
        let a1 = a[1] as u128;
        let a2 = a[2] as u128;
        let a3 = a[3] as u128;
        let a4 = a[4] as u128;
        let b0 = b[0] as u128;
        let b1 = b[1] as u128;
        let b2 = b[2] as u128;
        let b3 = b[3] as u128;
        let b4 = b[4] as u128;

        let mut r0 = a0 * b0 + 19 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1);
        let mut r1 = a0 * b1 + a1 * b0 + 19 * (a2 * b4 + a3 * b3 + a4 * b2);
        let mut r2 = a0 * b2 + a1 * b1 + a2 * b0 + 19 * (a3 * b4 + a4 * b3);
        let mut r3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + 19 * (a4 * b4);
        let mut r4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;

        let c0 = r0 >> 51;
        r0 &= MASK51 as u128;
        r1 += c0;
        let c1 = r1 >> 51;
        r1 &= MASK51 as u128;
        r2 += c1;
        let c2 = r2 >> 51;
        r2 &= MASK51 as u128;
        r3 += c2;
        let c3 = r3 >> 51;
        r3 &= MASK51 as u128;
        r4 += c3;
        let c4 = r4 >> 51;
        r4 &= MASK51 as u128;
        r0 += c4 * 19;

        Self::carry([r0 as u64, r1 as u64, r2 as u64, r3 as u64, r4 as u64])
    }

    fn sq(self) -> Self {
        self.mul(self)
    }

    /// Canonical 32-byte little-endian encoding in [0, 2^255 - 19).
    fn to_bytes(self) -> [u8; 32] {
        let mut h = Self::carry(self.0).0;
        // Compute h + 19; if it overflows 2^255, h >= 2^255 - 19
        let mut q = (h[0] + 19) >> 51;
        q = (h[1] + q) >> 51;
        q = (h[2] + q) >> 51;
        q = (h[3] + q) >> 51;
        q = (h[4] + q) >> 51;

        h[0] += 19 * q;
        let c0 = h[0] >> 51;
        h[0] &= MASK51;
        h[1] += c0;
        let c1 = h[1] >> 51;
        h[1] &= MASK51;
        h[2] += c1;
        let c2 = h[2] >> 51;
        h[2] &= MASK51;
        h[3] += c2;
        let c3 = h[3] >> 51;
        h[3] &= MASK51;
        h[4] = (h[4] + c3) & MASK51;

        // Pack five 51-bit limbs into 256 bits
        let mut out = [0u8; 32];
        let mut acc = 0u128;
        let mut acc_bits = 0u32;
        let mut byte_idx = 0usize;
        for &limb in &h {
            acc |= (limb as u128) << acc_bits;
            acc_bits += 51;
            while acc_bits >= 8 && byte_idx < 32 {
                out[byte_idx] = (acc & 0xFF) as u8;
                acc >>= 8;
                acc_bits -= 8;
                byte_idx += 1;
            }
        }
        if byte_idx < 32 {
            out[byte_idx] = (acc & 0xFF) as u8;
        }
        out
    }

    fn from_bytes(bytes: &[u8; 32]) -> Self {
        let mut h = [0u64; 5];
        let mut acc = 0u128;
        let mut acc_bits = 0u32;
        let mut limb_idx = 0usize;
        for &b in bytes {
            acc |= (b as u128) << acc_bits;
            acc_bits += 8;
            if acc_bits >= 51 && limb_idx < 4 {
                h[limb_idx] = (acc & (MASK51 as u128)) as u64;
                acc >>= 51;
                acc_bits -= 51;
                limb_idx += 1;
            }
        }
        h[4] = (acc & ((1u128 << 51) - 1)) as u64 & ((1u64 << 51) - 1);
        h[4] &= (1u64 << 51) - 1;
        Self::carry(h)
    }

    /// Exponentiation by a 256-bit little-endian byte array.
    fn pow_bytes(self, exp_le: &[u8; 32]) -> Self {
        let mut res = Self::ONE;
        let mut base = self;
        for &byte in exp_le {
            for bit in 0..8 {
                if ((byte >> bit) & 1) == 1 {
                    res = res.mul(base);
                }
                base = base.sq();
            }
        }
        res
    }

    /// Multiplicative inverse a^(p - 2) mod (2^255 - 19).
    fn inv(self) -> Self {
        // p - 2 = 2^255 - 21
        let mut exp = [0xFFu8; 32];
        exp[0] = 256u16.wrapping_sub(21) as u8; // 0xEB = 235
        exp[31] = 0x7F;
        self.pow_bytes(&exp)
    }
}

impl PartialEq for Fe {
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes() == other.to_bytes()
    }
}
impl Eq for Fe {}

/// Extended twisted Edwards point (X : Y : Z : T) with X*Y = Z*T on -x^2 + y^2 = 1 + d*x^2*y^2.
#[derive(Clone, Copy, Debug)]
struct EdwardsPoint {
    x: Fe,
    y: Fe,
    z: Fe,
    t: Fe,
}

impl EdwardsPoint {
    const IDENTITY: Self = Self {
        x: Fe::ZERO,
        y: Fe::ONE,
        z: Fe::ONE,
        t: Fe::ZERO,
    };

    /// Curve constant d = -121665 / 121666 mod (2^255 - 19).
    fn curve_d() -> Fe {
        static CURVE_D: std::sync::OnceLock<Fe> = std::sync::OnceLock::new();
        *CURVE_D.get_or_init(|| Fe::from_u64(121665).neg().mul(Fe::from_u64(121666).inv()))
    }

    /// Principal square root of -1: 2^((p - 1) / 4) mod (2^255 - 19).
    fn sqrt_m1() -> Fe {
        static SQRT_M1: std::sync::OnceLock<Fe> = std::sync::OnceLock::new();
        *SQRT_M1.get_or_init(|| {
            // (p - 1) / 4 = (2^255 - 20) / 4 = 2^253 - 5
            let mut exp = [0xFFu8; 32];
            exp[0] = 0xFB; // 256 - 5 = 251
            exp[31] = 0x1F;
            Fe::from_u64(2).pow_bytes(&exp)
        })
    }

    /// Complete unified twisted Edwards addition (Hisil et al. 2008 / RFC 8032 §5.1.4).
    fn add(self, rhs: Self) -> Self {
        let d = Self::curve_d();
        let a = self.y.sub(self.x).mul(rhs.y.sub(rhs.x));
        let b = self.y.add(self.x).mul(rhs.y.add(rhs.x));
        let c = self.t.mul(rhs.t).mul(d).mul(Fe::from_u64(2));
        let dd = self.z.mul(rhs.z).mul(Fe::from_u64(2));
        let e = b.sub(a);
        let f = dd.sub(c);
        let g = dd.add(c);
        let h = b.add(a);
        Self {
            x: e.mul(f),
            y: g.mul(h),
            z: f.mul(g),
            t: e.mul(h),
        }
    }

    fn scalar_mul(self, scalar_le: &[u8; 32]) -> Self {
        let mut res = Self::IDENTITY;
        let mut temp = self;
        for &byte in scalar_le {
            for bit in 0..8 {
                if ((byte >> bit) & 1) == 1 {
                    res = res.add(temp);
                }
                temp = temp.add(temp);
            }
        }
        res
    }

    /// Compress to 32 bytes (little-endian `y` with the low bit of `x` in bit 255).
    fn encode(self) -> [u8; 32] {
        let z_inv = self.z.inv();
        let x = self.x.mul(z_inv).to_bytes();
        let mut y = self.y.mul(z_inv).to_bytes();
        y[31] |= (x[0] & 1) << 7;
        y
    }

    /// Decompress a 32-byte point and verify it lies on -x^2 + y^2 = 1 + d*x^2*y^2.
    fn decode(bytes: &[u8; 32]) -> Option<Self> {
        let x_sign = (bytes[31] >> 7) & 1;
        let mut y_bytes = *bytes;
        y_bytes[31] &= 0x7F;
        let y = Fe::from_bytes(&y_bytes);
        // Require canonical y < p
        if y.to_bytes() != y_bytes {
            return None;
        }
        let d = Self::curve_d();
        let y2 = y.sq();
        let u = y2.sub(Fe::ONE);
        let v = d.mul(y2).add(Fe::ONE);
        let w = u.mul(v.inv());

        // Candidate root x = w^((p + 3) / 8) mod p, where (p + 3) / 8 = 2^252 - 2
        let mut exp = [0xFFu8; 32];
        exp[0] = 0xFE;
        exp[31] = 0x0F;
        let mut x = w.pow_bytes(&exp);
        if x.sq() != w {
            let x_alt = x.mul(Self::sqrt_m1());
            if x_alt.sq() == w {
                x = x_alt;
            } else {
                return None;
            }
        }
        if x == Fe::ZERO && x_sign == 1 {
            return None;
        }
        if (x.to_bytes()[0] & 1) != x_sign {
            x = x.neg();
        }
        Some(Self {
            x,
            y,
            z: Fe::ONE,
            t: x.mul(y),
        })
    }

    /// RFC 8032 Ed25519 basepoint B (y = 4/5 mod p, x >= 0 even).
    fn basepoint() -> Self {
        static BASEPOINT: std::sync::OnceLock<EdwardsPoint> = std::sync::OnceLock::new();
        *BASEPOINT.get_or_init(|| {
            let by = Fe::from_u64(4).mul(Fe::from_u64(5).inv()).to_bytes();
            Self::decode(&by).expect("valid Ed25519 basepoint B")
        })
    }
}

/// Prime order L = 2^252 + 27742317777372353535851937790883648493 of the Ed25519 basepoint B.
const ED25519_L: [u64; 4] = [
    0x5812631a5cf5d3ed,
    0x14def9dea2f79cd6,
    0x0000000000000000,
    0x1000000000000000,
];

fn u256_ge(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn u256_sub(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = (b1 as u64) + (b2 as u64);
    }
    out
}

fn scalar_add_mod_l(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(carry);
        out[i] = s2;
        carry = (c1 as u64) + (c2 as u64);
    }
    if carry > 0 || u256_ge(&out, &ED25519_L) {
        out = u256_sub(&out, &ED25519_L);
    }
    out
}

fn scalar_from_bytes_mod_l(bytes_le: &[u8; 32]) -> [u64; 4] {
    let mut acc = [0u64; 4];
    for &byte in bytes_le.iter().rev() {
        for bit in (0..8).rev() {
            acc = scalar_add_mod_l(&acc, &acc);
            if ((byte >> bit) & 1) == 1 {
                acc = scalar_add_mod_l(&acc, &[1, 0, 0, 0]);
            }
        }
    }
    acc
}

fn scalar_mul_mod_l(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut res = [0u64; 4];
    let mut base = *a;
    for i in 0..4 {
        let word = b[i];
        for bit in 0..64 {
            if ((word >> bit) & 1) == 1 {
                res = scalar_add_mod_l(&res, &base);
            }
            base = scalar_add_mod_l(&base, &base);
        }
    }
    res
}

fn scalar_to_bytes_le(s: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&s[i].to_le_bytes());
    }
    out
}

fn scalar_from_canonical_bytes_le(bytes: &[u8; 32]) -> Option<[u64; 4]> {
    let mut s = [0u64; 4];
    for i in 0..4 {
        s[i] = u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap());
    }
    if u256_ge(&s, &ED25519_L) {
        None
    } else {
        Some(s)
    }
}

/// Deterministic Ed25519 validator keypair over twisted Edwards Curve25519 for signing & verifying
/// BFT consensus certificates (`[S]B = R + [k]A`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorKeypair {
    pub node_id: usize,
    pub public_key: [u8; 32],
    secret_key: [u8; 32],
}

impl ValidatorKeypair {
    /// Deterministically derive a validator Curve25519 keypair from `node_id` and seed bytes.
    pub fn from_seed(node_id: usize, seed: &[u8]) -> Self {
        let raw_sk = cshake256_domain(b"obend.ed25519.sk", &node_id.to_be_bytes(), seed);
        let mut a_scalar = scalar_from_bytes_mod_l(&raw_sk);
        if a_scalar == [0, 0, 0, 0] {
            a_scalar[0] = 1;
        }
        let secret_key = scalar_to_bytes_le(&a_scalar);
        let a_point = EdwardsPoint::basepoint().scalar_mul(&secret_key);
        let public_key = a_point.encode();
        Self {
            node_id,
            public_key,
            secret_key,
        }
    }

    /// Sign a domain-separated consensus message payload using Schnorr/Ed25519 (`S = (r + k*a) mod L`).
    pub fn sign(&self, msg: &[u8]) -> [u8; 64] {
        let a_scalar = scalar_from_bytes_mod_l(&self.secret_key);
        let r_hash = cshake256_domain(b"obend.ed25519.r", &self.secret_key, msg);
        let mut r_scalar = scalar_from_bytes_mod_l(&r_hash);
        if r_scalar == [0, 0, 0, 0] {
            r_scalar[0] = 1;
        }
        let r_bytes_scalar = scalar_to_bytes_le(&r_scalar);
        let r_point = EdwardsPoint::basepoint().scalar_mul(&r_bytes_scalar);
        let r_encoded = r_point.encode();

        let k_hash = cshake256_domain(
            b"obend.ed25519.k",
            &r_encoded,
            &[&self.public_key[..], msg].concat(),
        );
        let k_scalar = scalar_from_bytes_mod_l(&k_hash);
        let ka = scalar_mul_mod_l(&k_scalar, &a_scalar);
        let s_scalar = scalar_add_mod_l(&r_scalar, &ka);
        let s_encoded = scalar_to_bytes_le(&s_scalar);

        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&r_encoded);
        sig[32..].copy_from_slice(&s_encoded);
        sig
    }

    /// Verify a 64-byte Ed25519 signature `(R, S)` against `public_key` (`A`) and `msg`
    /// by checking the Curve25519 group equation `[S]B == R + [k]A`.
    pub fn verify(public_key: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
        let mut r_encoded = [0u8; 32];
        let mut s_encoded = [0u8; 32];
        r_encoded.copy_from_slice(&sig[..32]);
        s_encoded.copy_from_slice(&sig[32..]);

        let Some(_s_scalar) = scalar_from_canonical_bytes_le(&s_encoded) else {
            return false;
        };
        let Some(a_point) = EdwardsPoint::decode(public_key) else {
            return false;
        };
        let Some(r_point) = EdwardsPoint::decode(&r_encoded) else {
            return false;
        };
        // Reject identity public key or identity R
        if a_point.encode() == EdwardsPoint::IDENTITY.encode()
            || r_point.encode() == EdwardsPoint::IDENTITY.encode()
        {
            return false;
        }

        let k_hash = cshake256_domain(
            b"obend.ed25519.k",
            &r_encoded,
            &[&public_key[..], msg].concat(),
        );
        let k_scalar = scalar_from_bytes_mod_l(&k_hash);
        let k_bytes = scalar_to_bytes_le(&k_scalar);

        let lhs = EdwardsPoint::basepoint().scalar_mul(&s_encoded);
        let rhs = r_point.add(a_point.scalar_mul(&k_bytes));
        lhs.encode() == rhs.encode()
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
            OrderSide::Bid => (price as u128) * (self.qty as u128) <= (self.total as u128),
            OrderSide::Ask => (self.total as u128) <= (price as u128) * (self.qty as u128),
        }
    }
}

/// Mirrors `highestBid?` in `Obend/Judge/Clearing.lean`.
pub fn highest_bid(orders: &[LimitOrder]) -> Option<&LimitOrder> {
    orders
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
        })
}

/// Mirrors `lowestAsk?` in `Obend/Judge/Clearing.lean`.
pub fn lowest_ask(orders: &[LimitOrder]) -> Option<&LimitOrder> {
    orders
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
        })
}

/// Mirrors `hasCrossingPair` in `Obend/Judge/Clearing.lean`.
pub fn has_crossing_pair(orders: &[LimitOrder]) -> bool {
    match (highest_bid(orders), lowest_ask(orders)) {
        (Some(b_max), Some(a_min)) => {
            (a_min.total as u128) * (b_max.qty as u128)
                <= (b_max.total as u128) * (a_min.qty as u128)
        }
        _ => false,
    }
}

/// Mirrors `priceInCrossingInterval` in `Obend/Judge/Clearing.lean`.
pub fn price_in_crossing_interval(orders: &[LimitOrder], price: u64) -> bool {
    match (highest_bid(orders), lowest_ask(orders)) {
        (Some(b_max), Some(a_min)) => {
            if (a_min.total as u128) * (b_max.qty as u128)
                <= (b_max.total as u128) * (a_min.qty as u128)
            {
                a_min.crosses(price) && b_max.crosses(price)
            } else {
                true
            }
        }
        _ => true,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResourceTransfer {
    pub source: String,
    pub destination: String,
    pub asset: String,
    pub amount: u64,
}

/// Mirrors `netFlow` in `Obend/Judge/Clearing.lean`.
pub fn net_flow(transfers: &[ResourceTransfer], account: &str, asset: &str) -> i64 {
    transfers
        .iter()
        .map(|t| {
            let inflow = if t.destination == account && t.asset == asset {
                t.amount as i64
            } else {
                0
            };
            let outflow = if t.source == account && t.asset == asset {
                t.amount as i64
            } else {
                0
            };
            inflow - outflow
        })
        .sum()
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
    let price = match (highest_bid(orders), lowest_ask(orders)) {
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
    /// Mirror all 13 checks of `Obend.Judge.Clearing.judge` (`Obend/Judge/Clearing.lean` lines 136-196)
    /// and verify the resulting receipt digest via `ObendSession` FFI.
    pub fn verify_with_kernel(
        &self,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<bool, ObendError> {
        // 1. marketMalformed (`m.currency = m.goods`)
        if self.schema != "drex-clearing@1" || self.currency == self.goods {
            return Ok(false);
        }
        // 2. foreignAsset (`t.asset != m.currency && t.asset != m.goods`)
        if self
            .transfers
            .iter()
            .any(|t| t.asset != self.currency && t.asset != self.goods)
        {
            return Ok(false);
        }
        // 3. notAnOrder (`!isOrderAccount orders t.source || !isOrderAccount orders t.destination`)
        let is_order_account = |acct: &str| orders.iter().any(|o| o.account == acct);
        if self
            .transfers
            .iter()
            .any(|t| !is_order_account(&t.source) || !is_order_account(&t.destination))
        {
            return Ok(false);
        }
        // 4. invalidPrice (`!priceInCrossingInterval orders c.price`)
        if !price_in_crossing_interval(orders, self.price) {
            return Ok(false);
        }
        // 5. slackCount (`c.slacks.length != orders.length`)
        if self.slacks.len() != orders.len() || self.fills.len() != orders.len() {
            return Ok(false);
        }

        // Compute `Order.fill` and `Order.paid` from `self.transfers` (`Obend/Judge/Clearing.lean` lines 99-112)
        let order_fill = |o: &LimitOrder| -> i64 {
            let nf = net_flow(&self.transfers, &o.account, &self.goods);
            match o.side {
                OrderSide::Bid => nf,
                OrderSide::Ask => -nf,
            }
        };
        let order_paid = |o: &LimitOrder| -> i64 {
            let nf = net_flow(&self.transfers, &o.account, &self.currency);
            match o.side {
                OrderSide::Bid => -nf,
                OrderSide::Ask => nf,
            }
        };

        // 6. notUniform (`o.paid m transfers != c.price * o.fill m transfers`)
        for (i, o) in orders.iter().enumerate() {
            let f = order_fill(o);
            let paid = order_paid(o);
            if f != (self.fills[i] as i64) || paid != (self.price as i64) * f {
                return Ok(false);
            }
        }

        let dual_diff = self.potentials.1 - self.potentials.0;
        let mut obj_vol = 0i64;
        let mut dual_cap = 0i64;
        let mut signed_flow = 0i64;

        for (i, o) in orders.iter().enumerate() {
            let f = order_fill(o);
            let cap = if o.crosses(self.price) { o.qty as i64 } else { 0 };
            // 7. negativeFill / capacityExceeded
            if f < 0 || f > cap {
                return Ok(false);
            }
            let s = self.slacks[i];
            // 8. negativeSlack / dualInfeasible
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

        // 9. nonConserving (`finSum ... != 0`)
        if signed_flow != 0 {
            return Ok(false);
        }
        // 10. uncertified (`gap <= m.epsilon`)
        let gap = dual_cap - obj_vol;
        if obj_vol != self.objective_volume
            || dual_cap != self.dual_capacity
            || gap != self.duality_gap
            || gap > (self.epsilon as i64)
        {
            return Ok(false);
        }
        // 11. unservedCrossing (`objVol == 0 && hasCrossingPair orders`)
        if obj_vol == 0 && has_crossing_pair(orders) {
            return Ok(false);
        }

        let expected_digest = cshake256_domain(
            b"drex-clearing@1",
            &self.price.to_be_bytes(),
            &self.objective_volume.to_be_bytes(),
        );
        if self.digest != expected_digest {
            return Ok(false);
        }

        // Propose and commit the clearing turn via ObendSession FFI, then verify the 32-byte receipt
        let cert_json = serde_json::to_vec(self).unwrap_or_default();
        let tid = session.propose_turn(&cert_json)?;
        session.commit_turn(&tid)?;
        session.verify_receipt(&self.digest)
    }
}

// ============================================================================
// 5. Verified FFI Transition Delegation (`VerifiedEpochBridge`, `SimplexState`,
//    `SimplexCert`, `ClearingReceipt`, `FogOfWar`, `VerifiedNodeTransition`)
// ============================================================================

/// Composite Simplex BFT certificate (`PropCert`, `SkipCert`, `FinCert`) cryptographically
/// bound to a Lean 4 FFI receipt (`receipt_bytes` + `state_digest`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplexCert {
    pub view: u64,
    pub height: u64,
    pub block_hash: [u8; 32],
    pub prop_cert: Option<PropCert>,
    pub skip_cert: Option<SkipCert>,
    pub fin_cert: Option<FinCert>,
    pub receipt_bytes: Vec<u8>,
    pub state_digest: [u8; 32],
}

impl SimplexCert {
    /// Compute the canonical domain-separated `state_digest` binding `(view, height, block_hash, vault_root, receipt_bytes)`.
    pub fn compute_state_digest(
        view: u64,
        height: u64,
        block_hash: &[u8; 32],
        vault_root: &[u8; 32],
        receipt_bytes: &[u8],
    ) -> [u8; 32] {
        let mut header = Vec::with_capacity(8 + 8 + 32 + 32);
        header.extend_from_slice(&view.to_be_bytes());
        header.extend_from_slice(&height.to_be_bytes());
        header.extend_from_slice(block_hash);
        header.extend_from_slice(vault_root);
        cshake256_domain(b"obend.simplex.ffi.cert", &header, receipt_bytes)
    }

    /// Verify the BFT certificate quorum/leader signatures, receipt binding, and Lean FFI receipt validity.
    pub fn verify_with_session(
        &self,
        total_parties: usize,
        quorum_size: usize,
        vault_root: &[u8; 32],
        session: &mut ObendSession,
    ) -> Result<bool, NodeError> {
        if self.receipt_bytes.len() < 32 {
            return Ok(false);
        }
        if let Some(prop) = &self.prop_cert {
            if prop.view != self.view
                || prop.height != self.height
                || prop.block_hash != self.block_hash
                || !prop.verify(total_parties)
            {
                return Ok(false);
            }
        }
        if let Some(skip) = &self.skip_cert {
            if !skip.verify(quorum_size) {
                return Ok(false);
            }
        }
        if let Some(fin) = &self.fin_cert {
            if fin.view != self.view
                || fin.block_hash != self.block_hash
                || !fin.verify(quorum_size)
            {
                return Ok(false);
            }
        } else if self.skip_cert.is_none() {
            return Ok(false);
        }

        let expected_digest = Self::compute_state_digest(
            self.view,
            self.height,
            &self.block_hash,
            vault_root,
            &self.receipt_bytes,
        );
        if self.state_digest != expected_digest {
            return Ok(false);
        }

        // Verify the embedded 32-byte Lean FFI receipt prefix and the bound state_digest
        let ffi_receipt_ok = session
            .verify_receipt(&self.receipt_bytes[..32])
            .map_err(NodeError::Ffi)?;
        let ffi_digest_ok = session
            .verify_receipt(&self.state_digest)
            .map_err(NodeError::Ffi)?;
        Ok(ffi_receipt_ok && ffi_digest_ok)
    }
}

/// Verified DREX clearing + Fog-of-War projection receipt bound to a Lean FFI session receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClearingReceipt {
    pub certificate: DrexClearingCertificate,
    pub multiproof: BlindedVaultMultiProof,
    pub receipt_bytes: Vec<u8>,
    pub state_digest: [u8; 32],
}

impl ClearingReceipt {
    /// Compute canonical `state_digest` binding `(certificate.digest, multiproof.unredacted_root, receipt_bytes)`.
    pub fn compute_state_digest(
        cert_digest: &[u8; 32],
        unredacted_root: &[u8; 32],
        receipt_bytes: &[u8],
    ) -> [u8; 32] {
        let mut left = Vec::with_capacity(64);
        left.extend_from_slice(cert_digest);
        left.extend_from_slice(unredacted_root);
        cshake256_domain(b"obend.clearing.ffi.receipt", &left, receipt_bytes)
    }

    /// Verify the clearing certificate, Fog-of-War multiproof, and bound Lean FFI receipt.
    pub fn verify_with_session(
        &self,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<bool, NodeError> {
        if self.receipt_bytes.len() < 32 {
            return Ok(false);
        }
        if !self.multiproof.verify_stranger() {
            return Ok(false);
        }
        if !self
            .multiproof
            .verify_via_ffi(session)
            .map_err(NodeError::Ffi)?
        {
            return Ok(false);
        }
        if !self
            .certificate
            .verify_with_kernel(orders, session)
            .map_err(NodeError::Ffi)?
        {
            return Ok(false);
        }
        let expected_digest = Self::compute_state_digest(
            &self.certificate.digest,
            &self.multiproof.unredacted_root,
            &self.receipt_bytes,
        );
        if self.state_digest != expected_digest {
            return Ok(false);
        }
        let ffi_receipt_ok = session
            .verify_receipt(&self.receipt_bytes[..32])
            .map_err(NodeError::Ffi)?;
        let ffi_state_ok = session
            .verify_receipt(&self.state_digest)
            .map_err(NodeError::Ffi)?;
        Ok(ffi_receipt_ok && ffi_state_ok)
    }
}

/// Fog-of-War blinded vault state and FFI-verified clearing coordinator.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FogOfWar {
    pub cells: Vec<VaultCellRecord>,
    pub viewer_caps: Vec<IpcAuth>,
}

impl FogOfWar {
    pub fn new(cells: Vec<VaultCellRecord>, viewer_caps: Vec<IpcAuth>) -> Self {
        Self { cells, viewer_caps }
    }

    pub fn project(&self) -> BlindedVaultMultiProof {
        BlindedVaultMultiProof::generate(&self.cells, &self.viewer_caps)
    }

    pub fn state_root(&self) -> [u8; 32] {
        let leaves: Vec<[u8; 32]> = self.cells.iter().map(|c| c.leaf_hash()).collect();
        merkle_root_from_leaves(&leaves)
    }

    /// Execute a Mandate-authorized VaultTurn and DREX clearing batch through `ObendSession`
    /// (`eval_cell` -> `propose_turn` -> `commit_turn` -> `verify_receipt`), returning a `ClearingReceipt`.
    pub fn step_with_verified_session(
        &mut self,
        mandate: &Mandate,
        turn: &VaultTurn,
        currency: &str,
        goods: &str,
        epsilon: u64,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<ClearingReceipt, NodeError> {
        if turn.has_duplicate_write_slots() {
            return Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot {
                agent: turn.agent.clone(),
            }));
        }
        mandate.check_turn(turn).map_err(NodeError::Sandbox)?;

        let mut cell_eval_accum = Vec::new();
        for (slot_id, payload) in &turn.write_slots {
            let mut cell_input = Vec::with_capacity(8 + payload.len());
            cell_input.extend_from_slice(&slot_id.to_be_bytes());
            cell_input.extend_from_slice(payload);
            let eval_out = session.eval_cell(&cell_input).map_err(NodeError::Ffi)?;
            if eval_out.is_empty() {
                return Err(NodeError::ConsensusVerification(
                    "ObendSession::eval_cell returned empty output".to_string(),
                ));
            }
            cell_eval_accum.extend_from_slice(&eval_out);

            if let Some(cell) = self.cells.iter_mut().find(|c| c.id == *slot_id) {
                cell.content = payload.clone();
            } else {
                self.cells.push(VaultCellRecord {
                    id: *slot_id,
                    required: vec![IpcAuth::Read],
                    salt: cshake256_domain(
                        b"obend.vault.salt",
                        &slot_id.to_be_bytes(),
                        &turn.turn_id,
                    ),
                    content: payload.clone(),
                });
            }
        }

        let cert = solve_primal_dual_clearing(currency, goods, epsilon, orders).ok_or_else(|| {
            NodeError::ConsensusVerification("failed to solve DREX clearing batch".to_string())
        })?;
        let kernel_ok = cert
            .verify_with_kernel(orders, session)
            .map_err(NodeError::Ffi)?;
        if !kernel_ok {
            return Err(NodeError::ConsensusVerification(
                "DREX clearing certificate rejected by kernel FFI".to_string(),
            ));
        }

        let turn_bytes = serde_json::to_vec(turn).unwrap_or_default();
        let turn_receipt = session.propose_turn(&turn_bytes).map_err(NodeError::Ffi)?;
        session
            .commit_turn(&turn.turn_id)
            .map_err(NodeError::Ffi)?;

        let multiproof = self.project();
        if !multiproof
            .verify_via_ffi(session)
            .map_err(NodeError::Ffi)?
        {
            return Err(NodeError::ConsensusVerification(
                "FogOfWar BlindedVaultMultiProof rejected by FFI".to_string(),
            ));
        }

        let woven = session
            .weave_cert(&cert.digest)
            .map_err(NodeError::Ffi)?;

        let mut receipt_bytes = Vec::new();
        let primary_digest = cshake256_domain(
            b"obend.clearing.ffi.primary",
            &turn_receipt,
            &[&cell_eval_accum[..], &woven[..]].concat(),
        );
        receipt_bytes.extend_from_slice(&primary_digest);
        receipt_bytes.extend_from_slice(&turn_receipt);
        receipt_bytes.extend_from_slice(&cell_eval_accum);
        receipt_bytes.extend_from_slice(&woven);

        let state_digest = ClearingReceipt::compute_state_digest(
            &cert.digest,
            &multiproof.unredacted_root,
            &receipt_bytes,
        );

        let verified = session
            .verify_receipt(&state_digest)
            .map_err(NodeError::Ffi)?;
        if !verified {
            return Err(NodeError::ConsensusVerification(
                "ObendSession::verify_receipt rejected ClearingReceipt state_digest".to_string(),
            ));
        }

        Ok(ClearingReceipt {
            certificate: cert,
            multiproof,
            receipt_bytes,
            state_digest,
        })
    }
}

impl Mandate {
    /// Delegate a Mandate-checked turn and DREX clearing step through `FogOfWar::step_with_verified_session`.
    pub fn step_with_verified_session(
        &self,
        fog: &mut FogOfWar,
        turn: &VaultTurn,
        currency: &str,
        goods: &str,
        epsilon: u64,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<ClearingReceipt, NodeError> {
        fog.step_with_verified_session(self, turn, currency, goods, epsilon, orders, session)
    }
}

/// Verified consensus view & clearing transition output produced by `SimplexState::step_with_verified_session`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifiedNodeTransition {
    pub prior_view: u64,
    pub next_view: u64,
    pub height: u64,
    pub post_vault_root: [u8; 32],
    pub simplex_cert: SimplexCert,
    pub clearing_receipt: Option<ClearingReceipt>,
    pub receipt_bytes: Vec<u8>,
    pub state_digest: [u8; 32],
}

impl VerifiedNodeTransition {
    /// Compute canonical transition `state_digest` over `(simplex_cert.state_digest, clearing_digest, receipt_bytes)`.
    pub fn compute_state_digest(
        simplex_state_digest: &[u8; 32],
        clearing_state_digest: Option<&[u8; 32]>,
        receipt_bytes: &[u8],
    ) -> [u8; 32] {
        let mut left = Vec::with_capacity(64);
        left.extend_from_slice(simplex_state_digest);
        if let Some(cd) = clearing_state_digest {
            left.extend_from_slice(cd);
        } else {
            left.extend_from_slice(&[0u8; 32]);
        }
        cshake256_domain(b"obend.node.verified_transition", &left, receipt_bytes)
    }

    /// Re-verify the entire transition (SimplexCert, optional ClearingReceipt, and FFI receipt bindings).
    pub fn verify_with_session(
        &self,
        total_parties: usize,
        quorum_size: usize,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<bool, NodeError> {
        if self.receipt_bytes.len() < 32
            || self.next_view <= self.prior_view
            || self.receipt_bytes != self.simplex_cert.receipt_bytes
        {
            return Ok(false);
        }
        if !self.simplex_cert.verify_with_session(
            total_parties,
            quorum_size,
            &self.post_vault_root,
            session,
        )? {
            return Ok(false);
        }
        if let Some(clearing) = &self.clearing_receipt {
            if !clearing.verify_with_session(orders, session)? {
                return Ok(false);
            }
        }
        let expected_digest = Self::compute_state_digest(
            &self.simplex_cert.state_digest,
            self.clearing_receipt.as_ref().map(|c| &c.state_digest),
            &self.receipt_bytes,
        );
        if self.state_digest != expected_digest {
            return Ok(false);
        }
        session
            .verify_receipt(&self.state_digest)
            .map_err(NodeError::Ffi)
    }
}

/// Deterministic Simplex BFT state machine with verified Lean FFI transition delegation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplexState {
    pub view: u64,
    pub height: u64,
    pub total_parties: usize,
    pub fault_tolerance: usize,
    pub parent_hash: [u8; 32],
    pub vault_cells: Vec<VaultCellRecord>,
    pub state_digest: [u8; 32],
    pub last_receipt_bytes: Vec<u8>,
}

impl SimplexState {
    pub fn new(
        total_parties: usize,
        fault_tolerance: usize,
        vault_cells: Vec<VaultCellRecord>,
    ) -> Self {
        let leaves: Vec<[u8; 32]> = vault_cells.iter().map(|c| c.leaf_hash()).collect();
        let state_digest = merkle_root_from_leaves(&leaves);
        Self {
            view: 0,
            height: 0,
            total_parties,
            fault_tolerance,
            parent_hash: [0u8; 32],
            vault_cells,
            state_digest,
            last_receipt_bytes: Vec::new(),
        }
    }

    pub fn quorum_size(&self) -> usize {
        2 * self.fault_tolerance + 1
    }

    pub fn vault_root(&self) -> [u8; 32] {
        let leaves: Vec<[u8; 32]> = self.vault_cells.iter().map(|c| c.leaf_hash()).collect();
        merkle_root_from_leaves(&leaves)
    }

    /// Execute a consensus view transition and optional DREX clearing batch through `ObendSession`
    /// (`eval_cell` -> `propose_turn` -> `commit_turn` -> `verify_receipt`), binding the Lean FFI
    /// receipt (`receipt_bytes` + `state_digest`) into `SimplexCert` and `ClearingReceipt`.
    pub fn step_with_verified_session(
        &mut self,
        validators: &[ValidatorKeypair],
        mandate: Option<&Mandate>,
        turn: &VaultTurn,
        drex_batch: Option<(&str, &str, u64, &[LimitOrder])>,
        session: &mut ObendSession,
    ) -> Result<VerifiedNodeTransition, NodeError> {
        if self.total_parties == 0 || validators.len() < self.total_parties {
            return Err(NodeError::ConsensusVerification(
                "insufficient validator keypairs for SimplexState transition".to_string(),
            ));
        }
        if turn.has_duplicate_write_slots() {
            return Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot {
                agent: turn.agent.clone(),
            }));
        }
        if let Some(m) = mandate {
            m.check_turn(turn).map_err(NodeError::Sandbox)?;
        }

        // 1. Evaluate every cell update via `ObendSession::eval_cell`
        let mut evaluated_cells_bytes = Vec::new();
        let mut next_cells = self.vault_cells.clone();
        for (slot_id, content) in &turn.write_slots {
            let mut cell_input = Vec::with_capacity(8 + content.len());
            cell_input.extend_from_slice(&slot_id.to_be_bytes());
            cell_input.extend_from_slice(content);
            let eval_res = session.eval_cell(&cell_input).map_err(NodeError::Ffi)?;
            if eval_res.is_empty() {
                return Err(NodeError::ConsensusVerification(
                    "ObendSession::eval_cell returned empty receipt".to_string(),
                ));
            }
            evaluated_cells_bytes.extend_from_slice(&eval_res);

            if let Some(existing) = next_cells.iter_mut().find(|c| c.id == *slot_id) {
                existing.content = content.clone();
            } else {
                next_cells.push(VaultCellRecord {
                    id: *slot_id,
                    required: vec![IpcAuth::Read],
                    salt: cshake256_domain(
                        b"obend.vault.salt",
                        &slot_id.to_be_bytes(),
                        &turn.turn_id,
                    ),
                    content: content.clone(),
                });
            }
        }

        //If read-only turn, still evaluate cell state over the first read slot via FFI
        if turn.write_slots.is_empty() {
            let probe_bytes = serde_json::to_vec(turn).unwrap_or_else(|_| b"readonly-turn".to_vec());
            let eval_res = session.eval_cell(&probe_bytes).map_err(NodeError::Ffi)?;
            evaluated_cells_bytes.extend_from_slice(&eval_res);
        }

        // 2. Propose and commit the turn via `ObendSession::propose_turn` & `commit_turn`
        let turn_payload = serde_json::to_vec(turn).unwrap_or_default();
        let proposed_receipt = session.propose_turn(&turn_payload).map_err(NodeError::Ffi)?;
        if proposed_receipt.is_empty() {
            return Err(NodeError::ConsensusVerification(
                "ObendSession::propose_turn returned empty receipt".to_string(),
            ));
        }
        session
            .commit_turn(&turn.turn_id)
            .map_err(NodeError::Ffi)?;

        // 3. Optional DREX clearing batch & FogOfWar multiproof
        let mut fog = FogOfWar::new(next_cells.clone(), vec![IpcAuth::Read]);
        let clearing_receipt = if let Some((currency, goods, epsilon, orders)) = drex_batch {
            if !orders.is_empty() {
                let default_mandate;
                let active_mandate = if let Some(m) = mandate {
                    m
                } else {
                    default_mandate = Mandate {
                        grantor: "kernel".to_string(),
                        holder: turn.agent.clone(),
                        target: "obend.vault".to_string(),
                        rights: vec![IpcAuth::Read, IpcAuth::Write, IpcAuth::Grant],
                        budget: u64::MAX,
                        allowed_slots: turn
                            .read_slots
                            .iter()
                            .copied()
                            .chain(turn.write_slots.iter().map(|(s, _)| *s))
                            .collect(),
                        expires_at: u64::MAX,
                        allowed_methods: None,
                    };
                    &default_mandate
                };
                Some(fog.step_with_verified_session(
                    active_mandate,
                    turn,
                    currency,
                    goods,
                    epsilon,
                    orders,
                    session,
                )?)
            } else {
                None
            }
        } else {
            None
        };

        // 4. Construct consensus view transition certificates (`PropCert` + `FinCert`)
        let prior_view = self.view;
        let next_view = self.view + 1;
        let next_height = self.height + 1;
        let leader_idx = ((next_view - 1) as usize) % self.total_parties;
        let prop_cert = PropCert::create(
            &validators[leader_idx],
            next_view,
            next_height,
            self.parent_hash,
            turn_payload,
        );
        let quorum = self.quorum_size();
        let fin_votes: Vec<SignedSimplexVote> = validators[..quorum]
            .iter()
            .map(|kp| {
                SignedSimplexVote::new(kp, next_view, SimplexVoteKind::Finalize, prop_cert.block_hash)
            })
            .collect();
        let fin_cert = FinCert {
            view: next_view,
            block_hash: prop_cert.block_hash,
            votes: fin_votes,
        };

        let woven_cert = session
            .weave_cert(&prop_cert.block_hash)
            .map_err(NodeError::Ffi)?;

        let post_leaves: Vec<[u8; 32]> = next_cells.iter().map(|c| c.leaf_hash()).collect();
        let post_vault_root = merkle_root_from_leaves(&post_leaves);

        // Build non-empty Lean FFI `receipt_bytes` (32-byte FFI commitment prefix + raw FFI artifacts)
        let receipt_head = cshake256_domain(
            b"obend.simplex.ffi.receipt_head",
            &proposed_receipt,
            &[&evaluated_cells_bytes[..], &woven_cert[..]].concat(),
        );
        let mut receipt_bytes = Vec::with_capacity(
            32 + proposed_receipt.len() + evaluated_cells_bytes.len() + woven_cert.len(),
        );
        receipt_bytes.extend_from_slice(&receipt_head);
        receipt_bytes.extend_from_slice(&proposed_receipt);
        receipt_bytes.extend_from_slice(&evaluated_cells_bytes);
        receipt_bytes.extend_from_slice(&woven_cert);

        let simplex_state_digest = SimplexCert::compute_state_digest(
            next_view,
            next_height,
            &prop_cert.block_hash,
            &post_vault_root,
            &receipt_bytes,
        );

        let simplex_cert = SimplexCert {
            view: next_view,
            height: next_height,
            block_hash: prop_cert.block_hash,
            prop_cert: Some(prop_cert.clone()),
            skip_cert: None,
            fin_cert: Some(fin_cert),
            receipt_bytes: receipt_bytes.clone(),
            state_digest: simplex_state_digest,
        };

        if !simplex_cert.verify_with_session(
            self.total_parties,
            quorum,
            &post_vault_root,
            session,
        )? {
            return Err(NodeError::ConsensusVerification(
                "SimplexCert FFI receipt verification failed".to_string(),
            ));
        }

        let state_digest = VerifiedNodeTransition::compute_state_digest(
            &simplex_cert.state_digest,
            clearing_receipt.as_ref().map(|c| &c.state_digest),
            &receipt_bytes,
        );

        if !session
            .verify_receipt(&state_digest)
            .map_err(NodeError::Ffi)?
        {
            return Err(NodeError::ConsensusVerification(
                "ObendSession::verify_receipt rejected transition state_digest".to_string(),
            ));
        }

        self.view = next_view;
        self.height = next_height;
        self.parent_hash = prop_cert.block_hash;
        self.vault_cells = next_cells;
        self.state_digest = state_digest;
        self.last_receipt_bytes = receipt_bytes.clone();

        Ok(VerifiedNodeTransition {
            prior_view,
            next_view,
            height: next_height,
            post_vault_root,
            simplex_cert,
            clearing_receipt,
            receipt_bytes,
            state_digest,
        })
    }

    /// Verify and apply an externally supplied `VerifiedNodeTransition`, rejecting any tampered FFI receipt.
    pub fn apply_verified_transition(
        &mut self,
        transition: &VerifiedNodeTransition,
        orders: &[LimitOrder],
        session: &mut ObendSession,
    ) -> Result<(), NodeError> {
        let quorum = self.quorum_size();
        let valid = transition.verify_with_session(
            self.total_parties,
            quorum,
            orders,
            session,
        )?;
        if !valid {
            return Err(NodeError::ConsensusVerification(
                "rejected tampered or invalid VerifiedNodeTransition receipt".to_string(),
            ));
        }
        self.view = transition.next_view;
        self.height = transition.height;
        self.parent_hash = transition.simplex_cert.block_hash;
        self.state_digest = transition.state_digest;
        self.last_receipt_bytes = transition.receipt_bytes.clone();
        Ok(())
    }
}

/// Stateless coordinator bridging consensus epochs, Fog-of-War vaults, and DREX clearing batches
/// through a verified `ObendSession`.
pub struct VerifiedEpochBridge;

impl VerifiedEpochBridge {
    pub fn step_with_verified_session(
        state: &mut SimplexState,
        validators: &[ValidatorKeypair],
        mandate: Option<&Mandate>,
        turn: &VaultTurn,
        drex_batch: Option<(&str, &str, u64, &[LimitOrder])>,
        session: &mut ObendSession,
    ) -> Result<VerifiedNodeTransition, NodeError> {
        state.step_with_verified_session(validators, mandate, turn, drex_batch, session)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha256_nist_vector_and_keccak_sponge() {
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

        // NIST FIPS 202 SHAKE256("", 256) test vector:
        // 46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f
        let shake_empty = keccak256_sponge(0x1F, &[]);
        let expected_shake: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
            0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
            0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
            0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f,
        ];
        assert_eq!(shake_empty, expected_shake);
    }

    #[test]
    fn test_ed25519_unforgeable_without_secret_key() {
        let kp = ValidatorKeypair::from_seed(0, b"validator-0-seed");
        let msg = b"propose-block-height-42";
        let sig = kp.sign(msg);
        assert!(ValidatorKeypair::verify(&kp.public_key, msg, &sig));

        // 1. Attempting the old forgery attack (choosing arbitrary R and hashing public_key + R + msg)
        // must be strictly rejected because the Curve25519 discrete log of A = [a]B is unknown:
        let fake_r = EdwardsPoint::basepoint().encode();
        let fake_s = cshake256_domain(
            b"obend.ed25519.s",
            &kp.public_key,
            &[&fake_r[..], &msg[..]].concat(),
        );
        let mut forged_sig = [0u8; 64];
        forged_sig[..32].copy_from_slice(&fake_r);
        forged_sig[32..].copy_from_slice(&fake_s);
        assert!(!ValidatorKeypair::verify(&kp.public_key, msg, &forged_sig));

        // 2. Wrong message or wrong public key must fail verification
        assert!(!ValidatorKeypair::verify(&kp.public_key, b"tampered-msg", &sig));
        let other_kp = ValidatorKeypair::from_seed(1, b"validator-1-seed");
        assert!(!ValidatorKeypair::verify(&other_kp.public_key, msg, &sig));
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

        // Negative pole 1: corrupting dual slacks to violate zero duality gap is refused
        let mut bad_slacks = cert.clone();
        bad_slacks.slacks[2] = 0;
        assert!(!bad_slacks
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));

        // Negative pole 2: wiping or tampering with `transfers` while keeping `fills` is refused (`notUniform` / `Order.fill`)
        let mut empty_transfers = cert.clone();
        empty_transfers.transfers.clear();
        assert!(!empty_transfers
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));

        // Negative pole 3: foreign asset posting is refused (`foreignAsset`)
        let mut foreign_asset = cert.clone();
        foreign_asset.transfers.push(ResourceTransfer {
            source: "alice_buyer".to_string(),
            destination: "carol_seller".to_string(),
            asset: "DOGE".to_string(),
            amount: 1,
        });
        assert!(!foreign_asset
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));

        // Negative pole 4: non-order account posting is refused (`notAnOrder`)
        let mut non_order = cert.clone();
        non_order.transfers.push(ResourceTransfer {
            source: "mallory_outsider".to_string(),
            destination: "carol_seller".to_string(),
            asset: "USDC".to_string(),
            amount: 1,
        });
        assert!(!non_order
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));

        // Negative pole 5: unserved crossing (zero volume when a crossing pair exists) is refused (`unservedCrossing`)
        let unserved = DrexClearingCertificate {
            schema: "drex-clearing@1".to_string(),
            currency: "USDC".to_string(),
            goods: "WAFER".to_string(),
            epsilon: 100,
            price: 110,
            potentials: (1, 0),
            slacks: vec![2, 2, 0],
            fills: vec![0, 0, 0],
            transfers: vec![],
            objective_volume: 0,
            dual_capacity: 30,
            duality_gap: 30,
            digest: cshake256_domain(b"drex-clearing@1", &110u64.to_be_bytes(), &0i64.to_be_bytes()),
        };
        assert!(!unserved
            .verify_with_kernel(&orders, &mut session)
            .expect("kernel check"));
    }

    fn sample_genesis_cells() -> Vec<VaultCellRecord> {
        vec![
            VaultCellRecord {
                id: 1,
                required: vec![IpcAuth::Read],
                salt: [0x11; 32],
                content: b"slot-1-genesis".to_vec(),
            },
            VaultCellRecord {
                id: 2,
                required: vec![IpcAuth::Read],
                salt: [0x22; 32],
                content: b"slot-2-genesis".to_vec(),
            },
            VaultCellRecord {
                id: 3,
                required: vec![IpcAuth::Read, IpcAuth::Control],
                salt: [0x33; 32],
                content: b"slot-3-dark-pool".to_vec(),
            },
        ]
    }

    #[test]
    fn test_ws32_e2e_multi_validator_networked_simplex_bft_tcp_and_udp() {
        for transport in [TransportProtocol::Tcp, TransportProtocol::Udp] {
            let mut cluster =
                SimplexCluster::with_transport(4, 1, sample_genesis_cells(), transport)
                    .expect("spawn 4-validator cluster");

            // Verify all 4 nodes bound real ephemeral 127.0.0.1 ports
            for node in &cluster.nodes {
                assert!(node.tcp_addr.ip().is_loopback());
                assert!(node.udp_addr.ip().is_loopback());
                assert_ne!(node.tcp_addr.port(), 0);
                assert_ne!(node.udp_addr.port(), 0);
            }

            // Stage a contended turn and run height 1 over real loopback sockets
            let turn_h1 = VaultTurn::new(
                [0x01; 32],
                "alice",
                vec![1],
                vec![(1, b"slot-1-height-1".to_vec())],
            );
            cluster
                .stage_contended_or_inflight_turn(turn_h1.clone())
                .expect("stage turn h1");

            let blk1 = cluster.run_simplex_block().expect("finalize block 1");
            assert_eq!(blk1.height, 1);
            assert_eq!(blk1.view, 1);
            assert!(blk1.fin_cert.verify(3));
            assert!(blk1.multiproof.verify_stranger());

            // Stage another turn and run height 2 (leader rotates to validator 1)
            let turn_h2 = VaultTurn::new(
                [0x02; 32],
                "bob",
                vec![2],
                vec![(2, b"slot-2-height-2".to_vec())],
            );
            cluster
                .stage_contended_or_inflight_turn(turn_h2.clone())
                .expect("stage turn h2");

            let blk2 = cluster.run_simplex_block().expect("finalize block 2");
            assert_eq!(blk2.height, 2);
            assert_eq!(blk2.view, 2);
            assert_eq!(blk2.parent_hash, blk1.block_hash);
            assert!(blk2.fin_cert.verify(3));

            // All 4 networked validators must agree on height 2 and identical FogOfWar Merkle state root
            let root0 = cluster.nodes[0].state_root();
            for node in &cluster.nodes {
                assert_eq!(node.committed_height(), 2);
                assert_eq!(node.state_root(), root0);
                assert!(node.wire_frames_received() > 0);
                assert_eq!(
                    node.turn_tier(&turn_h1.turn_id),
                    Some(FinalityTier::QuorumFinal)
                );
                assert_eq!(
                    node.turn_tier(&turn_h2.turn_id),
                    Some(FinalityTier::QuorumFinal)
                );
            }
        }
    }

    #[test]
    fn test_ws32_e2e_byzantine_equivocation_detection_and_slashing_broadcast() {
        let mut cluster =
            SimplexCluster::new(4, 1, sample_genesis_cells()).expect("spawn 4-validator cluster");

        // Validator 1 (faulty) double-signs two conflicting block hashes in view 2 over real sockets
        let slash_receipt = cluster
            .inject_byzantine_equivocation(1, 2, [0xA1; 32], [0xB2; 32])
            .expect("detect and broadcast SlashingReceipt");

        assert_eq!(slash_receipt.offender_id, 1);
        assert_eq!(slash_receipt.view, 2);
        assert!(slash_receipt.verify());

        // Every honest validator (0, 2, 3) must hold the verified SlashingReceipt and mark validator 1 slashed
        for &honest_id in &[0usize, 2, 3] {
            let receipts = cluster.nodes[honest_id].slashing_receipts();
            assert!(receipts
                .iter()
                .any(|r| r.offender_id == 1 && r.view == 2 && r.verify()));
            assert!(cluster.nodes[honest_id].slashed_validators().contains(&1));
        }

        // Block 1 (view 1, leader 0 is honest) finalizes with the 3 honest validators
        let turn1 = VaultTurn::new([0x10; 32], "alice", vec![1], vec![(1, b"post-slash-1".to_vec())]);
        cluster
            .stage_contended_or_inflight_turn(turn1)
            .expect("stage turn1");
        let blk1 = cluster.run_simplex_block().expect("finalize block 1");
        assert_eq!(blk1.height, 1);
        assert_eq!(blk1.view, 1);

        // Next view is view 2, whose leader would be validator 1 ((2 - 1) % 4 == 1), which is slashed!
        // `run_simplex_block` automatically executes a networked `SkipCert` view-change to view 3 (leader 2)
        // and finalizes block 2!
        let turn2 = VaultTurn::new([0x20; 32], "alice", vec![2], vec![(2, b"post-slash-2".to_vec())]);
        cluster
            .stage_contended_or_inflight_turn(turn2)
            .expect("stage turn2");
        let blk2 = cluster
            .run_simplex_block()
            .expect("finalize block 2 after SkipCert over slashed leader");
        assert_eq!(blk2.height, 2);
        assert_eq!(blk2.view, 3);
        assert!(blk2.fin_cert.verify(3));

        // Verify all honest nodes recorded the SkipCert for view 2
        for &honest_id in &[0usize, 2, 3] {
            let skips = cluster.nodes[honest_id].skip_certs();
            assert!(skips.iter().any(|s| s.view == 2 && s.verify(3)));
        }
    }

    #[test]
    fn test_ws32_e2e_tier1_disjoint_fast_path_vs_tier2_contended_drex_clearing() {
        let genesis = sample_genesis_cells();
        let mut cluster =
            SimplexCluster::new(4, 1, genesis.clone()).expect("spawn 4-validator cluster");

        // 1. Disjoint turns touching slot 1 and slot 2 commute (`disjoint_turns_commute`)
        let t_disjoint_a = VaultTurn::new(
            [0xD1; 32],
            "agent_a",
            vec![1],
            vec![(1, b"fast-slot-1".to_vec())],
        );
        let t_disjoint_b = VaultTurn::new(
            [0xD2; 32],
            "agent_b",
            vec![2],
            vec![(2, b"fast-slot-2".to_vec())],
        );
        assert!(disjoint_turns_commute(&t_disjoint_a, &t_disjoint_b));
        assert!(verify_turns_commute_on_vault(
            &genesis,
            &t_disjoint_a,
            &t_disjoint_b
        ));

        // Submit `t_disjoint_a` -> commits immediately on Tier 1 Fast-Path at block height 0!
        let out_a = cluster
            .submit_turn(t_disjoint_a.clone())
            .expect("submit disjoint turn A");
        match out_a {
            TurnSubmissionOutcome::FastPathCommitted { cert, tier } => {
                assert_eq!(tier, FinalityTier::AttestedFastPath);
                assert!(cert.verify(3));
            }
            other => panic!("expected FastPathCommitted, got {other:?}"),
        }
        assert_eq!(cluster.nodes[0].committed_height(), 0);
        assert_eq!(
            cluster.nodes[0].turn_tier(&t_disjoint_a.turn_id),
            Some(FinalityTier::AttestedFastPath)
        );

        // 2. Contended turns both writing to slot 1 DO NOT commute (`!disjoint_turns_commute`)
        let t_contended_1 = VaultTurn::new(
            [0xC1; 32],
            "trader_1",
            vec![1],
            vec![(1, b"contended-slot-1-v1".to_vec())],
        );
        let t_contended_2 = VaultTurn::new(
            [0xC2; 32],
            "trader_2",
            vec![1],
            vec![(1, b"contended-slot-1-v2".to_vec())],
        );
        assert!(!disjoint_turns_commute(&t_contended_1, &t_contended_2));

        // Submit concurrent batch with [t_disjoint_b, t_contended_1, t_contended_2]:
        // `t_disjoint_b` (slot 2) takes Tier 1 Fast-Path, while `t_contended_1` & `t_contended_2` (slot 1)
        // are routed to Tier 2 Contended Simplex BFT mempool!
        let batch_outcomes = cluster
            .submit_concurrent_batch(vec![
                t_disjoint_b.clone(),
                t_contended_1.clone(),
                t_contended_2.clone(),
            ])
            .expect("submit concurrent batch");
        assert!(matches!(
            batch_outcomes[0],
            TurnSubmissionOutcome::FastPathCommitted {
                tier: FinalityTier::AttestedFastPath,
                ..
            }
        ));
        assert!(matches!(
            batch_outcomes[1],
            TurnSubmissionOutcome::RoutedToContendedSimplex {
                tier: FinalityTier::Speculative,
                ..
            }
        ));
        assert!(matches!(
            batch_outcomes[2],
            TurnSubmissionOutcome::RoutedToContendedSimplex {
                tier: FinalityTier::Speculative,
                ..
            }
        ));

        // Submit `drex-clearing@1` limit orders into the Tier 2 mempool
        cluster.set_drex_market("USDC", "WAFER", 0);
        cluster.submit_drex_order(LimitOrder {
            account: "alice_buyer".to_string(),
            side: OrderSide::Bid,
            qty: 10,
            total: 1200,
        });
        cluster.submit_drex_order(LimitOrder {
            account: "bob_buyer".to_string(),
            side: OrderSide::Bid,
            qty: 5,
            total: 550,
        });
        cluster.submit_drex_order(LimitOrder {
            account: "carol_seller".to_string(),
            side: OrderSide::Ask,
            qty: 12,
            total: 1200,
        });

        // Finalize Tier 2 Simplex BFT block -> executes contended turns + `solve_drex_batch` + FFI verification
        let blk = cluster
            .run_simplex_block()
            .expect("finalize contended Simplex block with DREX clearing");
        assert_eq!(blk.height, 1);
        assert!(blk.clearing_kernel_verified);
        let clearing_cert = blk.clearing_cert.expect("DrexClearingCertificate present");
        assert_eq!(clearing_cert.price, 110);
        assert_eq!(clearing_cert.objective_volume, 24);
        assert_eq!(clearing_cert.duality_gap, 0);

        for node in &cluster.nodes {
            assert_eq!(
                node.turn_tier(&t_contended_1.turn_id),
                Some(FinalityTier::QuorumFinal)
            );
            assert_eq!(
                node.turn_tier(&t_contended_2.turn_id),
                Some(FinalityTier::QuorumFinal)
            );
        }
    }

    #[test]
    fn test_ws32_e2e_sandboxed_grain_powerbox_confinement_enforcement() {
        let tmp_dir =
            std::env::temp_dir().join(format!("obend_ws32_grain_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp_dir);
        let _ = std::fs::create_dir_all(&tmp_dir);

        let mut powerbox = Powerbox::new("obend.vault.prod");
        // Root mandate for `root_agent` covering slots [1, 2] with budget 100
        let root_mandate = Mandate {
            grantor: "kernel".to_string(),
            holder: "root_agent".to_string(),
            target: "obend.vault.prod".to_string(),
            rights: vec![IpcAuth::Read, IpcAuth::Write, IpcAuth::Grant],
            budget: 100,
            allowed_slots: vec![1, 2],
            expires_at: 10,
            allowed_methods: Some(vec![0, 1]),
        };
        powerbox
            .grant_mandate(root_mandate.clone())
            .expect("grant root mandate");

        // Sub-delegate a strictly attenuated mandate to `grain_worker` covering ONLY slot [1] and budget 10
        let child_mandate = powerbox
            .delegate(
                "root_agent",
                "grain_worker",
                &[IpcAuth::Read, IpcAuth::Write],
                10,
                &[1, 3], // Slot 3 is NOT in parent's allowed_slots [1, 2], so intersection yields only [1]!
                5,
                Some(vec![0]),
            )
            .expect("delegate child mandate");
        assert!(child_mandate.attenuates(&root_mandate));
        assert_eq!(child_mandate.allowed_slots, vec![1]);
        assert_eq!(child_mandate.budget, 10);

        let mut runner = SandboxRunner::new(powerbox);
        let grain_cfg = GrainConfig::strict_for_agent("grain_worker", tmp_dir.clone());
        assert!(grain_cfg
            .bwrap_flags()
            .contains(&"--unshare-net".to_string()));
        let gate_status = runner
            .register_grain("grain_worker", grain_cfg)
            .expect("register strict grain");
        assert_eq!(gate_status, GateStatus::Started);

        let mut cluster =
            SimplexCluster::new(4, 1, sample_genesis_cells()).expect("spawn 4-validator cluster");
        cluster.configure_sandbox(runner);

        // 1. Authorized turn on slot 1 succeeds and commits on Tier 1 Fast-Path
        let authorized_turn = VaultTurn::new(
            [0xA1; 32],
            "grain_worker",
            vec![1],
            vec![(1, b"authorized-grain-write".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read, IpcAuth::Write], 4, 2, 0);

        let ok_outcome = cluster
            .submit_turn(authorized_turn)
            .expect("authorized grain turn should succeed");
        assert!(matches!(
            ok_outcome,
            TurnSubmissionOutcome::FastPathCommitted { .. }
        ));

        // 2. Unauthorized slot access (attempting to read/write slot 2 or dark-pool slot 3) is REJECTED
        // by `obend-sandbox` Powerbox before admission and fences the Grain LaunchGate!
        let unauthorized_slot_turn = VaultTurn::new(
            [0xB1; 32],
            "grain_worker",
            vec![3],
            vec![(3, b"exfiltrate-dark-pool".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read, IpcAuth::Write], 2, 2, 0);

        let err = cluster
            .submit_turn(unauthorized_slot_turn)
            .expect_err("unauthorized slot access must be rejected");
        match err {
            NodeError::Sandbox(SandboxViolation::UnauthorizedSlotAccess { agent, slot_id }) => {
                assert_eq!(agent, "grain_worker");
                assert_eq!(slot_id, 3);
            }
            other => panic!("expected UnauthorizedSlotAccess, got {other:?}"),
        }

        // Verify the grain's LaunchGate was automatically fenced upon violation
        let sbx = cluster.sandbox.as_ref().unwrap();
        assert_eq!(
            sbx.grain_gate_status("grain_worker"),
            Some(GateStatus::Fenced)
        );
        assert_eq!(sbx.rejected_turns.len(), 1);

        // 3. Subsequent turn from the fenced grain is rejected immediately by LaunchGate
        let post_fence_turn = VaultTurn::new(
            [0xC1; 32],
            "grain_worker",
            vec![1],
            vec![(1, b"retry-after-fence".to_vec())],
        );
        let fence_err = cluster
            .submit_turn(post_fence_turn)
            .expect_err("fenced grain must not admit turns");
        assert!(matches!(
            fence_err,
            NodeError::Sandbox(SandboxViolation::GateNotOperational { .. })
        ));

        let _ = std::fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_ws32_e2e_fold_collapse_epoch_checkpoint_compression() {
        let mut cluster =
            SimplexCluster::new(4, 1, sample_genesis_cells()).expect("spawn 4-validator cluster");
        let initial_root = cluster.nodes[0].state_root();

        // Height 1: Contended VaultTurn + DREX batch clearing
        let t1 = VaultTurn::new([0xE1; 32], "alice", vec![1], vec![(1, b"epoch-h1".to_vec())]);
        cluster
            .stage_contended_or_inflight_turn(t1.clone())
            .expect("stage t1");
        cluster.submit_drex_order(LimitOrder {
            account: "buyer_1".to_string(),
            side: OrderSide::Bid,
            qty: 8,
            total: 800, // price 100
        });
        cluster.submit_drex_order(LimitOrder {
            account: "seller_1".to_string(),
            side: OrderSide::Ask,
            qty: 8,
            total: 800, // price 100
        });
        let b1 = cluster.run_simplex_block().expect("finalize height 1");
        assert_eq!(b1.height, 1);

        // Height 2: Empty block (simulating a heartbeat/timeout block with no turns or orders)
        // to exercise `collapseTrace_prune_empty` invariance
        let b2 = cluster.run_simplex_block().expect("finalize empty height 2");
        assert_eq!(b2.height, 2);
        assert!(b2.payload.is_empty());
        assert_eq!(b2.pre_state_root, b2.post_state_root);

        // Height 3: Contended VaultTurn + second DREX batch clearing
        let t3 = VaultTurn::new([0xE3; 32], "bob", vec![2], vec![(2, b"epoch-h3".to_vec())]);
        cluster
            .stage_contended_or_inflight_turn(t3.clone())
            .expect("stage t3");
        cluster.submit_drex_order(LimitOrder {
            account: "buyer_2".to_string(),
            side: OrderSide::Bid,
            qty: 5,
            total: 600, // price 120
        });
        cluster.submit_drex_order(LimitOrder {
            account: "seller_2".to_string(),
            side: OrderSide::Ask,
            qty: 5,
            total: 500, // price 100 -> midpoint 110
        });
        let b3 = cluster.run_simplex_block().expect("finalize height 3");
        assert_eq!(b3.height, 3);

        // Compress heights [1..=3] into a Tier 3 `CollapsedEpochReceipt` via `Fold.collapse`
        let epoch_receipt = cluster
            .collapse_epoch(1, 1, 3)
            .expect("collapse epoch [1..=3]");

        assert_eq!(epoch_receipt.epoch_id, 1);
        assert_eq!(epoch_receipt.start_height, 1);
        assert_eq!(epoch_receipt.end_height, 3);
        assert_eq!(epoch_receipt.total_block_count, 3);
        assert_eq!(epoch_receipt.active_block_count, 2);
        assert_eq!(epoch_receipt.pruned_empty_block_count, 1);
        assert_eq!(epoch_receipt.initial_state_root, initial_root);
        assert_eq!(epoch_receipt.final_state_root, b3.post_state_root);
        assert_eq!(epoch_receipt.cumulative_clearing_volume, 16 + 10);
        assert_eq!(epoch_receipt.cumulative_currency_net_flow, 0);
        assert_eq!(epoch_receipt.cumulative_goods_net_flow, 0);
        assert!(epoch_receipt.clearing_conserved);
        assert!(epoch_receipt.ffi_verified);
        assert_eq!(epoch_receipt.tier, FinalityTier::Collapsed);

        let mut session = ObendSession::new().expect("session init");
        assert!(epoch_receipt
            .verify(&mut session)
            .expect("verify collapsed epoch receipt via FFI"));

        // Tampering with cumulative_currency_net_flow or final_state_root must fail verification
        let mut tampered = epoch_receipt.clone();
        tampered.cumulative_currency_net_flow = 1;
        assert!(!tampered.verify(&mut session).expect("verify tampered"));

        // Verify all turns in the collapsed epoch were promoted to `FinalityTier::Collapsed` (Tier 3)
        for node in &cluster.nodes {
            assert_eq!(node.turn_tier(&t1.turn_id), Some(FinalityTier::Collapsed));
            assert_eq!(node.turn_tier(&t3.turn_id), Some(FinalityTier::Collapsed));
            assert_eq!(node.epoch_receipts().len(), 1);
        }
    }

    #[test]
    fn test_ws32_edge_cases_wire_tampering_duplicate_slots_and_fold_boundaries() {
        let genesis = sample_genesis_cells();
        let mut cluster =
            SimplexCluster::new(4, 1, genesis.clone()).expect("spawn 4-validator cluster");

        // 1. Duplicate write slots in a VaultTurn must be rejected by `disjoint_turns_commute` and `submit_turn`
        let dup_turn = VaultTurn::new(
            [0xDD; 32],
            "alice",
            vec![1],
            vec![(1, b"v1".to_vec()), (1, b"v2".to_vec())],
        );
        let normal_turn = VaultTurn::new([0xEE; 32], "bob", vec![2], vec![(2, b"ok".to_vec())]);
        assert!(dup_turn.has_duplicate_write_slots());
        assert!(!disjoint_turns_commute(&dup_turn, &normal_turn));
        assert!(matches!(
            cluster.submit_turn(dup_turn),
            Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot { .. }))
        ));

        // 2. Read-read on the same slot without writing commutes under Bernstein independence
        let read_only_1 = VaultTurn::new([0xF1; 32], "r1", vec![1], vec![]);
        let read_only_2 = VaultTurn::new([0xF2; 32], "r2", vec![1], vec![]);
        assert!(disjoint_turns_commute(&read_only_1, &read_only_2));

        // 3. Insecure GrainConfig (network enabled) must be rejected by `verify_strict_policy`
        let tmp_dir =
            std::env::temp_dir().join(format!("obend_ws32_edge_{}", std::process::id()));
        let mut insecure_grain = GrainConfig::strict_for_agent("bad_grain", tmp_dir.clone());
        insecure_grain.sandbox_config.allow_network = true;
        assert!(matches!(
            insecure_grain.verify_strict_policy(),
            Err(SandboxViolation::InsecureConfinementPolicy { .. })
        ));

        // 4. Mandate boundary checks: expired epoch, disallowed method, missing Write capability, budget exceeded
        let mandate = Mandate {
            grantor: "root".to_string(),
            holder: "worker".to_string(),
            target: "obend".to_string(),
            rights: vec![IpcAuth::Read], // Read-only!
            budget: 5,
            allowed_slots: vec![1],
            expires_at: 3,
            allowed_methods: Some(vec![7]),
        };
        let expired_turn =
            VaultTurn::new([0x01; 32], "worker", vec![1], vec![]).with_mandate_params(
                vec![IpcAuth::Read],
                1,
                4, // > expires_at (3)
                7,
            );
        assert!(matches!(
            mandate.check_turn(&expired_turn),
            Err(SandboxViolation::MandateExpired { .. })
        ));

        let bad_method_turn =
            VaultTurn::new([0x02; 32], "worker", vec![1], vec![]).with_mandate_params(
                vec![IpcAuth::Read],
                1,
                2,
                99, // != 7
            );
        assert!(matches!(
            mandate.check_turn(&bad_method_turn),
            Err(SandboxViolation::MethodDisallowed { .. })
        ));

        let missing_write_turn = VaultTurn::new(
            [0x03; 32],
            "worker",
            vec![1],
            vec![(1, b"illegal-write".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read], 1, 2, 7);
        assert!(matches!(
            mandate.check_turn(&missing_write_turn),
            Err(SandboxViolation::MissingCapability {
                required: IpcAuth::Write,
                ..
            })
        ));

        let over_budget_turn =
            VaultTurn::new([0x04; 32], "worker", vec![1], vec![]).with_mandate_params(
                vec![IpcAuth::Read],
                6, // > budget (5)
                2,
                7,
            );
        assert!(matches!(
            mandate.check_turn(&over_budget_turn),
            Err(SandboxViolation::BudgetExceeded { .. })
        ));

        // 5. Tampered WireEnvelope sent over real TCP socket to validator 0 must be rejected
        use std::io::Write;
        let kp0 = cluster.nodes[0].keypair.clone();
        let mut forged_env = WireEnvelope::create(
            &kp0,
            ConsensusNetMessage::FastPathPropose(normal_turn.clone()),
        );
        forged_env.signature[0] ^= 0xFF;
        let forged_bytes = serde_json::to_vec(&forged_env).unwrap();
        let mut stream =
             std::net::TcpStream::connect(cluster.nodes[0].tcp_addr).expect("connect node 0");
        stream
            .write_all(&(forged_bytes.len() as u32).to_be_bytes())
            .unwrap();
        stream.write_all(&forged_bytes).unwrap();
        stream.flush().unwrap();
        drop(stream);
        std::thread::sleep(std::time::Duration::from_millis(20));
        assert!(cluster.nodes[0].state.lock().unwrap().rejected_wire_frames >= 1);

        // 6. Fold::collapse on empty block slice must return ConsensusVerification error
        let mut session = ObendSession::new().expect("session");
        assert!(matches!(
            Fold::collapse(1, &genesis, &[], &mut session),
            Err(NodeError::ConsensusVerification(_))
        ));
    }

    #[test]
    fn test_ws32_multi_epoch_interleaved_fast_path_and_consensus_spoofing_rejection() {
        let genesis = sample_genesis_cells();

        // 0. Invalid BFT cluster parameters (N < 2f + 1 or N == 0) must be rejected immediately
        assert!(matches!(
            SimplexCluster::new(0, 0, genesis.clone()),
            Err(NodeError::ConsensusVerification(_))
        ));
        assert!(matches!(
            SimplexCluster::new(2, 1, genesis.clone()),
            Err(NodeError::ConsensusVerification(_))
        ));

        let mut cluster =
            SimplexCluster::new(4, 1, genesis.clone()).expect("spawn 4-validator cluster");

        // 1. Reject duplicate write slots in `submit_concurrent_batch` and `stage_contended_or_inflight_turn`
        // even when no SandboxRunner is configured (must fail immediately without hanging)
        let dup_turn = VaultTurn::new(
            [0xD0; 32],
            "alice",
            vec![1],
            vec![(1, b"dup-a".to_vec()), (1, b"dup-b".to_vec())],
        );
        assert!(matches!(
            cluster.submit_concurrent_batch(vec![dup_turn.clone()]),
            Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot { .. }))
        ));
        assert!(matches!(
            cluster.stage_contended_or_inflight_turn(dup_turn),
            Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot { .. }))
        ));

        // 2. Interleaved Tier 1 FastPathCert + Tier 2 Simplex blocks + multi-epoch Tier 3 Fold::collapse:
        // (a) Commit FastPathCert `fp0` before block 1 (anchor_height == 0) on slot 2
        let fp0 = VaultTurn::new(
            [0xF0; 32],
            "fp_agent",
            vec![2],
            vec![(2, b"fp-before-h1".to_vec())],
        );
        let out_fp0 = cluster.submit_turn(fp0.clone()).expect("commit fp0");
        match out_fp0 {
            TurnSubmissionOutcome::FastPathCommitted { cert, .. } => {
                assert_eq!(cert.anchor_height, 0);
            }
            other => panic!("expected FastPathCommitted, got {other:?}"),
        }

        // (b) Block 1 (height 1): contended write to slot 1
        let t_h1 = VaultTurn::new(
            [0xB1; 32],
            "block_agent",
            vec![1],
            vec![(1, b"block-h1-slot1".to_vec())],
        );
        cluster
            .stage_contended_or_inflight_turn(t_h1.clone())
            .expect("stage t_h1");
        let b1 = cluster.run_simplex_block().expect("finalize height 1");
        assert_eq!(b1.height, 1);

        // (c) Commit FastPathCert `fp1` INSIDE Epoch 1 between height 1 and height 2 (anchor_height == 1)
        let fp1 = VaultTurn::new(
            [0xF1; 32],
            "fp_agent",
            vec![3],
            vec![(3, b"fp-between-h1-h2".to_vec())],
        );
        let out_fp1 = cluster.submit_turn(fp1.clone()).expect("commit fp1");
        match out_fp1 {
            TurnSubmissionOutcome::FastPathCommitted { cert, .. } => {
                assert_eq!(cert.anchor_height, 1);
            }
            other => panic!("expected FastPathCommitted, got {other:?}"),
        }

        // (d) Block 2 (height 2): contended write to slot 2
        let t_h2 = VaultTurn::new(
            [0xB2; 32],
            "block_agent",
            vec![2],
            vec![(2, b"block-h2-slot2".to_vec())],
        );
        cluster
            .stage_contended_or_inflight_turn(t_h2.clone())
            .expect("stage t_h2");
        let b2 = cluster.run_simplex_block().expect("finalize height 2");
        assert_eq!(b2.height, 2);

        // (e) Commit FastPathCert `fp2` BETWEEN Epoch 1 [1..=2] and Epoch 2 [3..=4] (anchor_height == 2)
        // writing to slot 1 (which `b1` at height 1 also wrote to, testing chronological replay order!)
        let fp2 = VaultTurn::new(
            [0xF2; 32],
            "fp_agent",
            vec![1],
            vec![(1, b"fp-between-epochs-slot1-override".to_vec())],
        );
        let fp2_cert = match cluster.submit_turn(fp2.clone()).expect("commit fp2") {
            TurnSubmissionOutcome::FastPathCommitted { cert, .. } => {
                assert_eq!(cert.anchor_height, 2);
                cert
            }
            other => panic!("expected FastPathCommitted, got {other:?}"),
        };

        // (f) Block 3 (height 3, empty heartbeat block) and Block 4 (height 4, contended write to slot 3)
        let b3 = cluster.run_simplex_block().expect("finalize empty height 3");
        assert_eq!(b3.height, 3);
        let t_h4 = VaultTurn::new(
            [0xB4; 32],
            "block_agent",
            vec![3],
            vec![(3, b"block-h4-slot3".to_vec())],
        );
        cluster
            .stage_contended_or_inflight_turn(t_h4.clone())
            .expect("stage t_h4");
        let b4 = cluster.run_simplex_block().expect("finalize height 4");
        assert_eq!(b4.height, 4);

        // Collapse Epoch 1 [1..=2] (even after fp2 and blocks 3..=4 have already committed!)
        let epoch1 = cluster
            .collapse_epoch(1, 1, 2)
            .expect("collapse epoch 1 [1..=2] with interleaved fast-path turns");
        assert_eq!(epoch1.initial_state_root, b1.pre_state_root);
        assert_eq!(epoch1.final_state_root, b2.post_state_root);
        assert_eq!(epoch1.total_block_count, 2);
        assert_eq!(epoch1.active_block_count, 2);

        // Collapse Epoch 2 [3..=4] and verify state root continuity across the interleaved `fp2` transition
        let epoch2 = cluster
            .collapse_epoch(2, 3, 4)
            .expect("collapse epoch 2 [3..=4] after interleaved fast-path turn");
        assert_eq!(epoch2.initial_state_root, fp2_cert.post_state_root);
        assert_eq!(epoch2.initial_state_root, b3.pre_state_root);
        assert_eq!(epoch2.final_state_root, b4.post_state_root);
        assert_eq!(epoch2.total_block_count, 2);
        assert_eq!(epoch2.active_block_count, 1);
        assert_eq!(epoch2.pruned_empty_block_count, 1);

        let mut session = ObendSession::new().expect("session");
        assert!(epoch1.verify(&mut session).expect("verify epoch1"));
        assert!(epoch2.verify(&mut session).expect("verify epoch2"));

        // Verify all turns (both FastPath and Simplex block turns) in [1..=4] promoted to Collapsed
        for node in &cluster.nodes {
            for tid in [
                &fp0.turn_id,
                &t_h1.turn_id,
                &fp1.turn_id,
                &t_h2.turn_id,
                &fp2.turn_id,
                &t_h4.turn_id,
            ] {
                assert_eq!(node.turn_tier(tid), Some(FinalityTier::Collapsed));
            }
        }

        // Non-contiguous blocks or incomplete epoch ranges must be rejected
        assert!(matches!(
            Fold::collapse(99, &genesis, &[b1.clone(), b3.clone()], &mut session),
            Err(NodeError::ConsensusVerification(_))
        ));
        assert!(matches!(
            cluster.collapse_epoch(3, 1, 10),
            Err(NodeError::ConsensusVerification(_))
        ));
        assert!(matches!(
            cluster.collapse_epoch(3, 0, 2),
            Err(NodeError::ConsensusVerification(_))
        ));

        // 3. Consensus spoofing / impersonation rejection on NetworkedValidatorNode:
        // Non-leader validator 1 attempts to spoof leader 0 in view 5 by setting `voter_id = 0`
        // while signing with validator 1's keypair
        let rejected_before = cluster.nodes[0].state.lock().unwrap().rejected_wire_frames;
        let kp1 = cluster.nodes[1].keypair.clone();
        let fake_payload = BlockPayload {
            height: 5,
            view: 5,
            turns: vec![],
            drex_currency: "USDC".to_string(),
            drex_goods: "WAFER".to_string(),
            drex_epsilon: 0,
            drex_orders: vec![],
        };
        let mut spoofed_prop = PropCert::create(
            &kp1,
            5,
            5,
            b4.block_hash,
            fake_payload.to_bytes(),
        );
        spoofed_prop.leader_vote.voter_id = 0; // Claim to be validator 0 (leader for view 5)
        cluster.nodes[1]
            .broadcast(ConsensusNetMessage::Propose(
                spoofed_prop,
                fake_payload.clone(),
            ))
            .expect("broadcast spoofed proposal");

        // Also broadcast a FinCert signed by unknown ephemeral keys
        let rogue_votes: Vec<SignedSimplexVote> = (0..3)
            .map(|id| {
                let rogue_kp = ValidatorKeypair::from_seed(id, b"rogue-outsider-seed");
                SignedSimplexVote::new(&rogue_kp, 5, SimplexVoteKind::Finalize, [0x99; 32])
            })
            .collect();
        let rogue_fin = FinCert {
            view: 5,
            block_hash: [0x99; 32],
            votes: rogue_votes,
        };
        cluster.nodes[1]
            .broadcast(ConsensusNetMessage::FinalizationCertificate(
                rogue_fin,
                fake_payload,
            ))
            .expect("broadcast rogue FinCert");

        std::thread::sleep(std::time::Duration::from_millis(30));
        let rejected_after = cluster.nodes[0].state.lock().unwrap().rejected_wire_frames;
        assert!(rejected_after >= rejected_before + 2);
        assert_eq!(cluster.nodes[0].committed_height(), 4);

        // 4. `inject_byzantine_equivocation` boundary checks
        assert!(matches!(
            cluster.inject_byzantine_equivocation(99, 5, [0x11; 32], [0x22; 32]),
            Err(NodeError::ConsensusVerification(_))
        ));
        assert!(matches!(
            cluster.inject_byzantine_equivocation(1, 5, [0x11; 32], [0x11; 32]),
            Err(NodeError::ConsensusVerification(_))
        ));

        // 5. Powerbox::delegate requires IpcAuth::Grant and clamps to remaining unspent budget
        let mut pb = Powerbox::new("obend.vault");
        pb.grant_mandate(Mandate {
            grantor: "kernel".to_string(),
            holder: "no_grant_agent".to_string(),
            target: "obend.vault".to_string(),
            rights: vec![IpcAuth::Read, IpcAuth::Write],
            budget: 50,
            allowed_slots: vec![1],
            expires_at: 10,
            allowed_methods: None,
        })
        .unwrap();
        assert!(matches!(
            pb.delegate("no_grant_agent", "child", &[IpcAuth::Read], 10, &[1], 5, None),
            Err(SandboxViolation::MissingCapability {
                required: IpcAuth::Grant,
                ..
            })
        ));

        // 6. GrainConfig::verify_strict_policy rejects weakened namespace/process flags
        let mut weak_grain = GrainConfig::strict_for_agent("w", std::env::temp_dir());
        weak_grain.policy.die_with_parent = false;
        assert!(matches!(
            weak_grain.verify_strict_policy(),
            Err(SandboxViolation::InsecureConfinementPolicy { .. })
        ));
    }

    #[test]
    fn test_simplex_state_step_with_verified_session_and_tamper_rejection() {
        let validators: Vec<ValidatorKeypair> = (0..4)
            .map(|id| ValidatorKeypair::from_seed(id, b"verified-bridge-seed"))
            .collect();
        let genesis = sample_genesis_cells();
        let mut state = SimplexState::new(4, 1, genesis.clone());
        let mut session = ObendSession::new().expect("session init");

        let mandate = Mandate {
            grantor: "kernel".to_string(),
            holder: "alice_trader".to_string(),
            target: "obend.vault".to_string(),
            rights: vec![IpcAuth::Read, IpcAuth::Write],
            budget: 50,
            allowed_slots: vec![1, 2],
            expires_at: 100,
            allowed_methods: Some(vec![0]),
        };

        let turn = VaultTurn::new(
            [0x77; 32],
            "alice_trader",
            vec![1],
            vec![(1, b"verified-slot-1-v1".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read, IpcAuth::Write], 5, 1, 0);

        let orders = vec![
            LimitOrder {
                account: "alice_buyer".to_string(),
                side: OrderSide::Bid,
                qty: 10,
                total: 1200,
            },
            LimitOrder {
                account: "carol_seller".to_string(),
                side: OrderSide::Ask,
                qty: 10,
                total: 1000,
            },
        ];

        let transition = VerifiedEpochBridge::step_with_verified_session(
            &mut state,
            &validators,
            Some(&mandate),
            &turn,
            Some(("USDC", "WAFER", 0, &orders)),
            &mut session,
        )
        .expect("step_with_verified_session should succeed");

        assert_eq!(transition.prior_view, 0);
        assert_eq!(transition.next_view, 1);
        assert_eq!(transition.height, 1);
        assert!(!transition.receipt_bytes.is_empty());
        assert!(transition.receipt_bytes.len() > 32);
        assert_ne!(transition.state_digest, [0u8; 32]);
        assert_eq!(
            transition.simplex_cert.receipt_bytes,
            transition.receipt_bytes
        );
        assert_ne!(transition.simplex_cert.state_digest, [0u8; 32]);

        let clearing = transition
            .clearing_receipt
            .as_ref()
            .expect("clearing receipt present");
        assert!(!clearing.receipt_bytes.is_empty());
        assert_ne!(clearing.state_digest, [0u8; 32]);
        assert_eq!(clearing.certificate.price, 110);
        assert_eq!(clearing.certificate.objective_volume, 20);

        // Verify transition on a follower SimplexState
        let mut follower = SimplexState::new(4, 1, genesis.clone());
        assert!(transition
            .verify_with_session(4, 3, &orders, &mut session)
            .expect("verify transition"));
        follower
            .apply_verified_transition(&transition, &orders, &mut session)
            .expect("follower apply verified transition");
        assert_eq!(follower.view, 1);
        assert_eq!(follower.height, 1);
        assert_eq!(follower.state_digest, state.state_digest);

        // 1. Tampering with transition `receipt_bytes` must be rejected
        let mut tampered_receipt = transition.clone();
        tampered_receipt.receipt_bytes[0] ^= 0xFF;
        assert!(!tampered_receipt
            .verify_with_session(4, 3, &orders, &mut session)
            .expect("verify tampered receipt_bytes"));
        assert!(follower
            .apply_verified_transition(&tampered_receipt, &orders, &mut session)
            .is_err());

        // 2. Tampering with `simplex_cert.receipt_bytes` must be rejected
        let mut tampered_simplex = transition.clone();
        tampered_simplex.simplex_cert.receipt_bytes[16] ^= 0xAA;
        tampered_simplex.receipt_bytes = tampered_simplex.simplex_cert.receipt_bytes.clone();
        assert!(!tampered_simplex
            .verify_with_session(4, 3, &orders, &mut session)
            .expect("verify tampered simplex_cert"));

        // 3. Tampering with `clearing_receipt.state_digest` or `receipt_bytes` must be rejected
        let mut tampered_clearing = transition.clone();
        tampered_clearing
            .clearing_receipt
            .as_mut()
            .unwrap()
            .receipt_bytes[8] ^= 0x55;
        assert!(!tampered_clearing
            .verify_with_session(4, 3, &orders, &mut session)
            .expect("verify tampered clearing receipt"));

        // 4. Empty `receipt_bytes` must be rejected
        let mut empty_receipt = transition.clone();
        empty_receipt.receipt_bytes.clear();
        empty_receipt.simplex_cert.receipt_bytes.clear();
        assert!(!empty_receipt
            .verify_with_session(4, 3, &orders, &mut session)
            .expect("verify empty receipt"));
    }

    #[test]
    fn test_mandate_and_fog_of_war_step_with_verified_session() {
        let mut fog = FogOfWar::new(sample_genesis_cells(), vec![IpcAuth::Read]);
        let mut session = ObendSession::new().expect("session init");

        let mandate = Mandate {
            grantor: "kernel".to_string(),
            holder: "fog_worker".to_string(),
            target: "obend.vault".to_string(),
            rights: vec![IpcAuth::Read, IpcAuth::Write],
            budget: 20,
            allowed_slots: vec![1],
            expires_at: 10,
            allowed_methods: Some(vec![0]),
        };

        let orders = vec![
            LimitOrder {
                account: "buyer".to_string(),
                side: OrderSide::Bid,
                qty: 4,
                total: 400,
            },
            LimitOrder {
                account: "seller".to_string(),
                side: OrderSide::Ask,
                qty: 4,
                total: 400,
            },
        ];

        let valid_turn = VaultTurn::new(
            [0x88; 32],
            "fog_worker",
            vec![1],
            vec![(1, b"fog-cell-updated".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read, IpcAuth::Write], 5, 2, 0);

        let receipt = mandate
            .step_with_verified_session(
                &mut fog,
                &valid_turn,
                "USDC",
                "WAFER",
                0,
                &orders,
                &mut session,
            )
            .expect("Mandate::step_with_verified_session should succeed");

        assert!(!receipt.receipt_bytes.is_empty());
        assert_ne!(receipt.state_digest, [0u8; 32]);
        assert!(receipt
            .verify_with_session(&orders, &mut session)
            .expect("verify clearing receipt"));
        // Slot 3 remains Blinded to viewer holding only IpcAuth::Read
        assert!(matches!(
            receipt.multiproof.projected_cells[2],
            ProjectedCellView::Blinded { id: 3, .. }
        ));

        // Tampering with the FogOfWar multiproof root inside ClearingReceipt is rejected
        let mut bad_mp = receipt.clone();
        bad_mp.multiproof.unredacted_root[0] ^= 0x01;
        assert!(!bad_mp
            .verify_with_session(&orders, &mut session)
            .expect("tampered multiproof must fail"));

        // Unauthorized slot 3 write is rejected by Mandate before touching FFI
        let unauthorized_turn = VaultTurn::new(
            [0x89; 32],
            "fog_worker",
            vec![3],
            vec![(3, b"illegal".to_vec())],
        )
        .with_mandate_params(vec![IpcAuth::Read, IpcAuth::Write], 5, 2, 0);
        assert!(matches!(
            mandate.step_with_verified_session(
                &mut fog,
                &unauthorized_turn,
                "USDC",
                "WAFER",
                0,
                &orders,
                &mut session,
            ),
            Err(NodeError::Sandbox(SandboxViolation::UnauthorizedSlotAccess { .. }))
        ));

        // Edge case: SimplexState with insufficient validators or duplicate write slots
        let validators: Vec<ValidatorKeypair> = (0..4)
            .map(|id| ValidatorKeypair::from_seed(id, b"edge-seed"))
            .collect();
        let mut state = SimplexState::new(4, 1, sample_genesis_cells());
        let ro_turn = VaultTurn::new([0x90; 32], "reader", vec![1], vec![]);
        assert!(state
            .step_with_verified_session(&validators[..2], None, &ro_turn, None, &mut session)
            .is_err());

        // Read-only turn with no DREX batch across two consecutive views (view 1 leader 0 -> view 2 leader 1)
        let tr1 = state
            .step_with_verified_session(&validators, None, &ro_turn, None, &mut session)
            .expect("view 1 read-only transition");
        assert_eq!(tr1.next_view, 1);
        assert!(tr1.clearing_receipt.is_none());
        assert!(tr1
            .verify_with_session(4, 3, &[], &mut session)
            .expect("verify tr1"));

        let tr2 = state
            .step_with_verified_session(&validators, None, &ro_turn, None, &mut session)
            .expect("view 2 read-only transition");
        assert_eq!(tr2.prior_view, 1);
        assert_eq!(tr2.next_view, 2);
        assert_eq!(
            tr2.simplex_cert.prop_cert.as_ref().unwrap().parent_hash,
            tr1.simplex_cert.block_hash
        );
        assert!(tr2
            .verify_with_session(4, 3, &[], &mut session)
            .expect("verify tr2"));
    }
}


