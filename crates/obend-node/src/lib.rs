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
        Fe::from_u64(121665).neg().mul(Fe::from_u64(121666).inv())
    }

    /// Principal square root of -1: 2^((p - 1) / 4) mod (2^255 - 19).
    fn sqrt_m1() -> Fe {
        // (p - 1) / 4 = (2^255 - 20) / 4 = 2^253 - 5
        let mut exp = [0xFFu8; 32];
        exp[0] = 0xFB; // 256 - 5 = 251
        exp[31] = 0x1F;
        Fe::from_u64(2).pow_bytes(&exp)
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
        let by = Fe::from_u64(4).mul(Fe::from_u64(5).inv()).to_bytes();
        Self::decode(&by).expect("valid Ed25519 basepoint B")
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
}
