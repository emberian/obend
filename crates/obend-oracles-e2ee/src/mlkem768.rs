#![forbid(unsafe_code)]
//! Pure-Rust NIST FIPS 203 `ML-KEM-768` (`k = 3, n = 256, q = 3329, η₁ = 2, η₂ = 2, d_u = 10, d_v = 4`)
//! with `#![forbid(unsafe_code)]` and `0` external dependencies.
//!
//! Implements:
//! - FIPS 202 Keccak-f[1600] sponge primitives (`SHA3-256`, `SHA3-512`, `SHAKE128`, `SHAKE256`),
//! - FIPS 203 §4.2–4.3 `ByteEncode_d` / `ByteDecode_d`, constant-time Barrett `Compress_d` /
//!   `Decompress_d`, `SampleNTT`, `SamplePolyCBD_2`, and 128-point $\zeta = 17$ `NTT` / `NTT⁻¹` /
//!   `MultiplyNTTs`,
//! - Mandatory FIPS 203 §7.2 Encapsulation Key Check (`validate_encaps_key`: length `== 1184` AND
//!   canonical modulus round-trip `ByteEncode_12(ByteDecode_12(ek[0..1152])) == ek[0..1152]`),
//! - Mandatory FIPS 203 §7.3 Decapsulation Key Check (`validate_decaps_key`: length `== 2400` AND
//!   `SHA3-256(dk[1152..2336]) == dk[2336..2368]`),
//! - Deterministic `ml_kem_768_keygen_internal(d, z)`, `ml_kem_768_encaps_internal(ek, m)`, and
//!   constant-time Fujisaki–Okamoto implicit-rejection `ml_kem_768_decaps_internal(dk, ct)`
//!   (`J(z || c)` fallback with branchless comparison and bitwise conditional select).

use crate::sha256::ct_eq;

/// Degree of ML-KEM ring polynomials $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$.
pub const ML_KEM_N: usize = 256;
/// Prime modulus $q = 3329 = 13 \cdot 2^8 + 1$.
pub const ML_KEM_Q: u16 = 3329;
/// Module rank $k = 3$ for `ML-KEM-768`.
pub const ML_KEM_768_K: usize = 3;
/// Encapsulation (public) key byte length for `ML-KEM-768` ($384k + 32 = 1184$).
pub const ML_KEM_768_EK_LEN: usize = 1184;
/// Decapsulation (secret) key byte length for `ML-KEM-768` ($768k + 96 = 2400$).
pub const ML_KEM_768_DK_LEN: usize = 2400;
/// Ciphertext byte length for `ML-KEM-768` ($32(d_u k + d_v) = 1088$).
pub const ML_KEM_768_CT_LEN: usize = 1088;
/// Shared secret byte length for `ML-KEM-768` ($32$).
pub const ML_KEM_768_SS_LEN: usize = 32;

const INV_128_MOD_Q: u16 = 3303;
/// Exact Barrett reciprocal $\lceil 2^{36} / 3329 \rceil = 20{,}642{,}679$:
/// `(val * 20_642_679) >> 36 == val / 3329` for all `0 <= val < 4096 * 3329` (`13_635_584`).
const BARRETT_MUL_36: u64 = 20_642_679;

/// Errors returned by FIPS 203 `ML-KEM-768` input validation gates (§7.1–7.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlKemError {
    /// Encapsulation key length is not `1184` bytes.
    InvalidEncapsKeyLength { actual: usize },
    /// Encapsulation key failed the FIPS 203 §7.2 modulus check (coefficient $\ge 3329$).
    NonCanonicalEncapsKey,
    /// Decapsulation key length is not `2400` bytes.
    InvalidDecapsKeyLength { actual: usize },
    /// Decapsulation key failed the FIPS 203 §7.3 embedded `H(ek)` binding check.
    InvalidDecapsKeyHash,
    /// Ciphertext length is not `1088` bytes.
    InvalidCiphertextLength { actual: usize },
}

// ---------------------------------------------------------------------------
// 1. Pure-Rust FIPS 202 Keccak-f[1600] Sponge (SHA3-256, SHA3-512, SHAKE128, SHAKE256)
// ---------------------------------------------------------------------------

const KECCAK_RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

const KECCAK_RHO: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Permute a 25-lane Keccak-f[1600] state in place (24 rounds).
pub fn keccak_f1600(state: &mut [u64; 25]) {
    for &rc in &KECCAK_RC {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                state[x + 5 * y] ^= d;
            }
        }
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] =
                    state[x + 5 * y].rotate_left(KECCAK_RHO[x + 5 * y]);
            }
        }
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
            }
        }
        state[0] ^= rc;
    }
}

/// Reusable incremental FIPS 202 Keccak sponge parameterized by byte rate `R` and domain suffix.
#[derive(Clone)]
pub struct KeccakSponge<const RATE: usize> {
    state: [u64; 25],
    buf: [u8; RATE],
    pos: usize,
    squeezing: bool,
    suffix: u8,
}

impl<const RATE: usize> KeccakSponge<RATE> {
    pub const fn new(suffix: u8) -> Self {
        Self {
            state: [0u64; 25],
            buf: [0u8; RATE],
            pos: 0,
            squeezing: false,
            suffix,
        }
    }

    fn xor_block(&mut self, block: &[u8; RATE]) {
        let lanes = RATE / 8;
        for (i, lane_ref) in self.state.iter_mut().enumerate().take(lanes) {
            let off = 8 * i;
            let word = u64::from_le_bytes([
                block[off],
                block[off + 1],
                block[off + 2],
                block[off + 3],
                block[off + 4],
                block[off + 5],
                block[off + 6],
                block[off + 7],
            ]);
            *lane_ref ^= word;
        }
        keccak_f1600(&mut self.state);
    }

    fn export_rate_bytes(&mut self) {
        let lanes = RATE / 8;
        for i in 0..lanes {
            self.buf[8 * i..8 * i + 8].copy_from_slice(&self.state[i].to_le_bytes());
        }
    }

    pub fn absorb(&mut self, mut data: &[u8]) {
        debug_assert!(!self.squeezing);
        if self.pos > 0 {
            let take = (RATE - self.pos).min(data.len());
            self.buf[self.pos..self.pos + take].copy_from_slice(&data[..take]);
            self.pos += take;
            data = &data[take..];
            if self.pos == RATE {
                let block = self.buf;
                self.pos = 0;
                self.xor_block(&block);
            }
        }
        while data.len() >= RATE {
            let mut block = [0u8; RATE];
            block.copy_from_slice(&data[..RATE]);
            self.xor_block(&block);
            data = &data[RATE..];
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.pos = data.len();
        }
    }

    fn finalize_absorb(&mut self) {
        if !self.squeezing {
            for b in &mut self.buf[self.pos..RATE] {
                *b = 0;
            }
            self.buf[self.pos] ^= self.suffix;
            self.buf[RATE - 1] ^= 0x80;
            let block = self.buf;
            self.xor_block(&block);
            self.export_rate_bytes();
            self.pos = 0;
            self.squeezing = true;
        }
    }

    pub fn squeeze(&mut self, mut out: &mut [u8]) {
        self.finalize_absorb();
        while !out.is_empty() {
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.export_rate_bytes();
                self.pos = 0;
            }
            let avail = (RATE - self.pos).min(out.len());
            out[..avail].copy_from_slice(&self.buf[self.pos..self.pos + avail]);
            self.pos += avail;
            out = &mut out[avail..];
        }
    }
}

/// Incremental FIPS 202 `SHAKE128` XOF (`rate = 168`, `suffix = 0x1f`).
pub type Shake128 = KeccakSponge<168>;
/// Incremental FIPS 202 `SHAKE256` XOF (`rate = 136`, `suffix = 0x1f`).
pub type Shake256 = KeccakSponge<136>;

/// FIPS 202 `SHA3-256` (`H(s)` in FIPS 203 §4.1).
pub fn sha3_256(data: &[u8]) -> [u8; 32] {
    let mut sp = KeccakSponge::<136>::new(0x06);
    sp.absorb(data);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// FIPS 202 `SHA3-512` (`G(c)` in FIPS 203 §4.1).
pub fn sha3_512(data: &[u8]) -> [u8; 64] {
    let mut sp = KeccakSponge::<72>::new(0x06);
    sp.absorb(data);
    let mut out = [0u8; 64];
    sp.squeeze(&mut out);
    out
}

/// One-shot FIPS 202 `SHAKE256` into `out`.
pub fn shake256_into(data: &[u8], out: &mut [u8]) {
    let mut sp = Shake256::new(0x1f);
    sp.absorb(data);
    sp.squeeze(out);
}

// ---------------------------------------------------------------------------
// 2. Constant-Time Field Arithmetic mod q = 3329 & Precomputed Zeta Tables
// ---------------------------------------------------------------------------

/// Polynomial in $R_q$ or $\hat{R}_q$ with canonical coefficients in $[0, 3328]$.
pub type Poly = [u16; ML_KEM_N];

#[inline]
const fn bitrev7(mut x: u8) -> u8 {
    let mut r = 0u8;
    let mut k = 0;
    while k < 7 {
        r = (r << 1) | (x & 1);
        x >>= 1;
        k += 1;
    }
    r
}

#[inline]
const fn pow_mod_q(mut base: u32, mut exp: u8) -> u16 {
    let mut acc = 1u32;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = (acc * base) % (ML_KEM_Q as u32);
        }
        base = (base * base) % (ML_KEM_Q as u32);
        exp >>= 1;
    }
    acc as u16
}

const fn compute_zetas() -> [u16; 128] {
    let mut table = [0u16; 128];
    let mut i = 0;
    while i < 128 {
        table[i] = pow_mod_q(17, bitrev7(i as u8));
        i += 1;
    }
    table
}

const fn compute_gammas() -> [u16; 128] {
    let mut table = [0u16; 128];
    let mut i = 0;
    while i < 128 {
        table[i] = pow_mod_q(17, 2 * bitrev7(i as u8) + 1);
        i += 1;
    }
    table
}

/// FIPS 203 Appendix A bit-reversed powers $\zeta^{\text{BitRev}_7(i)} \bmod 3329$.
pub const ZETAS: [u16; 128] = compute_zetas();
/// Base-case powers $\zeta^{2 \cdot \text{BitRev}_7(i) + 1} \bmod 3329$ for `MultiplyNTTs`.
pub const GAMMAS: [u16; 128] = compute_gammas();

/// Constant-time division by $q = 3329$ for `val < 13_635_584` (`0` hardware `div` instructions).
#[inline]
pub const fn barrett_div_q(val: u32) -> u32 {
    (((val as u64) * BARRETT_MUL_36) >> 36) as u32
}

/// Constant-time canonical reduction modulo $q = 3329$ for `val < 13_635_584`.
#[inline]
pub const fn barrett_mod_q(val: u32) -> u16 {
    let q_quot = barrett_div_q(val);
    (val - q_quot * (ML_KEM_Q as u32)) as u16
}

#[inline]
const fn fq_add(a: u16, b: u16) -> u16 {
    let sum = (a + b).wrapping_sub(ML_KEM_Q);
    // If a + b < 3329, sum underflows so bit 15 is 1 -> add 3329 back.
    let mask = (sum >> 15).wrapping_neg();
    sum.wrapping_add(ML_KEM_Q & mask)
}

#[inline]
const fn fq_sub(a: u16, b: u16) -> u16 {
    let diff = a.wrapping_sub(b);
    let mask = (diff >> 15).wrapping_neg();
    diff.wrapping_add(ML_KEM_Q & mask)
}

#[inline]
const fn fq_mul(a: u16, b: u16) -> u16 {
    barrett_mod_q((a as u32) * (b as u32))
}

#[inline]
fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..ML_KEM_N {
        out[i] = fq_add(a[i], b[i]);
    }
    out
}

#[inline]
fn poly_sub(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..ML_KEM_N {
        out[i] = fq_sub(a[i], b[i]);
    }
    out
}

// ---------------------------------------------------------------------------
// 3. Compress_d / Decompress_d & ByteEncode_d / ByteDecode_d (FIPS 203 §4.2)
// ---------------------------------------------------------------------------

/// Constant-time FIPS 203 §4.2.1 `Compress_d(x)` ($\lceil (2^d / 3329) \cdot x \rfloor \bmod 2^d$).
#[inline]
pub const fn compress_d(x: u16, d: u32) -> u16 {
    let num = ((x as u32) << d) + 1664;
    let quot = barrett_div_q(num);
    (quot & ((1u32 << d) - 1)) as u16
}

/// Constant-time FIPS 203 §4.2.1 `Decompress_d(y)` ($\lceil (3329 / 2^d) \cdot y \rfloor$).
#[inline]
pub const fn decompress_d(y: u16, d: u32) -> u16 {
    (((ML_KEM_Q as u32) * (y as u32) + (1u32 << (d - 1))) >> d) as u16
}

/// FIPS 203 Algorithm 5 `ByteEncode_1` (`256` 1-bit values -> `32` bytes).
pub fn byte_encode_1(f: &Poly) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..32 {
        let mut acc = 0u8;
        for bit in 0..8 {
            acc |= ((f[8 * i + bit] & 1) as u8) << bit;
        }
        out[i] = acc;
    }
    out
}

/// FIPS 203 Algorithm 6 `ByteDecode_1` (`32` bytes -> `256` 1-bit values).
pub fn byte_decode_1(bytes: &[u8; 32]) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..32 {
        let b = bytes[i];
        for bit in 0..8 {
            out[8 * i + bit] = u16::from((b >> bit) & 1);
        }
    }
    out
}

/// FIPS 203 Algorithm 5 `ByteEncode_4` (`256` 4-bit values -> `128` bytes).
pub fn byte_encode_4(f: &Poly) -> [u8; 128] {
    let mut out = [0u8; 128];
    for i in 0..128 {
        out[i] = ((f[2 * i] & 0x0f) as u8) | (((f[2 * i + 1] & 0x0f) as u8) << 4);
    }
    out
}

/// FIPS 203 Algorithm 6 `ByteDecode_4` (`128` bytes -> `256` 4-bit values).
pub fn byte_decode_4(bytes: &[u8; 128]) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..128 {
        out[2 * i] = u16::from(bytes[i] & 0x0f);
        out[2 * i + 1] = u16::from(bytes[i] >> 4);
    }
    out
}

/// FIPS 203 Algorithm 5 `ByteEncode_10` (`256` 10-bit values -> `320` bytes).
pub fn byte_encode_10(f: &Poly) -> [u8; 320] {
    let mut out = [0u8; 320];
    for i in 0..64 {
        let t0 = f[4 * i] & 0x03ff;
        let t1 = f[4 * i + 1] & 0x03ff;
        let t2 = f[4 * i + 2] & 0x03ff;
        let t3 = f[4 * i + 3] & 0x03ff;
        out[5 * i] = (t0 & 0xff) as u8;
        out[5 * i + 1] = ((t0 >> 8) | ((t1 & 0x3f) << 2)) as u8;
        out[5 * i + 2] = ((t1 >> 6) | ((t2 & 0x0f) << 4)) as u8;
        out[5 * i + 3] = ((t2 >> 4) | ((t3 & 0x03) << 6)) as u8;
        out[5 * i + 4] = (t3 >> 2) as u8;
    }
    out
}

/// FIPS 203 Algorithm 6 `ByteDecode_10` (`320` bytes -> `256` 10-bit values).
pub fn byte_decode_10(bytes: &[u8; 320]) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..64 {
        let b0 = u16::from(bytes[5 * i]);
        let b1 = u16::from(bytes[5 * i + 1]);
        let b2 = u16::from(bytes[5 * i + 2]);
        let b3 = u16::from(bytes[5 * i + 3]);
        let b4 = u16::from(bytes[5 * i + 4]);
        out[4 * i] = b0 | ((b1 & 0x03) << 8);
        out[4 * i + 1] = (b1 >> 2) | ((b2 & 0x0f) << 6);
        out[4 * i + 2] = (b2 >> 4) | ((b3 & 0x3f) << 4);
        out[4 * i + 3] = (b3 >> 6) | (b4 << 2);
    }
    out
}

/// FIPS 203 Algorithm 5 `ByteEncode_12` (`256` canonical 12-bit coefficients -> `384` bytes).
pub fn byte_encode_12(f: &Poly) -> [u8; 384] {
    let mut out = [0u8; 384];
    for i in 0..128 {
        let a = f[2 * i] & 0x0fff;
        let b = f[2 * i + 1] & 0x0fff;
        out[3 * i] = (a & 0xff) as u8;
        out[3 * i + 1] = ((a >> 8) | ((b & 0x0f) << 4)) as u8;
        out[3 * i + 2] = (b >> 4) as u8;
    }
    out
}

/// FIPS 203 Algorithm 6 `ByteDecode_12` (`384` bytes -> `256` coefficients reduced mod $q = 3329$).
pub fn byte_decode_12(bytes: &[u8; 384]) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..128 {
        let b0 = u16::from(bytes[3 * i]);
        let b1 = u16::from(bytes[3 * i + 1]);
        let b2 = u16::from(bytes[3 * i + 2]);
        let d0 = b0 | ((b1 & 0x0f) << 8);
        let d1 = (b1 >> 4) | (b2 << 4);
        out[2 * i] = barrett_mod_q(u32::from(d0));
        out[2 * i + 1] = barrett_mod_q(u32::from(d1));
    }
    out
}

// ---------------------------------------------------------------------------
// 4. Sampling (`SampleNTT`, `SamplePolyCBD_2`) & NTT / NTT⁻¹ / MultiplyNTTs
// ---------------------------------------------------------------------------

/// FIPS 203 Algorithm 7 `SampleNTT(XOF(ρ, b1, b2))` using incremental `SHAKE128` (`0` wasted blocks).
pub fn sample_ntt(rho: &[u8; 32], b1: u8, b2: u8) -> Poly {
    let mut xof = Shake128::new(0x1f);
    xof.absorb(rho);
    xof.absorb(&[b1, b2]);

    let mut out = [0u16; ML_KEM_N];
    let mut j = 0usize;
    let mut triple = [0u8; 3];
    while j < ML_KEM_N {
        xof.squeeze(&mut triple);
        let d1 = u16::from(triple[0]) | (u16::from(triple[1] & 0x0f) << 8);
        let d2 = u16::from(triple[1] >> 4) | (u16::from(triple[2]) << 4);
        if d1 < ML_KEM_Q {
            out[j] = d1;
            j += 1;
        }
        if d2 < ML_KEM_Q && j < ML_KEM_N {
            out[j] = d2;
            j += 1;
        }
    }
    out
}

/// FIPS 203 Algorithm 8 `SamplePolyCBD_2` ($\eta = 2$, reading $64\eta = 128$ PRF bytes).
pub fn sample_poly_cbd2(bytes: &[u8; 128]) -> Poly {
    let mut out = [0u16; ML_KEM_N];
    for i in 0..128 {
        let b = bytes[i];
        let x0 = u16::from((b & 1) + ((b >> 1) & 1));
        let y0 = u16::from(((b >> 2) & 1) + ((b >> 3) & 1));
        out[2 * i] = fq_sub(x0, y0);

        let x1 = u16::from(((b >> 4) & 1) + ((b >> 5) & 1));
        let y1 = u16::from(((b >> 6) & 1) + ((b >> 7) & 1));
        out[2 * i + 1] = fq_sub(x1, y1);
    }
    out
}

fn prf_eta2(sigma: &[u8; 32], nonce: u8) -> [u8; 128] {
    let mut sp = Shake256::new(0x1f);
    sp.absorb(sigma);
    sp.absorb(&[nonce]);
    let mut out = [0u8; 128];
    sp.squeeze(&mut out);
    out
}

/// FIPS 203 Algorithm 9 `NTT(f)` (128-point radix-2 Cooley–Tukey over $\zeta = 17 \bmod 3329$).
pub fn ntt(f: &Poly) -> Poly {
    let mut a = *f;
    let mut k = 1usize;
    let mut len = 128usize;
    while len >= 2 {
        let mut start = 0usize;
        while start < ML_KEM_N {
            let zeta = ZETAS[k];
            k += 1;
            for j in start..start + len {
                let t = fq_mul(zeta, a[j + len]);
                a[j + len] = fq_sub(a[j], t);
                a[j] = fq_add(a[j], t);
            }
            start += 2 * len;
        }
        len >>= 1;
    }
    a
}

/// FIPS 203 Algorithm 10 `NTT⁻¹(f̂)` (Gentleman–Sande butterflies + $128^{-1} \equiv 3303 \bmod 3329$).
pub fn ntt_inv(f_hat: &Poly) -> Poly {
    let mut a = *f_hat;
    let mut k = 127usize;
    let mut len = 2usize;
    while len <= 128 {
        let mut start = 0usize;
        while start < ML_KEM_N {
            let zeta = ZETAS[k];
            k = k.wrapping_sub(1);
            for j in start..start + len {
                let t = a[j];
                a[j] = fq_add(t, a[j + len]);
                a[j + len] = fq_mul(zeta, fq_sub(a[j + len], t));
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    for coeff in &mut a {
        *coeff = fq_mul(*coeff, INV_128_MOD_Q);
    }
    a
}

/// FIPS 203 Algorithms 11 & 12 `MultiplyNTTs(f̂, ĝ)` across the 128 quadratic factors
/// $X^2 - \zeta^{2 \cdot \text{BitRev}_7(i) + 1}$.
pub fn multiply_ntts(f_hat: &Poly, g_hat: &Poly) -> Poly {
    let mut h = [0u16; ML_KEM_N];
    for i in 0..128 {
        let a0 = u32::from(f_hat[2 * i]);
        let a1 = u32::from(f_hat[2 * i + 1]);
        let b0 = u32::from(g_hat[2 * i]);
        let b1 = u32::from(g_hat[2 * i + 1]);
        let gamma = u32::from(GAMMAS[i]);

        let a1b1_gamma = u32::from(barrett_mod_q(a1 * b1)) * gamma;
        h[2 * i] = barrett_mod_q(a0 * b0 + a1b1_gamma);
        h[2 * i + 1] = barrett_mod_q(a0 * b1 + a1 * b0);
    }
    h
}

// ---------------------------------------------------------------------------
// 5. Mandatory FIPS 203 §7.2 & §7.3 Input Validation Gates
// ---------------------------------------------------------------------------

/// **FIPS 203 §7.2 Encapsulation Key Check**: verifies `ek.len() == 1184` AND enforces canonical
/// modulus encoding `ByteEncode_12(ByteDecode_12(ek[0..1152])) == ek[0..1152]` in constant time
/// (rejecting any 12-bit coefficient $\ge 3329$).
pub fn validate_encaps_key(ek: &[u8]) -> Result<&[u8; ML_KEM_768_EK_LEN], MlKemError> {
    let ek_arr: &[u8; ML_KEM_768_EK_LEN] = ek
        .try_into()
        .map_err(|_| MlKemError::InvalidEncapsKeyLength { actual: ek.len() })?;

    let mut reencoded = [0u8; 384 * ML_KEM_768_K];
    for i in 0..ML_KEM_768_K {
        let mut slice = [0u8; 384];
        slice.copy_from_slice(&ek_arr[384 * i..384 * (i + 1)]);
        let decoded = byte_decode_12(&slice);
        let encoded = byte_encode_12(&decoded);
        reencoded[384 * i..384 * (i + 1)].copy_from_slice(&encoded);
    }

    if !ct_eq(&reencoded, &ek_arr[..384 * ML_KEM_768_K]) {
        return Err(MlKemError::NonCanonicalEncapsKey);
    }
    Ok(ek_arr)
}

/// **FIPS 203 §7.3 Decapsulation Key Check**: verifies `dk.len() == 2400`, validates the embedded
/// encapsulation key `dk[1152..2336]` under §7.2, and verifies `SHA3-256(ek) == dk[2336..2368]`
/// in constant time.
pub fn validate_decaps_key(dk: &[u8]) -> Result<&[u8; ML_KEM_768_DK_LEN], MlKemError> {
    let dk_arr: &[u8; ML_KEM_768_DK_LEN] = dk
        .try_into()
        .map_err(|_| MlKemError::InvalidDecapsKeyLength { actual: dk.len() })?;

    let embedded_ek = &dk_arr[1152..2336];
    let expected_h = sha3_256(embedded_ek);
    if !ct_eq(&expected_h, &dk_arr[2336..2368]) {
        return Err(MlKemError::InvalidDecapsKeyHash);
    }
    validate_encaps_key(embedded_ek)?;
    Ok(dk_arr)
}

// ---------------------------------------------------------------------------
// 6. K-PKE (Algorithms 13–15) & ML-KEM-768 Internal / Checked Entry Points (Algorithms 16–21)
// ---------------------------------------------------------------------------

fn k_pke_keygen(d: &[u8; 32]) -> ([u8; ML_KEM_768_EK_LEN], [u8; 1152]) {
    let mut g_in = [0u8; 33];
    g_in[..32].copy_from_slice(d);
    g_in[32] = ML_KEM_768_K as u8;
    let g_out = sha3_512(&g_in);
    let mut rho = [0u8; 32];
    let mut sigma = [0u8; 32];
    rho.copy_from_slice(&g_out[0..32]);
    sigma.copy_from_slice(&g_out[32..64]);

    let mut a_hat = [[[0u16; ML_KEM_N]; ML_KEM_768_K]; ML_KEM_768_K];
    for i in 0..ML_KEM_768_K {
        for j in 0..ML_KEM_768_K {
            a_hat[i][j] = sample_ntt(&rho, j as u8, i as u8);
        }
    }

    let mut s_hat = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    let mut e_hat = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    let mut nonce = 0u8;
    for s_poly in &mut s_hat {
        *s_poly = ntt(&sample_poly_cbd2(&prf_eta2(&sigma, nonce)));
        nonce += 1;
    }
    for e_poly in &mut e_hat {
        *e_poly = ntt(&sample_poly_cbd2(&prf_eta2(&sigma, nonce)));
        nonce += 1;
    }

    let mut ek = [0u8; ML_KEM_768_EK_LEN];
    for i in 0..ML_KEM_768_K {
        let mut acc = e_hat[i];
        for j in 0..ML_KEM_768_K {
            let prod = multiply_ntts(&a_hat[i][j], &s_hat[j]);
            acc = poly_add(&acc, &prod);
        }
        ek[384 * i..384 * (i + 1)].copy_from_slice(&byte_encode_12(&acc));
    }
    ek[1152..1184].copy_from_slice(&rho);

    let mut dk_pke = [0u8; 1152];
    for (i, s_poly) in s_hat.iter().enumerate() {
        dk_pke[384 * i..384 * (i + 1)].copy_from_slice(&byte_encode_12(s_poly));
    }

    (ek, dk_pke)
}

fn k_pke_encrypt(
    ek: &[u8; ML_KEM_768_EK_LEN],
    m: &[u8; 32],
    r: &[u8; 32],
) -> [u8; ML_KEM_768_CT_LEN] {
    let mut t_hat = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    for (i, t_poly) in t_hat.iter_mut().enumerate() {
        let mut slice = [0u8; 384];
        slice.copy_from_slice(&ek[384 * i..384 * (i + 1)]);
        *t_poly = byte_decode_12(&slice);
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&ek[1152..1184]);

    let mut a_hat = [[[0u16; ML_KEM_N]; ML_KEM_768_K]; ML_KEM_768_K];
    for i in 0..ML_KEM_768_K {
        for j in 0..ML_KEM_768_K {
            a_hat[i][j] = sample_ntt(&rho, j as u8, i as u8);
        }
    }

    let mut y_hat = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    let mut e1 = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    let mut nonce = 0u8;
    for y_poly in &mut y_hat {
        *y_poly = ntt(&sample_poly_cbd2(&prf_eta2(r, nonce)));
        nonce += 1;
    }
    for e1_poly in &mut e1 {
        *e1_poly = sample_poly_cbd2(&prf_eta2(r, nonce));
        nonce += 1;
    }
    let e2 = sample_poly_cbd2(&prf_eta2(r, nonce));

    let mut ct = [0u8; ML_KEM_768_CT_LEN];
    for i in 0..ML_KEM_768_K {
        let mut acc = [0u16; ML_KEM_N];
        for j in 0..ML_KEM_768_K {
            let prod = multiply_ntts(&a_hat[j][i], &y_hat[j]);
            acc = poly_add(&acc, &prod);
        }
        let u_i = poly_add(&ntt_inv(&acc), &e1[i]);
        let mut u_comp = [0u16; ML_KEM_N];
        for idx in 0..ML_KEM_N {
            u_comp[idx] = compress_d(u_i[idx], 10);
        }
        ct[320 * i..320 * (i + 1)].copy_from_slice(&byte_encode_10(&u_comp));
    }

    let m_bits = byte_decode_1(m);
    let mut mu = [0u16; ML_KEM_N];
    for idx in 0..ML_KEM_N {
        mu[idx] = decompress_d(m_bits[idx], 1);
    }

    let mut inner = [0u16; ML_KEM_N];
    for j in 0..ML_KEM_768_K {
        let prod = multiply_ntts(&t_hat[j], &y_hat[j]);
        inner = poly_add(&inner, &prod);
    }
    let v = poly_add(&poly_add(&ntt_inv(&inner), &e2), &mu);
    let mut v_comp = [0u16; ML_KEM_N];
    for idx in 0..ML_KEM_N {
        v_comp[idx] = compress_d(v[idx], 4);
    }
    ct[960..1088].copy_from_slice(&byte_encode_4(&v_comp));
    ct
}

fn k_pke_decrypt(dk_pke: &[u8; 1152], ct: &[u8; ML_KEM_768_CT_LEN]) -> [u8; 32] {
    let mut u_prime = [[0u16; ML_KEM_N]; ML_KEM_768_K];
    for (i, u_poly) in u_prime.iter_mut().enumerate() {
        let mut c1_i = [0u8; 320];
        c1_i.copy_from_slice(&ct[320 * i..320 * (i + 1)]);
        let dec = byte_decode_10(&c1_i);
        for idx in 0..ML_KEM_N {
            u_poly[idx] = decompress_d(dec[idx], 10);
        }
    }

    let mut c2 = [0u8; 128];
    c2.copy_from_slice(&ct[960..1088]);
    let v_dec = byte_decode_4(&c2);
    let mut v_prime = [0u16; ML_KEM_N];
    for idx in 0..ML_KEM_N {
        v_prime[idx] = decompress_d(v_dec[idx], 4);
    }

    let mut inner = [0u16; ML_KEM_N];
    for (i, u_poly) in u_prime.iter().enumerate() {
        let mut s_slice = [0u8; 384];
        s_slice.copy_from_slice(&dk_pke[384 * i..384 * (i + 1)]);
        let s_i = byte_decode_12(&s_slice);
        let prod = multiply_ntts(&s_i, &ntt(u_poly));
        inner = poly_add(&inner, &prod);
    }

    let w = poly_sub(&v_prime, &ntt_inv(&inner));
    let mut m_bits = [0u16; ML_KEM_N];
    for idx in 0..ML_KEM_N {
        m_bits[idx] = compress_d(w[idx], 1);
    }
    byte_encode_1(&m_bits)
}

/// **FIPS 203 Algorithm 16 `ML-KEM.KeyGen_internal(d, z)`** -> `(ek: [u8; 1184], dk: [u8; 2400])`.
pub fn ml_kem_768_keygen_internal(
    d: &[u8; 32],
    z: &[u8; 32],
) -> ([u8; ML_KEM_768_EK_LEN], [u8; ML_KEM_768_DK_LEN]) {
    let (ek, dk_pke) = k_pke_keygen(d);
    let h_ek = sha3_256(&ek);
    let mut dk = [0u8; ML_KEM_768_DK_LEN];
    dk[0..1152].copy_from_slice(&dk_pke);
    dk[1152..2336].copy_from_slice(&ek);
    dk[2336..2368].copy_from_slice(&h_ek);
    dk[2368..2400].copy_from_slice(z);
    (ek, dk)
}

/// **FIPS 203 Algorithm 17 `ML-KEM.Encaps_internal(ek, m)`** -> `(ct: [u8; 1088], k: [u8; 32])`.
pub fn ml_kem_768_encaps_internal(
    ek: &[u8; ML_KEM_768_EK_LEN],
    m: &[u8; 32],
) -> ([u8; ML_KEM_768_CT_LEN], [u8; ML_KEM_768_SS_LEN]) {
    let h_ek = sha3_256(ek);
    let mut g_in = [0u8; 64];
    g_in[0..32].copy_from_slice(m);
    g_in[32..64].copy_from_slice(&h_ek);
    let g_out = sha3_512(&g_in);

    let mut k_out = [0u8; 32];
    let mut r = [0u8; 32];
    k_out.copy_from_slice(&g_out[0..32]);
    r.copy_from_slice(&g_out[32..64]);

    let ct = k_pke_encrypt(ek, m, &r);
    (ct, k_out)
}

/// **FIPS 203 Algorithm 18 `ML-KEM.Decaps_internal(dk, ct)`** -> `[u8; 32]`.
///
/// Executes Fujisaki–Okamoto re-encryption and selects between `K'` and the implicit-rejection
/// pseudorandom fallback `K̄ = J(z || c) = SHAKE256(z || c, 32)` in **constant time** (`0` branches
/// on ciphertext validity).
pub fn ml_kem_768_decaps_internal(
    dk: &[u8; ML_KEM_768_DK_LEN],
    ct: &[u8; ML_KEM_768_CT_LEN],
) -> [u8; ML_KEM_768_SS_LEN] {
    let mut dk_pke = [0u8; 1152];
    dk_pke.copy_from_slice(&dk[0..1152]);
    let mut ek_pke = [0u8; ML_KEM_768_EK_LEN];
    ek_pke.copy_from_slice(&dk[1152..2336]);
    let h = &dk[2336..2368];
    let z = &dk[2368..2400];

    let m_prime = k_pke_decrypt(&dk_pke, ct);

    let mut g_in = [0u8; 64];
    g_in[0..32].copy_from_slice(&m_prime);
    g_in[32..64].copy_from_slice(h);
    let g_out = sha3_512(&g_in);
    let mut k_prime = [0u8; 32];
    let mut r_prime = [0u8; 32];
    k_prime.copy_from_slice(&g_out[0..32]);
    r_prime.copy_from_slice(&g_out[32..64]);

    // Implicit-rejection fallback K̄ = J(z || c) = SHAKE256(z || c, 32).
    let mut j_sp = Shake256::new(0x1f);
    j_sp.absorb(z);
    j_sp.absorb(ct);
    let mut k_bar = [0u8; 32];
    j_sp.squeeze(&mut k_bar);

    let c_prime = k_pke_encrypt(&ek_pke, &m_prime, &r_prime);

    // Branchless constant-time comparison across all 1088 ciphertext bytes.
    let mut diff = 0u16;
    for i in 0..ML_KEM_768_CT_LEN {
        diff |= u16::from(ct[i] ^ c_prime[i]);
    }
    // mismatch_mask == 0xff iff diff != 0, else 0x00.
    let mismatch_mask = (((diff | diff.wrapping_neg()) >> 15) as u8).wrapping_neg();

    let mut shared_secret = [0u8; ML_KEM_768_SS_LEN];
    for i in 0..ML_KEM_768_SS_LEN {
        shared_secret[i] = (k_prime[i] & !mismatch_mask) | (k_bar[i] & mismatch_mask);
    }
    shared_secret
}

/// **FIPS 203 Algorithm 20 `ML-KEM.Encaps`** with mandatory §7.2 `validate_encaps_key` check.
pub fn ml_kem_768_encaps(
    ek: &[u8],
    m: &[u8; 32],
) -> Result<([u8; ML_KEM_768_CT_LEN], [u8; ML_KEM_768_SS_LEN]), MlKemError> {
    let ek_arr = validate_encaps_key(ek)?;
    Ok(ml_kem_768_encaps_internal(ek_arr, m))
}

/// **FIPS 203 Algorithm 21 `ML-KEM.Decaps`** with mandatory §7.3 `validate_decaps_key` & length check.
pub fn ml_kem_768_decaps(dk: &[u8], ct: &[u8]) -> Result<[u8; ML_KEM_768_SS_LEN], MlKemError> {
    let ct_arr: &[u8; ML_KEM_768_CT_LEN] = ct
        .try_into()
        .map_err(|_| MlKemError::InvalidCiphertextLength { actual: ct.len() })?;
    let dk_arr = validate_decaps_key(dk)?;
    Ok(ml_kem_768_decaps_internal(dk_arr, ct_arr))
}
