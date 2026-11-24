#![forbid(unsafe_code)]
//! Pure-Rust Sandstorm `.spk` Verifier (`SHA-512` + RFC 8032 `Ed25519` `verify_strict`),
//! Streaming-Bounded XZ/LZMA2 Container Codec, and Fixed Role/Permission Manifest Extractor
//! (closing `sandstorm-package/src/manifest.rs:287` & `spk.rs:64`).
//!
//! Quarried and hardened from `breadstuffs/sandstorm-package/src/{spk.rs,manifest.rs}` +
//! `minidregg/native/spk-rpc/src/{bridge_config.rs,protocol.rs}` with `#![forbid(unsafe_code)]`
//! and shared SHA-2 and signature verification from `obend-primitives`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use obend_primitives::{
    ct::{ct_eq, ct_eq_32},
    ed25519,
    sha256::sha256,
    sha512::{sha512, Sha512},
};
use serde::{Deserialize, Serialize};

use crate::capnp_wire::{self, Message, Struct, WireContent, WireFile};

/// Default upper bound on accepted decompressed `.spk` stream bytes (`256 MiB`).
pub const MAX_DECOMPRESSED_BYTES: usize = 256 * 1024 * 1024;

/// Canonical 8-byte Sandstorm `.spk` magic (`package.capnp:magicNumber`).
pub const SPK_MAGIC: [u8; 8] = [0x8f, 0xc6, 0xcd, 0xef, 0x45, 0x1a, 0xea, 0x96];

/// Conventional manifest path at the `.spk` archive root.
pub const MANIFEST_PATH: &str = "sandstorm-manifest";

/// Conventional `sandstorm-http-bridge` permission/role configuration path at the `.spk` archive root.
pub const BRIDGE_CONFIG_PATH: &str = "sandstorm-http-bridge-config";

const MAX_ARCHIVE_DEPTH: usize = 64;
const MAX_ARCHIVE_FILES: usize = 100_000;
const MAX_ARCHIVE_NAME_BYTES: usize = 16 * 1024 * 1024;
const MAX_FILE_NAME_BYTES: usize = 255;
const MAX_BRIDGE_CONFIG_BYTES: usize = 64 * 1024;
const MAX_API_PATH_BYTES: usize = 4096;

/// Sandstorm Crockford-style base32 alphabet (32 symbols, omits `b`, `i`, `l`, `o`, no padding).
const SANDSTORM_BASE32: &[u8; 32] = b"0123456789acdefghjkmnpqrstuvwxyz";

/// Encode arbitrary bytes in Sandstorm's unpadded base32 alphabet (`AppId` encoding).
pub fn sandstorm_base32_encode(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return String::new();
    }
    let out_len = (bytes.len() * 8).div_ceil(5);
    let mut out = String::with_capacity(out_len);
    let mut acc = 0u32;
    let mut bits = 0u32;
    for &b in bytes {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            let idx = ((acc >> bits) & 0x1F) as usize;
            out.push(SANDSTORM_BASE32[idx] as char);
        }
    }
    if bits > 0 {
        let idx = ((acc << (5 - bits)) & 0x1F) as usize;
        out.push(SANDSTORM_BASE32[idx] as char);
    }
    out
}

// =========================================================================
// Pure-Rust RFC 8032 Ed25519 (`sign` + `verify_strict`) over the shared SHA-512 core
// =========================================================================

const MASK51: u64 = (1u64 << 51) - 1;

/// Group order $\ell = 2^{252} + 27742317777372353535851937790883648493$ (little-endian bytes).
pub const ED25519_L: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

#[derive(Clone, Copy, Debug)]
struct Fe255([u64; 5]);

impl Fe255 {
    const ZERO: Self = Self([0; 5]);
    const ONE: Self = Self([1, 0, 0, 0, 0]);

    fn from_u64(v: u64) -> Self {
        Self([v & MASK51, v >> 51, 0, 0, 0])
    }

    fn from_bytes_unchecked(b: &[u8; 32]) -> Self {
        let load64 = |off: usize| -> u64 {
            u64::from_le_bytes([
                b[off],
                b[off + 1],
                b[off + 2],
                b[off + 3],
                b[off + 4],
                b[off + 5],
                b[off + 6],
                b[off + 7],
            ])
        };
        let l0 = load64(0) & MASK51;
        let l1 = (load64(6) >> 3) & MASK51;
        let l2 = (load64(12) >> 6) & MASK51;
        let l3 = (load64(19) >> 1) & MASK51;
        let l4 = (load64(24) >> 12) & MASK51;
        Self([l0, l1, l2, l3, l4])
    }

    /// Canonical RFC 8032 §5.1.3 field decoding: returns `(y, x_sign_bit)` iff `0 <= y < 2^255 - 19`.
    fn from_bytes_canonical(bytes: &[u8; 32]) -> Option<(Self, u8)> {
        let sign = (bytes[31] >> 7) & 1;
        let mut masked = *bytes;
        masked[31] &= 0x7F;
        let fe = Self::from_bytes_unchecked(&masked);
        if fe.to_bytes() != masked {
            return None;
        }
        Some((fe, sign))
    }

    fn to_bytes(self) -> [u8; 32] {
        let mut l = self.0;
        for _ in 0..2 {
            let c0 = l[0] >> 51;
            l[0] &= MASK51;
            l[1] += c0;
            let c1 = l[1] >> 51;
            l[1] &= MASK51;
            l[2] += c1;
            let c2 = l[2] >> 51;
            l[2] &= MASK51;
            l[3] += c2;
            let c3 = l[3] >> 51;
            l[3] &= MASK51;
            l[4] += c3;
            let c4 = l[4] >> 51;
            l[4] &= MASK51;
            l[0] += c4 * 19;
        }
        let mut q = (l[0] + 19) >> 51;
        q = (l[1] + q) >> 51;
        q = (l[2] + q) >> 51;
        q = (l[3] + q) >> 51;
        q = (l[4] + q) >> 51;

        l[0] += 19 * q;
        let c0 = l[0] >> 51;
        l[0] &= MASK51;
        l[1] += c0;
        let c1 = l[1] >> 51;
        l[1] &= MASK51;
        l[2] += c1;
        let c2 = l[2] >> 51;
        l[2] &= MASK51;
        l[3] += c2;
        let c3 = l[3] >> 51;
        l[3] &= MASK51;
        l[4] = (l[4] + c3) & MASK51;

        let mut out = [0u8; 32];
        let mut bit_pos = 0usize;
        for limb in l {
            for b in 0..51 {
                if ((limb >> b) & 1) == 1 {
                    out[bit_pos / 8] |= 1u8 << (bit_pos % 8);
                }
                bit_pos += 1;
            }
        }
        out
    }

    fn eq_ct(self, other: Self) -> bool {
        ct_eq_32(&self.to_bytes(), &other.to_bytes())
    }

    fn is_zero(self) -> bool {
        self.eq_ct(Self::ZERO)
    }

    fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ])
    }

    fn sub(self, rhs: Self) -> Self {
        // Add `2 * p` to avoid unsigned underflow (`2 * (2^51 - 19) = 0xfff_ffff_ffff_ffda`, `2 * (2^51 - 1) = 0xfff_ffff_ffff_fffe`).
        const TWO_P0: u64 = 0x000f_ffff_ffff_ffda;
        const TWO_PN: u64 = 0x000f_ffff_ffff_fffe;
        let mut r = [
            (self.0[0] + TWO_P0) - rhs.0[0],
            (self.0[1] + TWO_PN) - rhs.0[1],
            (self.0[2] + TWO_PN) - rhs.0[2],
            (self.0[3] + TWO_PN) - rhs.0[3],
            (self.0[4] + TWO_PN) - rhs.0[4],
        ];
        let c0 = r[0] >> 51;
        r[0] &= MASK51;
        r[1] += c0;
        let c1 = r[1] >> 51;
        r[1] &= MASK51;
        r[2] += c1;
        let c2 = r[2] >> 51;
        r[2] &= MASK51;
        r[3] += c2;
        let c3 = r[3] >> 51;
        r[3] &= MASK51;
        r[4] += c3;
        let c4 = r[4] >> 51;
        r[4] &= MASK51;
        r[0] += c4 * 19;
        Self(r)
    }

    fn neg(self) -> Self {
        Self::ZERO.sub(self)
    }

    fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;
        let b1_19 = (b[1] as u128) * 19;
        let b2_19 = (b[2] as u128) * 19;
        let b3_19 = (b[3] as u128) * 19;
        let b4_19 = (b[4] as u128) * 19;

        let t0 = (a[0] as u128) * (b[0] as u128)
            + (a[1] as u128) * b4_19
            + (a[2] as u128) * b3_19
            + (a[3] as u128) * b2_19
            + (a[4] as u128) * b1_19;
        let mut t1 = (a[0] as u128) * (b[1] as u128)
            + (a[1] as u128) * (b[0] as u128)
            + (a[2] as u128) * b4_19
            + (a[3] as u128) * b3_19
            + (a[4] as u128) * b2_19;
        let mut t2 = (a[0] as u128) * (b[2] as u128)
            + (a[1] as u128) * (b[1] as u128)
            + (a[2] as u128) * (b[0] as u128)
            + (a[3] as u128) * b4_19
            + (a[4] as u128) * b3_19;
        let mut t3 = (a[0] as u128) * (b[3] as u128)
            + (a[1] as u128) * (b[2] as u128)
            + (a[2] as u128) * (b[1] as u128)
            + (a[3] as u128) * (b[0] as u128)
            + (a[4] as u128) * b4_19;
        let mut t4 = (a[0] as u128) * (b[4] as u128)
            + (a[1] as u128) * (b[3] as u128)
            + (a[2] as u128) * (b[2] as u128)
            + (a[3] as u128) * (b[1] as u128)
            + (a[4] as u128) * (b[0] as u128);

        let mut c0 = (t0 as u64) & MASK51;
        t1 += t0 >> 51;
        let mut c1 = (t1 as u64) & MASK51;
        t2 += t1 >> 51;
        let c2 = (t2 as u64) & MASK51;
        t3 += t2 >> 51;
        let c3 = (t3 as u64) & MASK51;
        t4 += t3 >> 51;
        let c4 = (t4 as u64) & MASK51;
        let carry = ((t4 >> 51) as u64) * 19;
        c0 += carry;
        c1 += c0 >> 51;
        c0 &= MASK51;
        Self([c0, c1, c2, c3, c4])
    }

    fn square(self) -> Self {
        self.mul(self)
    }

    /// Modular exponentiation $x^e \bmod p$ where `exp_bits` is a 255-bit little-endian byte array.
    fn pow_le_bytes(self, exp: &[u8; 32]) -> Self {
        let mut res = Self::ONE;
        let mut base = self;
        for &byte in exp {
            for bit in 0..8 {
                if ((byte >> bit) & 1) == 1 {
                    res = res.mul(base);
                }
                base = base.square();
            }
        }
        res
    }

    /// $x^{p - 2} \bmod p$ (`p - 2 = 2^255 - 21`).
    fn invert(self) -> Self {
        let mut exp = [0xFFu8; 32];
        exp[0] = 0xEB; // 256 - 21 = 235 = 0xEB
        exp[31] = 0x7F;
        self.pow_le_bytes(&exp)
    }

    /// $x^{(p - 5) / 8} \bmod p = x^{2^{252} - 3} \bmod p$.
    fn pow_p_minus_5_div_8(self) -> Self {
        let mut exp = [0xFFu8; 32];
        exp[0] = 0xFD; // 256 - 3 = 253 = 0xFD
        exp[31] = 0x0F; // 2^252 - 1 has top byte 0x0F
        self.pow_le_bytes(&exp)
    }
}

fn curve_d() -> Fe255 {
    // d = -121665 / 121666 mod p
    Fe255::from_u64(121_665)
        .neg()
        .mul(Fe255::from_u64(121_666).invert())
}

fn sqrt_minus_one() -> Fe255 {
    // 2^((p - 1) / 4) mod p, where (p - 1)/4 = 2^253 - 5
    let mut exp = [0xFFu8; 32];
    exp[0] = 0xFB; // 256 - 5 = 251 = 0xFB
    exp[31] = 0x1F; // 2^253 - 1 has top byte 0x1F
    Fe255::from_u64(2).pow_le_bytes(&exp)
}

/// Extended Twisted Edwards point $(X : Y : Z : T)$ with $X Y = Z T$ on $-x^2 + y^2 = 1 + d x^2 y^2$.
#[derive(Clone, Copy, Debug)]
struct GeP3 {
    x: Fe255,
    y: Fe255,
    z: Fe255,
    t: Fe255,
}

impl GeP3 {
    const IDENTITY: Self = Self {
        x: Fe255::ZERO,
        y: Fe255::ONE,
        z: Fe255::ONE,
        t: Fe255::ZERO,
    };

    fn basepoint() -> Self {
        // RFC 8032 §5.1: B has y = 4/5 mod p and positive (even) x (`sign == 0`).
        let y = Fe255::from_u64(4).mul(Fe255::from_u64(5).invert());
        let mut enc = y.to_bytes();
        enc[31] &= 0x7F;
        Self::from_bytes_strict(&enc).expect("canonical Ed25519 basepoint")
    }

    /// Strict RFC 8032 §5.1.3 point decompression rejecting non-canonical $y \ge p$, off-curve $y$,
    /// and negative zero ($x = 0, \text{sign} = 1$).
    fn from_bytes_strict(bytes: &[u8; 32]) -> Option<Self> {
        let (y, sign) = Fe255::from_bytes_canonical(bytes)?;
        let d = curve_d();
        let y2 = y.square();
        let u = y2.sub(Fe255::ONE);
        let v = d.mul(y2).add(Fe255::ONE);
        let v3 = v.square().mul(v);
        let v7 = v3.square().mul(v);
        let uv7 = u.mul(v7);
        let mut x = u.mul(v3).mul(uv7.pow_p_minus_5_div_8());

        let vx2 = v.mul(x.square());
        if vx2.eq_ct(u) {
            // root valid
        } else if vx2.eq_ct(u.neg()) {
            x = x.mul(sqrt_minus_one());
        } else {
            return None;
        }

        if x.is_zero() && sign == 1 {
            return None;
        }
        if (x.to_bytes()[0] & 1) != sign {
            x = x.neg();
        }
        Some(Self {
            x,
            y,
            z: Fe255::ONE,
            t: x.mul(y),
        })
    }

    fn to_bytes(self) -> [u8; 32] {
        let recip = self.z.invert();
        let x = self.x.mul(recip);
        let y = self.y.mul(recip);
        let mut out = y.to_bytes();
        out[31] |= (x.to_bytes()[0] & 1) << 7;
        out
    }

    /// Unified complete addition on $-x^2 + y^2 = 1 + d x^2 y^2$ (Hisil et al. 2008 §3.1).
    fn add(self, rhs: Self, two_d: Fe255) -> Self {
        let a = self.y.sub(self.x).mul(rhs.y.sub(rhs.x));
        let b = self.y.add(self.x).mul(rhs.y.add(rhs.x));
        let c = self.t.mul(two_d).mul(rhs.t);
        let z2 = self.z.mul(rhs.z);
        let d = z2.add(z2);
        let e = b.sub(a);
        let f = d.sub(c);
        let g = d.add(c);
        let h = b.add(a);
        Self {
            x: e.mul(f),
            y: g.mul(h),
            t: e.mul(h),
            z: f.mul(g),
        }
    }

    fn double(self, two_d: Fe255) -> Self {
        self.add(self, two_d)
    }

    fn scalar_mul(self, scalar_le: &[u8; 32], two_d: Fe255) -> Self {
        let mut acc = Self::IDENTITY;
        let mut addend = self;
        for &byte in scalar_le {
            for bit in 0..8 {
                if ((byte >> bit) & 1) == 1 {
                    acc = acc.add(addend, two_d);
                }
                addend = addend.double(two_d);
            }
        }
        acc
    }
}

fn le_lt_32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    for i in (0..32).rev() {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
    }
    false
}

/// Exact 33-byte little-endian conditional subtraction of `ED25519_L`.
fn sub_ell_if_ge(acc: &mut [u8; 33]) {
    let mut diff = [0u8; 33];
    let mut borrow = 0i16;
    for i in 0..33 {
        let l_byte = if i < 32 { i16::from(ED25519_L[i]) } else { 0 };
        let d = i16::from(acc[i]) - l_byte - borrow;
        if d < 0 {
            diff[i] = (d + 256) as u8;
            borrow = 1;
        } else {
            diff[i] = d as u8;
            borrow = 0;
        }
    }
    if borrow == 0 {
        *acc = diff;
    }
}

/// Reduce a 512-bit little-endian SHA-512 output modulo $\ell$.
fn reduce_512_mod_ell(wide: &[u8; 64]) -> [u8; 32] {
    let mut rem = [0u8; 33];
    for byte_idx in (0..64).rev() {
        let b = wide[byte_idx];
        for bit in (0..8).rev() {
            let mut carry = (b >> bit) & 1;
            for r in &mut rem {
                let next = (*r << 1) | carry;
                carry = *r >> 7;
                *r = next;
            }
            sub_ell_if_ge(&mut rem);
        }
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&rem[..32]);
    out
}

fn add_mod_ell(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut sum = [0u8; 33];
    let mut carry = 0u16;
    for i in 0..32 {
        let v = u16::from(a[i]) + u16::from(b[i]) + carry;
        sum[i] = v as u8;
        carry = v >> 8;
    }
    sum[32] = carry as u8;
    sub_ell_if_ge(&mut sum);
    sub_ell_if_ge(&mut sum);
    let mut out = [0u8; 32];
    out.copy_from_slice(&sum[..32]);
    out
}

/// Compute `(r + k * a) mod ell` where `a` is a clamped 32-byte Ed25519 secret scalar.
fn mul_add_mod_ell(r: &[u8; 32], k: &[u8; 32], a: &[u8; 32]) -> [u8; 32] {
    let mut prod = [0u8; 32];
    let mut a_mod = [0u8; 33];
    a_mod[..32].copy_from_slice(a);
    while a_mod[32] != 0 || !le_lt_32(a_mod[..32].try_into().unwrap(), &ED25519_L) {
        sub_ell_if_ge(&mut a_mod);
    }
    let mut term = [0u8; 32];
    term.copy_from_slice(&a_mod[..32]);

    for &byte in k {
        for bit in 0..8 {
            if ((byte >> bit) & 1) == 1 {
                prod = add_mod_ell(&prod, &term);
            }
            term = add_mod_ell(&term, &term);
        }
    }
    add_mod_ell(r, &prod)
}

/// Pure-Rust RFC 8032 Ed25519 signing key (`32`-byte seed).
#[derive(Clone)]
pub struct Ed25519SigningKey {
    seed: [u8; 32],
    public_key: [u8; 32],
}

impl Drop for Ed25519SigningKey {
    fn drop(&mut self) {
        self.seed.fill(0);
        std::hint::black_box(&self.seed);
    }
}

impl Ed25519SigningKey {
    pub fn from_bytes(seed: &[u8; 32]) -> Self {
        let mut h: [u8; 64] = sha512(seed);
        let mut scalar = [0u8; 32];
        scalar.copy_from_slice(&h[..32]);
        scalar[0] &= 248;
        scalar[31] &= 127;
        scalar[31] |= 64;

        let d = curve_d();
        let two_d = d.add(d);
        let public_key = GeP3::basepoint().scalar_mul(&scalar, two_d).to_bytes();
        h.fill(0);
        scalar.fill(0);
        std::hint::black_box((&h, &scalar));
        Self {
            seed: *seed,
            public_key,
        }
    }

    pub fn verifying_key_bytes(&self) -> [u8; 32] {
        self.public_key
    }

    pub fn sign(&self, msg: &[u8]) -> [u8; 64] {
        let mut h: [u8; 64] = sha512(&self.seed);
        let mut a = [0u8; 32];
        a.copy_from_slice(&h[..32]);
        a[0] &= 248;
        a[31] &= 127;
        a[31] |= 64;
        let prefix = &h[32..64];

        let mut r_hasher = Sha512::new();
        r_hasher.update(prefix);
        r_hasher.update(msg);
        let mut r_wide = [0; 64];
        r_hasher.finalize_into(&mut r_wide);
        let r_scalar = reduce_512_mod_ell(&r_wide);

        let d = curve_d();
        let two_d = d.add(d);
        let big_r = GeP3::basepoint().scalar_mul(&r_scalar, two_d).to_bytes();

        let mut k_hasher = Sha512::new();
        k_hasher.update(&big_r);
        k_hasher.update(&self.public_key);
        k_hasher.update(msg);
        let mut k_wide = [0; 64];
        k_hasher.finalize_into(&mut k_wide);
        let k_scalar = reduce_512_mod_ell(&k_wide);

        let s_scalar = mul_add_mod_ell(&r_scalar, &k_scalar, &a);
        h.fill(0);
        a.fill(0);
        std::hint::black_box((&h, &a));

        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&big_r);
        sig[32..].copy_from_slice(&s_scalar);
        sig
    }
}

/// Strict RFC 8032 + `ed25519-dalek` `verify_strict` verifier:
/// 1. Rejects non-canonical $s \ge \ell$.
/// 2. Decompresses `public_key` ($A$) and `sig[..32]` ($R$) strictly ($y < p$, on-curve, no $-0$).
/// 3. Rejects small-order (8-torsion) $A$ (`[8]A == O`) AND small-order $R$ (`[8]R == O`),
///    killing universal weak-key `.spk` forgeries!
/// 4. Enforces the cofactorless group equation $[s]B = R + [k]A$.
pub fn ed25519_verify_strict(
    public_key: &[u8; 32],
    msg: &[u8],
    signature: &[u8; 64],
) -> Result<(), SpkError> {
    ed25519::verify_strict(public_key, msg, signature)
        .then_some(())
        .ok_or(SpkError::BadSignature)
}

// =========================================================================
// Pure-Rust Streaming-Bounded XZ + LZMA2 Container Codec
// =========================================================================

const XZ_HEADER_MAGIC: [u8; 6] = [0xFD, b'7', b'z', b'X', b'Z', 0x00];
const XZ_FOOTER_MAGIC: [u8; 2] = *b"YZ";

fn crc32_ieee(data: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in data {
        crc ^= u32::from(b);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

fn crc64_ecma(data: &[u8]) -> u64 {
    let mut crc = 0xFFFF_FFFF_FFFF_FFFFu64;
    for &b in data {
        crc ^= u64::from(b);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xC96C_5795_D787_0F42 & mask);
        }
    }
    !crc
}

fn encode_xz_varint(mut n: u64, out: &mut Vec<u8>) {
    loop {
        if n < 0x80 {
            out.push(n as u8);
            break;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
}

fn decode_xz_varint(buf: &[u8], pos: &mut usize) -> Result<u64, SpkError> {
    let mut val = 0u64;
    for i in 0..9 {
        let b = *buf
            .get(*pos)
            .ok_or_else(|| SpkError::Decompress("xz varint truncated".into()))?;
        *pos += 1;
        if i > 0 && b == 0x00 {
            return Err(SpkError::Decompress("non-canonical xz varint".into()));
        }
        val |= u64::from(b & 0x7F) << (i * 7);
        if (b & 0x80) == 0 {
            if val > (i64::MAX as u64) {
                return Err(SpkError::Decompress(
                    "xz varint exceeds 63-bit bound".into(),
                ));
            }
            return Ok(val);
        }
    }
    Err(SpkError::Decompress("xz varint too long".into()))
}

/// Compress `plain` into a standard RFC/Tukaani `.xz` stream (CRC64 check + LZMA2 uncompressed
/// chunks, 100% interoperable with `/usr/bin/xz -dc` and `lzma-rs`).
pub fn xz_compress(plain: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(plain.len() + 64);
    // 1. Stream Header (check = 0x04 CRC64)
    let stream_flags = [0x00u8, 0x04u8];
    out.extend_from_slice(&XZ_HEADER_MAGIC);
    out.extend_from_slice(&stream_flags);
    out.extend_from_slice(&crc32_ieee(&stream_flags).to_le_bytes());

    // 2. Single Block with LZMA2 filter (`id = 0x21`, `props_len = 1`, `dict_prop = 0x14` = 1 MiB)
    // Block header: [size_byte=0x02 => 12 bytes, flags=0x00 (1 filter), 0x21, 0x01, 0x14, 0, 0, 0, crc32(4B)]
    let block_start = out.len();
    let bh_body = [0x02u8, 0x00, 0x21, 0x01, 0x14, 0x00, 0x00, 0x00];
    out.extend_from_slice(&bh_body);
    out.extend_from_slice(&crc32_ieee(&bh_body).to_le_bytes());

    let comp_start = out.len();
    let mut first = true;
    for chunk in plain.chunks(65_536) {
        out.push(if first { 0x01 } else { 0x02 });
        first = false;
        let len_minus_one = (chunk.len() - 1) as u16;
        out.extend_from_slice(&len_minus_one.to_be_bytes());
        out.extend_from_slice(chunk);
    }
    out.push(0x00); // End of LZMA2 stream
    let comp_len = out.len() - comp_start;
    let unpadded_size = (12 + comp_len + 8) as u64; // header(12) + comp + crc64(8)
    while !(out.len() - block_start).is_multiple_of(4) {
        out.push(0x00);
    }
    out.extend_from_slice(&crc64_ecma(plain).to_le_bytes());

    // 3. Index: 1 record `(unpadded_size, plain.len())`
    let index_start = out.len();
    out.push(0x00); // Index indicator
    encode_xz_varint(1, &mut out);
    encode_xz_varint(unpadded_size, &mut out);
    encode_xz_varint(plain.len() as u64, &mut out);
    while !(out.len() - index_start).is_multiple_of(4) {
        out.push(0x00);
    }
    let idx_crc = crc32_ieee(&out[index_start..]);
    out.extend_from_slice(&idx_crc.to_le_bytes());
    let index_total_bytes = out.len() - index_start;

    // 4. Stream Footer
    let backward_size = ((index_total_bytes / 4) - 1) as u32;
    let mut footer_mid = [0u8; 6];
    footer_mid[0..4].copy_from_slice(&backward_size.to_le_bytes());
    footer_mid[4..6].copy_from_slice(&stream_flags);
    out.extend_from_slice(&crc32_ieee(&footer_mid).to_le_bytes());
    out.extend_from_slice(&footer_mid);
    out.extend_from_slice(&XZ_FOOTER_MAGIC);
    out
}

struct RangeDecoder<'a> {
    buf: &'a [u8],
    pos: usize,
    range: u32,
    code: u32,
}

impl<'a> RangeDecoder<'a> {
    fn new(buf: &'a [u8]) -> Result<Self, SpkError> {
        if buf.len() < 5 || buf[0] != 0x00 {
            return Err(SpkError::Decompress(
                "invalid LZMA2 range coder init".into(),
            ));
        }
        let code = u32::from_be_bytes([buf[1], buf[2], buf[3], buf[4]]);
        Ok(Self {
            buf,
            pos: 5,
            range: 0xFFFF_FFFF,
            code,
        })
    }

    fn normalize(&mut self) -> Result<(), SpkError> {
        if self.range < 0x0100_0000 {
            let b = *self
                .buf
                .get(self.pos)
                .ok_or_else(|| SpkError::Decompress("LZMA2 range stream truncated".into()))?;
            self.pos += 1;
            self.range <<= 8;
            self.code = (self.code << 8) | u32::from(b);
        }
        Ok(())
    }

    fn decode_bit(&mut self, prob: &mut u16) -> Result<u32, SpkError> {
        self.normalize()?;
        let bound = (self.range >> 11) * u32::from(*prob);
        if self.code < bound {
            self.range = bound;
            *prob += (2048 - *prob) >> 5;
            Ok(0)
        } else {
            self.range -= bound;
            self.code -= bound;
            *prob -= *prob >> 5;
            Ok(1)
        }
    }

    fn decode_direct(&mut self, num_bits: u32) -> Result<u32, SpkError> {
        let mut res = 0u32;
        for _ in 0..num_bits {
            self.normalize()?;
            self.range >>= 1;
            self.code = self.code.wrapping_sub(self.range);
            let neg = self.code >> 31;
            if neg == 1 {
                self.code = self.code.wrapping_add(self.range);
            }
            res = (res << 1) | (1 - neg);
        }
        Ok(res)
    }

    fn bit_tree(&mut self, probs: &mut [u16], num_bits: u32) -> Result<u32, SpkError> {
        let mut m = 1usize;
        for _ in 0..num_bits {
            let bit = self.decode_bit(&mut probs[m])? as usize;
            m = (m << 1) | bit;
        }
        Ok((m - (1usize << num_bits)) as u32)
    }

    fn rev_bit_tree(&mut self, probs: &mut [u16], num_bits: u32) -> Result<u32, SpkError> {
        let mut m = 1usize;
        let mut symbol = 0u32;
        for i in 0..num_bits {
            let bit = self.decode_bit(&mut probs[m])?;
            m = (m << 1) | (bit as usize);
            symbol |= bit << i;
        }
        Ok(symbol)
    }
}

struct LenDecoder {
    choice: u16,
    choice2: u16,
    low: [[u16; 8]; 16],
    mid: [[u16; 8]; 16],
    high: [u16; 256],
}

impl LenDecoder {
    fn new() -> Self {
        Self {
            choice: 1024,
            choice2: 1024,
            low: [[1024; 8]; 16],
            mid: [[1024; 8]; 16],
            high: [1024; 256],
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }

    fn decode(&mut self, rc: &mut RangeDecoder<'_>, pos_state: usize) -> Result<usize, SpkError> {
        if rc.decode_bit(&mut self.choice)? == 0 {
            Ok(rc.bit_tree(&mut self.low[pos_state], 3)? as usize)
        } else if rc.decode_bit(&mut self.choice2)? == 0 {
            Ok(8 + rc.bit_tree(&mut self.mid[pos_state], 3)? as usize)
        } else {
            Ok(16 + rc.bit_tree(&mut self.high, 8)? as usize)
        }
    }
}

struct Lzma2State {
    lc: u32,
    lp: u32,
    pb: u32,
    props_initialized: bool,
    dict_initialized: bool,
    state: usize,
    reps: [u32; 4],
    is_match: [u16; 192],
    is_rep: [u16; 12],
    is_rep_g0: [u16; 12],
    is_rep_g1: [u16; 12],
    is_rep_g2: [u16; 12],
    is_rep0_long: [u16; 192],
    pos_slot: [[u16; 64]; 4],
    spec_pos: [u16; 115],
    align: [u16; 16],
    match_len: LenDecoder,
    rep_len: LenDecoder,
    lit_probs: Vec<u16>,
    dict_reset_pos: usize,
}

impl Lzma2State {
    fn new() -> Self {
        Self {
            lc: 0,
            lp: 0,
            pb: 0,
            props_initialized: false,
            dict_initialized: false,
            state: 0,
            reps: [0; 4],
            is_match: [1024; 192],
            is_rep: [1024; 12],
            is_rep_g0: [1024; 12],
            is_rep_g1: [1024; 12],
            is_rep_g2: [1024; 12],
            is_rep0_long: [1024; 192],
            pos_slot: [[1024; 64]; 4],
            spec_pos: [1024; 115],
            align: [1024; 16],
            match_len: LenDecoder::new(),
            rep_len: LenDecoder::new(),
            lit_probs: Vec::new(),
            dict_reset_pos: 0,
        }
    }

    fn reset_probs(&mut self) {
        self.state = 0;
        self.reps = [0; 4];
        self.is_match.fill(1024);
        self.is_rep.fill(1024);
        self.is_rep_g0.fill(1024);
        self.is_rep_g1.fill(1024);
        self.is_rep_g2.fill(1024);
        self.is_rep0_long.fill(1024);
        for row in &mut self.pos_slot {
            row.fill(1024);
        }
        self.spec_pos.fill(1024);
        self.align.fill(1024);
        self.match_len.reset();
        self.rep_len.reset();
        let num_lit_tables = 1usize << (self.lc + self.lp);
        self.lit_probs.clear();
        self.lit_probs.resize(num_lit_tables * 0x300, 1024);
    }

    fn decode_compressed_chunk(
        &mut self,
        pack: &[u8],
        unpack_size: usize,
        out: &mut Vec<u8>,
        dict_limit: usize,
    ) -> Result<(), SpkError> {
        let mut rc = RangeDecoder::new(pack)?;
        let target_end = out.len() + unpack_size;
        out.reserve(unpack_size);
        let lp_mask = (1usize << self.lp) - 1;
        let pb_mask = (1usize << self.pb) - 1;

        while out.len() < target_end {
            let rel_pos = out.len() - self.dict_reset_pos;
            let pos_state = rel_pos & pb_mask;

            if rc.decode_bit(&mut self.is_match[self.state * 16 + pos_state])? == 0 {
                let prev_byte = if rel_pos == 0 {
                    0u8
                } else {
                    out[out.len() - 1]
                };
                let lit_state =
                    ((rel_pos & lp_mask) << self.lc) | ((prev_byte as usize) >> (8 - self.lc));
                let probs = &mut self.lit_probs[lit_state * 0x300..(lit_state + 1) * 0x300];
                let mut symbol = 1usize;
                if self.state >= 7 {
                    let dist = (self.reps[0] as usize) + 1;
                    if dist > rel_pos || dist > dict_limit {
                        return Err(SpkError::Decompress(
                            "LZMA2 matched literal distance OOB".into(),
                        ));
                    }
                    let mut match_byte = out[out.len() - dist];
                    while symbol < 0x100 {
                        let match_bit = (match_byte >> 7) & 1;
                        match_byte <<= 1;
                        let bit = rc
                            .decode_bit(&mut probs[0x100 + ((match_bit as usize) << 8) + symbol])?
                            as usize;
                        symbol = (symbol << 1) | bit;
                        if bit != match_bit as usize {
                            while symbol < 0x100 {
                                let b2 = rc.decode_bit(&mut probs[symbol])? as usize;
                                symbol = (symbol << 1) | b2;
                            }
                            break;
                        }
                    }
                } else {
                    while symbol < 0x100 {
                        let bit = rc.decode_bit(&mut probs[symbol])? as usize;
                        symbol = (symbol << 1) | bit;
                    }
                }
                out.push((symbol & 0xFF) as u8);
                self.state = if self.state < 4 {
                    0
                } else if self.state < 10 {
                    self.state - 3
                } else {
                    self.state - 6
                };
            } else {
                let len: usize;
                if rc.decode_bit(&mut self.is_rep[self.state])? == 0 {
                    self.reps[3] = self.reps[2];
                    self.reps[2] = self.reps[1];
                    self.reps[1] = self.reps[0];
                    len = self.match_len.decode(&mut rc, pos_state)? + 2;
                    self.state = if self.state < 7 { 7 } else { 10 };
                    let len_ctx = (len - 2).min(3);
                    let pos_slot = rc.bit_tree(&mut self.pos_slot[len_ctx], 6)?;
                    if pos_slot < 4 {
                        self.reps[0] = pos_slot;
                    } else {
                        let num_direct = (pos_slot >> 1) - 1;
                        let mut dist = (2 | (pos_slot & 1)) << num_direct;
                        if pos_slot < 14 {
                            let base = (dist - pos_slot) as usize;
                            dist += rc.rev_bit_tree(&mut self.spec_pos[base..], num_direct)?;
                        } else {
                            dist += rc.decode_direct(num_direct - 4)? << 4;
                            dist += rc.rev_bit_tree(&mut self.align, 4)?;
                        }
                        self.reps[0] = dist;
                    }
                } else if rc.decode_bit(&mut self.is_rep_g0[self.state])? == 0 {
                    if rc.decode_bit(&mut self.is_rep0_long[self.state * 16 + pos_state])? == 0 {
                        self.state = if self.state < 7 { 9 } else { 11 };
                        len = 1;
                    } else {
                        self.state = if self.state < 7 { 8 } else { 11 };
                        len = self.rep_len.decode(&mut rc, pos_state)? + 2;
                    }
                } else {
                    let dist: u32;
                    if rc.decode_bit(&mut self.is_rep_g1[self.state])? == 0 {
                        dist = self.reps[1];
                    } else {
                        if rc.decode_bit(&mut self.is_rep_g2[self.state])? == 0 {
                            dist = self.reps[2];
                        } else {
                            dist = self.reps[3];
                            self.reps[3] = self.reps[2];
                        }
                        self.reps[2] = self.reps[1];
                    }
                    self.reps[1] = self.reps[0];
                    self.reps[0] = dist;
                    len = self.rep_len.decode(&mut rc, pos_state)? + 2;
                    self.state = if self.state < 7 { 8 } else { 11 };
                }

                let lookback = (self.reps[0] as usize).saturating_add(1);
                let cur_rel = out.len() - self.dict_reset_pos;
                if lookback == 0
                    || lookback > cur_rel
                    || lookback > dict_limit
                    || out.len() + len > target_end
                {
                    return Err(SpkError::Decompress(
                        "LZMA2 match distance/length OOB".into(),
                    ));
                }
                for _ in 0..len {
                    let b = out[out.len() - lookback];
                    out.push(b);
                }
            }
        }
        rc.normalize()?;
        if rc.code != 0 || rc.pos != pack.len() {
            return Err(SpkError::Decompress(
                "LZMA2 chunk trailing/corrupt range state".into(),
            ));
        }
        Ok(())
    }
}

/// Streaming-bounded `.xz` decompressor: checks `limit` BEFORE every chunk expansion (closing
/// `sandstorm-package/src/spk.rs:64` block-buffering gap), verifies all stream/block/index CRCs,
/// and refuses any trailing bytes past the `YZ` footer!
pub fn xz_decompress_bounded(input: &[u8], limit: usize) -> Result<Vec<u8>, SpkError> {
    if input.len() < 24 || input[..6] != XZ_HEADER_MAGIC {
        return Err(SpkError::Decompress("bad xz header magic".into()));
    }
    let stream_flags = [input[6], input[7]];
    let hdr_crc = u32::from_le_bytes([input[8], input[9], input[10], input[11]]);
    if crc32_ieee(&stream_flags) != hdr_crc || stream_flags[0] != 0 {
        return Err(SpkError::Decompress("corrupt xz stream header".into()));
    }
    let check_size = match stream_flags[1] {
        0x00 => 0usize,
        0x01 => 4usize,
        0x04 => 8usize,
        0x0A => 32usize,
        _ => return Err(SpkError::Decompress("unsupported xz check type".into())),
    };

    let mut pos = 12usize;
    let mut out = Vec::new();
    let mut blocks: Vec<(u64, u64)> = Vec::new();

    while pos < input.len() && input[pos] != 0x00 {
        let block_start = pos;
        let hdr_size = (usize::from(input[pos]) + 1) * 4;
        let hdr = input
            .get(pos..pos + hdr_size)
            .ok_or_else(|| SpkError::Decompress("xz block header truncated".into()))?;
        let want_crc = u32::from_le_bytes([
            hdr[hdr_size - 4],
            hdr[hdr_size - 3],
            hdr[hdr_size - 2],
            hdr[hdr_size - 1],
        ]);
        if crc32_ieee(&hdr[..hdr_size - 4]) != want_crc {
            return Err(SpkError::Decompress("xz block header CRC mismatch".into()));
        }
        let bflags = hdr[1];
        if (bflags & 0x3C) != 0 || (bflags & 0x03) != 0 {
            return Err(SpkError::Decompress(
                "xz block header has reserved flags or unsupported filter chain".into(),
            ));
        }
        let mut hpos = 2usize;
        let declared_comp = if (bflags & 0x40) != 0 {
            Some(decode_xz_varint(&hdr[..hdr_size - 4], &mut hpos)?)
        } else {
            None
        };
        let declared_uncomp = if (bflags & 0x80) != 0 {
            let u = decode_xz_varint(&hdr[..hdr_size - 4], &mut hpos)?;
            if u > (limit.saturating_sub(out.len())) as u64 {
                return Err(SpkError::TooLarge);
            }
            Some(u)
        } else {
            None
        };
        let filter_id = decode_xz_varint(&hdr[..hdr_size - 4], &mut hpos)?;
        let props_size = decode_xz_varint(&hdr[..hdr_size - 4], &mut hpos)?;
        if filter_id != 0x21 || props_size != 1 || hpos >= hdr_size - 4 {
            return Err(SpkError::Decompress("expected single LZMA2 filter".into()));
        }
        let dict_prop = hdr[hpos];
        hpos += 1;
        if dict_prop > 40 || hdr[hpos..hdr_size - 4].iter().any(|&b| b != 0) {
            return Err(SpkError::Decompress(
                "invalid LZMA2 dictionary prop or header pad".into(),
            ));
        }
        let dict_limit = if dict_prop == 40 {
            0xFFFF_FFFFusize
        } else {
            ((2usize | ((dict_prop & 1) as usize)) << (dict_prop / 2 + 11)).max(4096)
        };

        pos += hdr_size;
        let comp_start = pos;
        let out_block_start = out.len();
        let mut lzma = Lzma2State::new();

        loop {
            let ctrl = *input
                .get(pos)
                .ok_or_else(|| SpkError::Decompress("LZMA2 stream truncated".into()))?;
            pos += 1;
            if ctrl == 0x00 {
                break;
            }
            if ctrl == 0x01 || ctrl == 0x02 {
                if ctrl == 0x02 && !lzma.dict_initialized {
                    return Err(SpkError::Decompress(
                        "LZMA2 chunk missing initial dict reset".into(),
                    ));
                }
                if ctrl == 0x01 {
                    lzma.dict_initialized = true;
                    lzma.props_initialized = false;
                    lzma.dict_reset_pos = out.len();
                }
                let hi = *input
                    .get(pos)
                    .ok_or_else(|| SpkError::Decompress("LZMA2 raw len truncated".into()))?;
                let lo = *input
                    .get(pos + 1)
                    .ok_or_else(|| SpkError::Decompress("LZMA2 raw len truncated".into()))?;
                pos += 2;
                let chunk_len = usize::from(u16::from_be_bytes([hi, lo])) + 1;
                // Check `limit` BEFORE reading/allocating!
                if out.len().saturating_add(chunk_len) > limit {
                    return Err(SpkError::TooLarge);
                }
                let raw = input
                    .get(pos..pos + chunk_len)
                    .ok_or_else(|| SpkError::Decompress("LZMA2 raw body truncated".into()))?;
                pos += chunk_len;
                out.extend_from_slice(raw);
            } else if ctrl >= 0x80 {
                let reset_mode = (ctrl >> 5) & 0x03;
                if reset_mode == 3 {
                    lzma.dict_initialized = true;
                    lzma.dict_reset_pos = out.len();
                } else if !lzma.dict_initialized {
                    return Err(SpkError::Decompress(
                        "LZMA2 compressed chunk missing dict reset".into(),
                    ));
                }
                let hdr4 = input.get(pos..pos + 4).ok_or_else(|| {
                    SpkError::Decompress("LZMA2 compressed header truncated".into())
                })?;
                pos += 4;
                let unpack_size = (((ctrl & 0x1F) as usize) << 16)
                    + usize::from(u16::from_be_bytes([hdr4[0], hdr4[1]]))
                    + 1;
                if out.len().saturating_add(unpack_size) > limit {
                    return Err(SpkError::TooLarge);
                }
                let pack_size = usize::from(u16::from_be_bytes([hdr4[2], hdr4[3]])) + 1;
                if reset_mode >= 2 {
                    let pbyte = *input
                        .get(pos)
                        .ok_or_else(|| SpkError::Decompress("LZMA2 props truncated".into()))?;
                    pos += 1;
                    if pbyte >= 225 {
                        return Err(SpkError::Decompress("invalid LZMA2 lc/lp/pb byte".into()));
                    }
                    let lc = u32::from(pbyte % 9);
                    let r = pbyte / 9;
                    let lp = u32::from(r % 5);
                    let pb = u32::from(r / 5);
                    if lc + lp > 4 {
                        return Err(SpkError::Decompress("LZMA2 lc + lp > 4".into()));
                    }
                    lzma.lc = lc;
                    lzma.lp = lp;
                    lzma.pb = pb;
                    lzma.props_initialized = true;
                    lzma.reset_probs();
                } else if !lzma.props_initialized {
                    return Err(SpkError::Decompress("LZMA2 props uninitialized".into()));
                } else if reset_mode == 1 {
                    lzma.reset_probs();
                }
                let pack_slice = input.get(pos..pos + pack_size).ok_or_else(|| {
                    SpkError::Decompress("LZMA2 compressed payload truncated".into())
                })?;
                pos += pack_size;
                lzma.decode_compressed_chunk(pack_slice, unpack_size, &mut out, dict_limit)?;
            } else {
                return Err(SpkError::Decompress(format!(
                    "invalid LZMA2 control byte {ctrl:#x}"
                )));
            }
        }

        let comp_size = (pos - comp_start) as u64;
        let block_out = &out[out_block_start..];
        let uncomp_size = block_out.len() as u64;
        if declared_comp.is_some_and(|dc| dc != comp_size) {
            return Err(SpkError::Decompress(
                "xz block compressed size mismatch".into(),
            ));
        }
        if declared_uncomp.is_some_and(|du| du != uncomp_size) {
            return Err(SpkError::Decompress(
                "xz block uncompressed size mismatch".into(),
            ));
        }

        while !(pos - block_start).is_multiple_of(4) {
            if input.get(pos) != Some(&0x00) {
                return Err(SpkError::Decompress("non-zero xz block padding".into()));
            }
            pos += 1;
        }
        let check_bytes = input
            .get(pos..pos + check_size)
            .ok_or_else(|| SpkError::Decompress("xz block check truncated".into()))?;
        pos += check_size;
        match stream_flags[1] {
            0x00 => {}
            0x01 => {
                if check_bytes != crc32_ieee(block_out).to_le_bytes() {
                    return Err(SpkError::Decompress("xz block CRC32 mismatch".into()));
                }
            }
            0x04 => {
                if check_bytes != crc64_ecma(block_out).to_le_bytes() {
                    return Err(SpkError::Decompress("xz block CRC64 mismatch".into()));
                }
            }
            0x0A => {
                let dig: [u8; 32] = sha256(block_out);
                if check_bytes != dig {
                    return Err(SpkError::Decompress("xz block SHA-256 mismatch".into()));
                }
            }
            _ => unreachable!(),
        }
        let unpadded = (hdr_size as u64) + comp_size + (check_size as u64);
        blocks.push((unpadded, uncomp_size));
    }

    // Index (`input[pos] == 0x00`)
    let index_start = pos;
    if input.get(pos) != Some(&0x00) {
        return Err(SpkError::Decompress("missing xz index indicator".into()));
    }
    pos += 1;
    let num_records = decode_xz_varint(input, &mut pos)? as usize;
    if num_records != blocks.len() {
        return Err(SpkError::Decompress(
            "xz index record count mismatch".into(),
        ));
    }
    for &(want_unpadded, want_uncomp) in &blocks {
        let got_unpadded = decode_xz_varint(input, &mut pos)?;
        let got_uncomp = decode_xz_varint(input, &mut pos)?;
        if got_unpadded != want_unpadded || got_uncomp != want_uncomp {
            return Err(SpkError::Decompress("xz index record mismatch".into()));
        }
    }
    while !(pos - index_start).is_multiple_of(4) {
        if input.get(pos) != Some(&0x00) {
            return Err(SpkError::Decompress("non-zero xz index padding".into()));
        }
        pos += 1;
    }
    let idx_crc_bytes = input
        .get(pos..pos + 4)
        .ok_or_else(|| SpkError::Decompress("xz index CRC truncated".into()))?;
    if crc32_ieee(&input[index_start..pos]).to_le_bytes() != idx_crc_bytes {
        return Err(SpkError::Decompress("xz index CRC mismatch".into()));
    }
    pos += 4;
    let index_total = pos - index_start;

    // Stream Footer (12 bytes)
    let footer = input
        .get(pos..pos + 12)
        .ok_or_else(|| SpkError::Decompress("xz footer truncated".into()))?;
    pos += 12;
    let ftr_crc = u32::from_le_bytes([footer[0], footer[1], footer[2], footer[3]]);
    if crc32_ieee(&footer[4..10]) != ftr_crc || footer[10..12] != XZ_FOOTER_MAGIC {
        return Err(SpkError::Decompress("corrupt xz stream footer".into()));
    }
    let backward_size =
        (u32::from_le_bytes([footer[4], footer[5], footer[6], footer[7]]) as usize + 1) * 4;
    if backward_size != index_total || footer[8..10] != stream_flags {
        return Err(SpkError::Decompress(
            "xz footer backward_size/flags mismatch".into(),
        ));
    }
    if pos != input.len() {
        return Err(SpkError::Decompress(
            "xz error: Unexpected data after last XZ block".into(),
        ));
    }
    Ok(out)
}

// =========================================================================
// `.spk` Archive & `verify_strict` Package Verifier
// =========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FileContent {
    Regular(Vec<u8>),
    Executable(Vec<u8>),
    Symlink(String),
    Directory(Vec<SpkFile>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpkFile {
    pub name: String,
    pub content: FileContent,
    pub mtime_ns: i64,
}

impl SpkFile {
    pub fn regular(name: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            name: name.into(),
            content: FileContent::Regular(bytes.into()),
            mtime_ns: 0,
        }
    }

    pub fn executable(name: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            name: name.into(),
            content: FileContent::Executable(bytes.into()),
            mtime_ns: 0,
        }
    }

    pub fn symlink(name: impl Into<String>, target: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            content: FileContent::Symlink(target.into()),
            mtime_ns: 0,
        }
    }

    pub fn directory(name: impl Into<String>, children: Vec<SpkFile>) -> Self {
        Self {
            name: name.into(),
            content: FileContent::Directory(children),
            mtime_ns: 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SpkArchive {
    pub files: Vec<SpkFile>,
}

struct ArchiveBudget {
    files: usize,
    name_bytes: usize,
    data_bytes: usize,
    max_data_bytes: usize,
}

impl ArchiveBudget {
    fn new(max_data_bytes: usize) -> Self {
        Self {
            files: 0,
            name_bytes: 0,
            data_bytes: 0,
            max_data_bytes,
        }
    }
}

fn to_wire_files(files: &[SpkFile]) -> Vec<WireFile<'_>> {
    files
        .iter()
        .map(|f| {
            let content = match &f.content {
                FileContent::Regular(b) => WireContent::Regular(b),
                FileContent::Executable(b) => WireContent::Executable(b),
                FileContent::Symlink(t) => WireContent::Symlink(t),
                FileContent::Directory(sub) => WireContent::Directory(to_wire_files(sub)),
            };
            WireFile {
                name: &f.name,
                content,
                mtime_ns: f.mtime_ns,
            }
        })
        .collect()
}

fn check_symlink_target(depth: usize, name: &str, target: &str) -> Result<(), SpkError> {
    let escape = || SpkError::SymlinkEscape {
        name: name.to_owned(),
        target: target.to_owned(),
    };
    if target.is_empty() || target.contains('\0') {
        return Err(escape());
    }
    let mut level = if target.starts_with('/') { 0 } else { depth };
    for comp in target.split('/') {
        match comp {
            "" | "." => {}
            ".." => level = level.checked_sub(1).ok_or_else(escape)?,
            _ => level += 1,
        }
    }
    Ok(())
}

fn decode_files(
    list: &capnp_wire::List<'_, '_>,
    depth: usize,
    budget: &mut ArchiveBudget,
) -> Result<Vec<SpkFile>, SpkError> {
    if depth > MAX_ARCHIVE_DEPTH {
        return Err(SpkError::Archive("archive directory depth exceeded".into()));
    }
    if list.len() > MAX_ARCHIVE_FILES.saturating_sub(budget.files) {
        return Err(SpkError::Archive("archive file count exceeded".into()));
    }
    let structs = list
        .structs()
        .map_err(|e| SpkError::Archive(e.to_string()))?;
    if structs.len() > MAX_ARCHIVE_FILES.saturating_sub(budget.files) {
        return Err(SpkError::Archive("archive file count exceeded".into()));
    }
    let mut out = Vec::with_capacity(structs.len());
    let mut names = BTreeSet::new();
    for s in structs {
        budget.files += 1;
        let name = s
            .get_text(0)
            .map_err(|e| SpkError::Archive(e.to_string()))?;
        if name.is_empty()
            || name == "."
            || name == ".."
            || name.contains('/')
            || name.contains('\0')
            || name.len() > MAX_FILE_NAME_BYTES
        {
            return Err(SpkError::Archive("invalid archive file name".into()));
        }
        if !names.insert(name.clone()) {
            return Err(SpkError::Archive("duplicate archive file name".into()));
        }
        budget.name_bytes = budget.name_bytes.saturating_add(name.len());
        if budget.name_bytes > MAX_ARCHIVE_NAME_BYTES {
            return Err(SpkError::Archive("archive name bytes exceeded".into()));
        }
        let mtime_ns = s.get_i64(8);
        let disc = s.get_u16(0);
        let content = match disc {
            0 | 1 => {
                let data = s
                    .get_data(1)
                    .map_err(|e| SpkError::Archive(e.to_string()))?;
                budget.data_bytes = budget.data_bytes.saturating_add(data.len());
                if budget.data_bytes > budget.max_data_bytes {
                    return Err(SpkError::Archive("archive file bytes exceeded".into()));
                }
                if disc == 0 {
                    FileContent::Regular(data)
                } else {
                    FileContent::Executable(data)
                }
            }
            2 => {
                let target = s
                    .get_text(1)
                    .map_err(|e| SpkError::Archive(e.to_string()))?;
                check_symlink_target(depth, &name, &target)?;
                FileContent::Symlink(target)
            }
            3 => {
                let sub = match s
                    .get_list(1)
                    .map_err(|e| SpkError::Archive(e.to_string()))?
                {
                    Some(l) => decode_files(&l, depth + 1, budget)?,
                    None => Vec::new(),
                };
                FileContent::Directory(sub)
            }
            other => return Err(SpkError::Archive(format!("bad file union tag {other}"))),
        };
        out.push(SpkFile {
            name,
            content,
            mtime_ns,
        });
    }
    Ok(out)
}

impl SpkArchive {
    pub fn find(&self, path: &str) -> Option<&[u8]> {
        if let Some(f) = self.files.iter().find(|f| f.name == path) {
            if let FileContent::Regular(b) | FileContent::Executable(b) = &f.content {
                return Some(b);
            }
        }
        let mut parts = path.split('/').filter(|p| !p.is_empty());
        let mut files = &self.files;
        let mut target = parts.next()?;
        loop {
            let f = files.iter().find(|f| f.name == target)?;
            match (&f.content, parts.next()) {
                (FileContent::Regular(b) | FileContent::Executable(b), None) => return Some(b),
                (FileContent::Directory(sub), Some(next)) => {
                    files = sub;
                    target = next;
                }
                _ => return None,
            }
        }
    }

    pub fn flatten(&self) -> BTreeMap<String, Vec<u8>> {
        fn walk(prefix: &str, files: &[SpkFile], out: &mut BTreeMap<String, Vec<u8>>) {
            for f in files {
                let path = if prefix.is_empty() {
                    f.name.clone()
                } else {
                    format!("{prefix}/{}", f.name)
                };
                match &f.content {
                    FileContent::Regular(b) | FileContent::Executable(b) => {
                        out.insert(path, b.clone());
                    }
                    FileContent::Directory(sub) => walk(&path, sub, out),
                    FileContent::Symlink(_) => {}
                }
            }
        }
        let mut out = BTreeMap::new();
        walk("", &self.files, &mut out);
        out
    }

    pub fn to_capnp_bytes(&self) -> Vec<u8> {
        capnp_wire::write_archive(&to_wire_files(&self.files))
    }

    pub fn from_capnp_bytes(buf: &[u8], max_data_bytes: usize) -> Result<Self, SpkError> {
        let (msg, consumed) =
            Message::parse_prefix(buf).map_err(|e| SpkError::Archive(e.to_string()))?;
        if consumed != buf.len() {
            return Err(SpkError::TrailingBytes {
                count: buf.len().saturating_sub(consumed),
            });
        }
        let root = msg.root().map_err(|e| SpkError::Archive(e.to_string()))?;
        let files = match root
            .get_list(0)
            .map_err(|e| SpkError::Archive(e.to_string()))?
        {
            Some(list) => decode_files(&list, 0, &mut ArchiveBudget::new(max_data_bytes))?,
            None => Vec::new(),
        };
        Ok(Self { files })
    }
}

/// Intrinsic Sandstorm App ID (unpadded Sandstorm-base32 of the signing Ed25519 public key).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AppId(pub String);

/// Errors returned during strict `.spk` verification and unpacking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpkError {
    BadMagic,
    Decompress(String),
    TooLarge,
    Truncated,
    BadSignature,
    Archive(String),
    TrailingBytes { count: usize },
    SymlinkEscape { name: String, target: String },
}

impl fmt::Display for SpkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpkError::BadMagic => write!(f, "not a .spk: bad magic prefix"),
            SpkError::Decompress(e) => write!(f, ".spk xz decompress failed: {e}"),
            SpkError::TooLarge => write!(f, ".spk exceeds selected decompressed size limit"),
            SpkError::Truncated => write!(f, ".spk payload truncated"),
            SpkError::BadSignature => {
                write!(
                    f,
                    ".spk signature failed strict SHA-512 + Ed25519 verification"
                )
            }
            SpkError::Archive(e) => write!(f, ".spk archive decode failed: {e}"),
            SpkError::TrailingBytes { count } => {
                write!(f, ".spk has {count} trailing byte(s) after archive message")
            }
            SpkError::SymlinkEscape { name, target } => {
                write!(f, ".spk symlink {name:?} -> {target:?} escapes image root")
            }
        }
    }
}

impl std::error::Error for SpkError {}

/// A strictly signature-verified Sandstorm `.spk` package.
#[derive(Clone, Debug)]
pub struct Spk {
    pub public_key: [u8; 32],
    pub archive_sha512: [u8; 64],
    pub archive: SpkArchive,
}

impl Spk {
    /// Strictly verify and decode a `.spk` image under [`MAX_DECOMPRESSED_BYTES`].
    pub fn verify_strict(bytes: &[u8]) -> Result<Self, SpkError> {
        Self::verify_strict_with_limit(bytes, MAX_DECOMPRESSED_BYTES)
    }

    /// Alias matching `sandstorm_package::Spk::parse` (always invokes `verify_strict`).
    pub fn parse(bytes: &[u8]) -> Result<Self, SpkError> {
        Self::verify_strict(bytes)
    }

    pub fn parse_with_limit(bytes: &[u8], limit: usize) -> Result<Self, SpkError> {
        Self::verify_strict_with_limit(bytes, limit)
    }

    /// Strictly verify a `.spk` container:
    /// 1. Checks `SPK_MAGIC`.
    /// 2. Decompresses XZ stream with per-chunk `limit` guard & trailing-byte refusal.
    /// 3. Decodes Cap'n Proto `Signature` message (`32B` pubkey, `128B` `sig || sha512`).
    /// 4. Verifies `SHA-512(archive_bytes)` in constant time AND RFC 8032 `ed25519_verify_strict`
    ///    (refusing small-order $A$/$R$ and non-canonical $s \ge \ell$).
    /// 5. Decodes `Archive` refusing trailing bytes, count bombs, and symlink escapes.
    pub fn verify_strict_with_limit(bytes: &[u8], limit: usize) -> Result<Self, SpkError> {
        let body = bytes
            .strip_prefix(&SPK_MAGIC[..])
            .ok_or(SpkError::BadMagic)?;
        let plain = xz_decompress_bounded(body, limit)?;

        let (sig_msg, consumed) = Message::parse_prefix(&plain).map_err(|_| SpkError::Truncated)?;
        let sig_root = sig_msg.root().map_err(|_| SpkError::Truncated)?;
        let pk_vec = sig_root.get_data(0).map_err(|_| SpkError::Truncated)?;
        let sig_field = sig_root.get_data(1).map_err(|_| SpkError::Truncated)?;
        if pk_vec.len() != 32 || sig_field.len() != 128 {
            return Err(SpkError::BadSignature);
        }
        let mut public_key = [0u8; 32];
        public_key.copy_from_slice(&pk_vec);
        let archive_bytes = plain.get(consumed..).ok_or(SpkError::Truncated)?;

        let mut sig_bytes = [0u8; 64];
        let mut embedded_hash = [0u8; 64];
        sig_bytes.copy_from_slice(&sig_field[..64]);
        embedded_hash.copy_from_slice(&sig_field[64..128]);

        let computed: [u8; 64] = sha512(archive_bytes);
        if !ct_eq(&embedded_hash, &computed) {
            return Err(SpkError::BadSignature);
        }

        ed25519_verify_strict(&public_key, &embedded_hash, &sig_bytes)?;

        let archive = SpkArchive::from_capnp_bytes(archive_bytes, limit)?;
        Ok(Self {
            public_key,
            archive_sha512: computed,
            archive,
        })
    }

    pub fn app_id(&self) -> AppId {
        AppId(sandstorm_base32_encode(&self.public_key))
    }

    pub fn manifest_bytes(&self) -> Option<&[u8]> {
        self.archive.find(MANIFEST_PATH)
    }

    pub fn bridge_config_bytes(&self) -> Option<&[u8]> {
        self.archive.find(BRIDGE_CONFIG_PATH)
    }
}

/// Builder for genuinely signed `.spk` packages in real Sandstorm wire format.
#[derive(Default)]
pub struct SpkBuilder {
    files: Vec<SpkFile>,
}

impl SpkBuilder {
    pub fn new() -> Self {
        Self { files: Vec::new() }
    }

    pub fn manifest_json(mut self, json: &str) -> Self {
        self.files
            .push(SpkFile::regular(MANIFEST_PATH, json.as_bytes().to_vec()));
        self
    }

    pub fn manifest_capnp(mut self, bytes: Vec<u8>) -> Self {
        self.files.push(SpkFile::regular(MANIFEST_PATH, bytes));
        self
    }

    pub fn bridge_config_capnp(mut self, bytes: Vec<u8>) -> Self {
        self.files.push(SpkFile::regular(BRIDGE_CONFIG_PATH, bytes));
        self
    }

    pub fn file(mut self, f: SpkFile) -> Self {
        self.files.push(f);
        self
    }

    pub fn pack(self, signing_key: &Ed25519SigningKey) -> Vec<u8> {
        let archive = SpkArchive { files: self.files };
        let archive_msg = archive.to_capnp_bytes();
        let hash: [u8; 64] = sha512(&archive_msg);
        let sig = signing_key.sign(&hash);

        let mut sig_field = Vec::with_capacity(128);
        sig_field.extend_from_slice(&sig);
        sig_field.extend_from_slice(&hash);

        let sig_msg = capnp_wire::write_signature(&signing_key.verifying_key_bytes(), &sig_field);
        let mut plain = sig_msg;
        plain.extend_from_slice(&archive_msg);

        let compressed = xz_compress(&plain);
        let mut out = Vec::with_capacity(SPK_MAGIC.len() + compressed.len());
        out.extend_from_slice(&SPK_MAGIC);
        out.extend_from_slice(&compressed);
        out
    }
}

// =========================================================================
// Fixed Role/Permission Manifest Extractor (Closing `manifest.rs:287`)
// =========================================================================

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpkCommand {
    #[serde(default)]
    pub argv: Vec<String>,
    #[serde(default)]
    pub environ: Vec<(String, String)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpkAction {
    #[serde(default)]
    pub noun_phrase: String,
    pub command: SpkCommand,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PermissionDef {
    pub name: String,
    #[serde(default)]
    pub title: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub obsolete: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Role {
    pub title: String,
    #[serde(default)]
    pub verb_phrase: String,
    /// Named permissions granted by this role (strictly validated as a subset of declared permissions!).
    #[serde(default)]
    pub permissions: Vec<String>,
    /// Exact ordered bitmask over `BridgeConfig::permissions`.
    #[serde(default)]
    pub permission_bits: Vec<bool>,
    #[serde(default)]
    pub obsolete: bool,
    #[serde(default)]
    pub default: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BridgeConfig {
    #[serde(default)]
    pub api_port: Option<u16>,
    #[serde(default)]
    pub api_path: Option<String>,
    #[serde(default)]
    pub permissions: Vec<String>,
    #[serde(default)]
    pub permission_defs: Vec<PermissionDef>,
    #[serde(default)]
    pub roles: Vec<Role>,
    #[serde(default)]
    pub denied_permissions: Vec<bool>,
    #[serde(default)]
    pub save_identity_caps: bool,
    #[serde(default)]
    pub expect_app_hooks: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct SpkMetadata {
    #[serde(default)]
    pub author: String,
    #[serde(default)]
    pub website: String,
    #[serde(default)]
    pub categories: Vec<String>,
    #[serde(default)]
    pub short_description: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpkManifest {
    pub app_id: AppId,
    pub app_title: String,
    pub app_version: u32,
    #[serde(default)]
    pub marketing_version: String,
    #[serde(default)]
    pub actions: Vec<SpkAction>,
    pub continue_command: SpkCommand,
    #[serde(default)]
    pub bridge_config: Option<BridgeConfig>,
    #[serde(default)]
    pub metadata: SpkMetadata,
}

/// Errors raised when decoding or validating an `SpkManifest` / `BridgeConfig`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ManifestError {
    MissingManifest,
    Malformed(String),
    InvalidPermissionName(String),
    DuplicatePermissionName(String),
    /// Role attempts to grant an undeclared permission name or out-of-range bit index (`manifest.rs:287` escalation guard!).
    RolePermissionEscalation {
        role: String,
        detail: String,
    },
    AmbiguousDefaultRole,
    InvalidApiPath(String),
    UnknownRole(String),
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingManifest => write!(f, "no sandstorm-manifest in package archive"),
            Self::Malformed(m) => write!(f, "manifest parse error: {m}"),
            Self::InvalidPermissionName(n) => {
                write!(f, "invalid permission identifier {n:?} (header-safe [A-Za-z][A-Za-z0-9_.-]* required)")
            }
            Self::DuplicatePermissionName(n) => {
                write!(f, "duplicate declared permission name {n:?}")
            }
            Self::RolePermissionEscalation { role, detail } => {
                write!(f, "role {role:?} permission escalation refused: {detail}")
            }
            Self::AmbiguousDefaultRole => {
                write!(f, "multiple default roles in ViewInfo are ambiguous")
            }
            Self::InvalidApiPath(p) => write!(f, "invalid bridge apiPath {p:?}"),
            Self::UnknownRole(r) => write!(f, "unknown or obsolete sharing role {r:?}"),
        }
    }
}

impl std::error::Error for ManifestError {}

fn validate_permission_identifier(name: &str) -> Result<(), ManifestError> {
    if name.is_empty()
        || name.len() > 256
        || !name.starts_with(|c: char| c.is_ascii_alphabetic())
        || !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
    {
        return Err(ManifestError::InvalidPermissionName(name.to_string()));
    }
    Ok(())
}

fn validate_canonical_api_path(path: &str) -> Result<Option<String>, ManifestError> {
    if path.is_empty() {
        return Ok(None);
    }
    if path.len() > MAX_API_PATH_BYTES
        || path.contains('\0')
        || !path.starts_with('/')
        || !path.ends_with('/')
        || path.contains("//")
    {
        return Err(ManifestError::InvalidApiPath(path.to_string()));
    }
    for seg in path.split('/').filter(|s| !s.is_empty()) {
        if seg == "."
            || seg == ".."
            || !seg
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
        {
            return Err(ManifestError::InvalidApiPath(path.to_string()));
        }
    }
    Ok(Some(path.to_string()))
}

/// Validate and normalize a [`BridgeConfig`] (for both JSON and Cap'n Proto decode paths),
/// rejecting duplicate/header-unsafe permission names, out-of-bounds or undeclared role grants,
/// and multiple default roles.
fn normalize_and_validate_bridge_config(
    mut cfg: BridgeConfig,
) -> Result<BridgeConfig, ManifestError> {
    if cfg.permissions.len() > 4096 || cfg.roles.len() > 4096 {
        return Err(ManifestError::Malformed(
            "ViewInfo exceeds 4096 entry bound".into(),
        ));
    }
    let mut seen = BTreeSet::new();
    for p in &cfg.permissions {
        validate_permission_identifier(p)?;
        if !seen.insert(p.clone()) {
            return Err(ManifestError::DuplicatePermissionName(p.clone()));
        }
    }
    if cfg.permission_defs.is_empty() && !cfg.permissions.is_empty() {
        cfg.permission_defs = cfg
            .permissions
            .iter()
            .map(|name| PermissionDef {
                name: name.clone(),
                title: name.clone(),
                description: String::new(),
                obsolete: false,
            })
            .collect();
    }
    if let Some(raw_api) = cfg.api_path.take() {
        cfg.api_path = validate_canonical_api_path(&raw_api)?;
    }
    if cfg.denied_permissions.len() > cfg.permissions.len() {
        return Err(ManifestError::Malformed(
            "deniedPermissions bitset exceeds declared permissions length".into(),
        ));
    }

    let mut default_count = 0usize;
    for role in &mut cfg.roles {
        if role.default {
            default_count += 1;
        }
        if !role.permission_bits.is_empty() {
            if role.permission_bits.len() > cfg.permissions.len() {
                return Err(ManifestError::RolePermissionEscalation {
                    role: role.title.clone(),
                    detail: format!(
                        "permission bitset length {} exceeds declared permissions count {}",
                        role.permission_bits.len(),
                        cfg.permissions.len()
                    ),
                });
            }
            let mut derived_names = Vec::new();
            for (idx, &granted) in role.permission_bits.iter().enumerate() {
                if granted {
                    derived_names.push(cfg.permissions[idx].clone());
                }
            }
            if !role.permissions.is_empty() && role.permissions != derived_names {
                return Err(ManifestError::RolePermissionEscalation {
                    role: role.title.clone(),
                    detail: "role named permissions disagree with permission_bits".into(),
                });
            }
            role.permissions = derived_names;
        } else {
            let mut bits = vec![false; cfg.permissions.len()];
            let mut role_seen = BTreeSet::new();
            for pname in &role.permissions {
                if !role_seen.insert(pname.as_str()) {
                    return Err(ManifestError::RolePermissionEscalation {
                        role: role.title.clone(),
                        detail: format!("duplicate permission {pname:?} in role"),
                    });
                }
                let Some(idx) = cfg.permissions.iter().position(|d| d == pname) else {
                    return Err(ManifestError::RolePermissionEscalation {
                        role: role.title.clone(),
                        detail: format!(
                            "grants undeclared permission {pname:?} outside {:?}",
                            cfg.permissions
                        ),
                    });
                };
                bits[idx] = true;
            }
            role.permission_bits = bits;
        }
    }
    if default_count > 1 {
        return Err(ManifestError::AmbiguousDefaultRole);
    }
    Ok(cfg)
}

/// Decode a signed Cap'n Proto `sandstorm-http-bridge-config` (`package.capnp:BridgeConfig`) member,
/// recovering its ordered `ViewInfo` (`permissions`, `roles`, `deniedPermissions`), `apiPath`,
/// `saveIdentityCaps`, and `expectAppHooks`!
pub fn decode_bridge_config_capnp(
    member: &[u8],
    api_port: Option<u16>,
) -> Result<BridgeConfig, ManifestError> {
    if member.is_empty() || member.len() > MAX_BRIDGE_CONFIG_BYTES {
        return Err(ManifestError::Malformed(
            "bridge-config member empty or exceeds 64 KiB".into(),
        ));
    }
    let (msg, consumed) =
        Message::parse_prefix(member).map_err(|e| ManifestError::Malformed(e.to_string()))?;
    if consumed != member.len() {
        return Err(ManifestError::Malformed(
            "bridge-config member has trailing bytes".into(),
        ));
    }
    let root = msg
        .root()
        .map_err(|e| ManifestError::Malformed(e.to_string()))?;
    let save_identity_caps = root.get_bool(0);
    let expect_app_hooks = root.get_bool(1);
    let raw_api_path = root
        .get_text(1)
        .map_err(|e| ManifestError::Malformed(e.to_string()))?;
    let api_path = validate_canonical_api_path(&raw_api_path)?;

    if root
        .get_list(2)
        .map_err(|e| ManifestError::Malformed(e.to_string()))?
        .is_some_and(|pb_list| !pb_list.is_empty())
    {
        return Err(ManifestError::Malformed(
            "powerboxApis require an explicit interface descriptor gate".into(),
        ));
    }

    let mut permission_defs = Vec::new();
    let mut permissions = Vec::new();
    let mut roles = Vec::new();
    let mut denied_permissions = Vec::new();

    if let Some(vi) = root
        .get_struct(0)
        .map_err(|e| ManifestError::Malformed(e.to_string()))?
    {
        if let Some(perm_list) = vi
            .get_list(0)
            .map_err(|e| ManifestError::Malformed(e.to_string()))?
        {
            for p_struct in perm_list
                .structs()
                .map_err(|e| ManifestError::Malformed(e.to_string()))?
            {
                let name = p_struct
                    .get_text(2)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                let title = read_localized(&p_struct, 0)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                let description = read_localized(&p_struct, 1)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                let obsolete = p_struct.get_bool(0);
                permissions.push(name.clone());
                permission_defs.push(PermissionDef {
                    name,
                    title,
                    description,
                    obsolete,
                });
            }
        }
        if let Some(role_list) = vi
            .get_list(1)
            .map_err(|e| ManifestError::Malformed(e.to_string()))?
        {
            for r_struct in role_list
                .structs()
                .map_err(|e| ManifestError::Malformed(e.to_string()))?
            {
                let title = read_localized(&r_struct, 0)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                let verb_phrase = read_localized(&r_struct, 1)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                let mut bits = r_struct
                    .get_bool_list(3)
                    .map_err(|e| ManifestError::Malformed(e.to_string()))?;
                if bits.len() > permissions.len() {
                    return Err(ManifestError::RolePermissionEscalation {
                        role: title,
                        detail: format!(
                            "role bitset len {} exceeds declared permissions count {}",
                            bits.len(),
                            permissions.len()
                        ),
                    });
                }
                bits.resize(permissions.len(), false);
                let obsolete = r_struct.get_bool(0);
                let default = r_struct.get_bool(1);
                roles.push(Role {
                    title,
                    verb_phrase,
                    permissions: Vec::new(),
                    permission_bits: bits,
                    obsolete,
                    default,
                });
            }
        }
        denied_permissions = vi
            .get_bool_list(2)
            .map_err(|e| ManifestError::Malformed(e.to_string()))?;
    }

    normalize_and_validate_bridge_config(BridgeConfig {
        api_port,
        api_path,
        permissions,
        permission_defs,
        roles,
        denied_permissions,
        save_identity_caps,
        expect_app_hooks,
    })
}

fn looks_like_json(bytes: &[u8]) -> bool {
    bytes
        .iter()
        .find(|b| !b.is_ascii_whitespace())
        .is_some_and(|b| *b == b'{')
}

fn read_localized(s: &Struct<'_, '_>, slot: usize) -> Result<String, capnp_wire::CapnpError> {
    match s.get_struct(slot)? {
        Some(lt) => lt.get_text(0),
        None => Ok(String::new()),
    }
}

fn read_command(cmd: Option<Struct<'_, '_>>) -> Result<SpkCommand, capnp_wire::CapnpError> {
    let Some(cmd) = cmd else {
        return Ok(SpkCommand {
            argv: Vec::new(),
            environ: Vec::new(),
        });
    };
    let mut argv = match cmd.get_list(1)? {
        Some(list) => list.text_list()?,
        None => Vec::new(),
    };
    let deprecated = cmd.get_text(0)?;
    if !deprecated.is_empty() {
        argv.insert(0, deprecated);
    }
    let environ = match cmd.get_list(2)? {
        Some(list) => list
            .structs()?
            .into_iter()
            .map(|e| Ok((e.get_text(0)?, e.get_text(1)?)))
            .collect::<Result<Vec<_>, capnp_wire::CapnpError>>()?,
        None => Vec::new(),
    };
    Ok(SpkCommand { argv, environ })
}

fn read_actions(root: &Struct<'_, '_>) -> Result<Vec<SpkAction>, capnp_wire::CapnpError> {
    let Some(list) = root.get_list(0)? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for a in list.structs()? {
        let command = read_command(a.get_struct(1)?)?;
        let noun_phrase = read_localized(&a, 4)?;
        out.push(SpkAction {
            noun_phrase,
            command,
        });
    }
    Ok(out)
}

fn bridge_port_from_argv(argv: &[String]) -> Option<Option<u16>> {
    let idx = argv
        .iter()
        .position(|a| a == "/sandstorm-http-bridge" || a.ends_with("/sandstorm-http-bridge"))?;
    let port = argv.get(idx + 1).and_then(|p| p.parse::<u16>().ok());
    Some(port)
}

impl SpkManifest {
    pub fn from_json(s: &str) -> Result<Self, ManifestError> {
        let mut m: Self =
            serde_json::from_str(s).map_err(|e| ManifestError::Malformed(e.to_string()))?;
        if let Some(bc) = m.bridge_config.take() {
            m.bridge_config = Some(normalize_and_validate_bridge_config(bc)?);
        }
        Ok(m)
    }

    pub fn from_capnp(bytes: &[u8]) -> Result<Self, ManifestError> {
        Self::from_capnp_with_bridge_config(bytes, None)
    }

    /// Decode a Cap'n Proto `Manifest` AND join it with an optional signed
    /// `sandstorm-http-bridge-config` archive member (closing `manifest.rs:287`!).
    pub fn from_capnp_with_bridge_config(
        bytes: &[u8],
        bridge_config_member: Option<&[u8]>,
    ) -> Result<Self, ManifestError> {
        let (msg, consumed) =
            Message::parse_prefix(bytes).map_err(|e| ManifestError::Malformed(e.to_string()))?;
        if consumed != bytes.len() {
            return Err(ManifestError::Malformed(
                "sandstorm-manifest has trailing bytes".into(),
            ));
        }
        let root = msg
            .root()
            .map_err(|e| ManifestError::Malformed(e.to_string()))?;
        let app_version = root.get_u32(8);
        let app_title =
            read_localized(&root, 3).map_err(|e| ManifestError::Malformed(e.to_string()))?;
        let marketing_version =
            read_localized(&root, 2).map_err(|e| ManifestError::Malformed(e.to_string()))?;
        let continue_command = read_command(
            root.get_struct(1)
                .map_err(|e| ManifestError::Malformed(e.to_string()))?,
        )
        .map_err(|e| ManifestError::Malformed(e.to_string()))?;
        let actions = read_actions(&root).map_err(|e| ManifestError::Malformed(e.to_string()))?;

        let argv_bridge = bridge_port_from_argv(&continue_command.argv);
        let bridge_config = match (argv_bridge, bridge_config_member) {
            (Some(port), Some(member)) => Some(decode_bridge_config_capnp(member, port)?),
            (None, Some(member)) => Some(decode_bridge_config_capnp(member, None)?),
            (Some(port), None) => Some(BridgeConfig {
                api_port: port,
                ..BridgeConfig::default()
            }),
            (None, None) => None,
        };

        Ok(Self {
            app_id: AppId(String::new()),
            app_title,
            app_version,
            marketing_version,
            actions,
            continue_command,
            bridge_config,
            metadata: SpkMetadata::default(),
        })
    }

    /// Decode and validate the manifest from a strictly verified [`Spk`], extracting
    /// `sandstorm-http-bridge-config` roles/permissions when present and pinning `app_id`
    /// exclusively to the verified Ed25519 signing key!
    pub fn from_spk(spk: &Spk) -> Result<Self, ManifestError> {
        let bytes = spk.manifest_bytes().ok_or(ManifestError::MissingManifest)?;
        let bridge_member = spk.bridge_config_bytes();
        let mut m = if looks_like_json(bytes) {
            let text = std::str::from_utf8(bytes)
                .map_err(|_| ManifestError::Malformed("manifest is not UTF-8".into()))?;
            let mut parsed = Self::from_json(text)?;
            if let Some(member) = bridge_member {
                let port = parsed.bridge_config.as_ref().and_then(|b| b.api_port);
                parsed.bridge_config = Some(decode_bridge_config_capnp(member, port)?);
            }
            parsed
        } else {
            Self::from_capnp_with_bridge_config(bytes, bridge_member)?
        };
        m.app_id = spk.app_id();
        Ok(m)
    }

    pub fn is_http_bridge(&self) -> bool {
        self.bridge_config.is_some()
    }

    pub fn declared_permissions(&self) -> Vec<String> {
        self.bridge_config
            .as_ref()
            .map(|b| b.permissions.clone())
            .unwrap_or_default()
    }

    /// Resolve effective non-obsolete, non-denied permissions for `role_title` (attenuation gate:
    /// refuses unknown or obsolete roles rather than escalating!).
    pub fn resolve_role_permissions(&self, role_title: &str) -> Result<Vec<String>, ManifestError> {
        let bc = self
            .bridge_config
            .as_ref()
            .ok_or_else(|| ManifestError::UnknownRole(role_title.to_string()))?;
        let role = bc
            .roles
            .iter()
            .find(|r| r.title == role_title && !r.obsolete)
            .ok_or_else(|| ManifestError::UnknownRole(role_title.to_string()))?;
        let mut out = Vec::new();
        for (idx, &granted) in role.permission_bits.iter().enumerate() {
            let denied = bc.denied_permissions.get(idx).copied().unwrap_or(false);
            let obs = bc
                .permission_defs
                .get(idx)
                .map(|p| p.obsolete)
                .unwrap_or(false);
            if granted && !denied && !obs {
                out.push(bc.permissions[idx].clone());
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capnp_wire::{
        write_bridge_config, write_manifest_capnp, WireBridgeConfig, WirePermissionDef, WireRoleDef,
    };

    fn hex_decode(h: &str) -> Vec<u8> {
        let mut out = Vec::with_capacity(h.len() / 2);
        let bytes = h.as_bytes();
        let mut i = 0;
        while i + 1 < bytes.len() {
            let s = std::str::from_utf8(&bytes[i..i + 2]).unwrap();
            out.push(u8::from_str_radix(s, 16).unwrap());
            i += 2;
        }
        out
    }

    #[test]
    fn rfc8032_section_7_1_official_test_vectors_and_small_order_rejection() {
        // RFC 8032 §7.1 TEST 1 (empty message) & TEST 2 (1-byte 0x72)
        let sk1 = hex_decode("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
        let pk1 = hex_decode("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        let sig1 = hex_decode("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
        let key1 = Ed25519SigningKey::from_bytes(sk1.as_slice().try_into().unwrap());
        assert_eq!(&key1.verifying_key_bytes()[..], &pk1[..]);
        assert_eq!(&key1.sign(b"")[..], &sig1[..]);
        assert!(ed25519_verify_strict(
            pk1.as_slice().try_into().unwrap(),
            b"",
            sig1.as_slice().try_into().unwrap()
        )
        .is_ok());

        let sk2 = hex_decode("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb");
        let pk2 = hex_decode("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let sig2 = hex_decode("92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00");
        let key2 = Ed25519SigningKey::from_bytes(sk2.as_slice().try_into().unwrap());
        assert_eq!(&key2.verifying_key_bytes()[..], &pk2[..]);
        assert_eq!(&key2.sign(&[0x72])[..], &sig2[..]);
        assert!(ed25519_verify_strict(
            pk2.as_slice().try_into().unwrap(),
            &[0x72],
            sig2.as_slice().try_into().unwrap()
        )
        .is_ok());

        // Small-order identity key `[1, 0, ..., 0]` universal forgery MUST fail `verify_strict`!
        let mut identity = [0u8; 32];
        identity[0] = 1;
        let mut forged_sig = [0u8; 64];
        forged_sig[0] = 1;
        assert_eq!(
            ed25519_verify_strict(&identity, b"any archive hash", &forged_sig),
            Err(SpkError::BadSignature)
        );
    }

    #[test]
    fn closes_manifest_rs_287_bridge_config_extraction_and_blocks_role_escalation() {
        let key = Ed25519SigningKey::from_bytes(&[7u8; 32]);
        let manifest_bytes = write_manifest_capnp(
            "GitWeb",
            12,
            "2.40.0",
            &["/sandstorm-http-bridge", "8000", "--", "/start.sh"],
        );
        let bc_bytes = write_bridge_config(&WireBridgeConfig {
            app_title: "GitWeb",
            permissions: &[
                WirePermissionDef {
                    name: "read",
                    title: "Read",
                    obsolete: false,
                },
                WirePermissionDef {
                    name: "write",
                    title: "Write",
                    obsolete: false,
                },
            ],
            roles: &[
                WireRoleDef {
                    title: "guest",
                    verb_phrase: "can read",
                    permissions: &[true, false],
                    obsolete: false,
                    default: false,
                },
                WireRoleDef {
                    title: "developer",
                    verb_phrase: "can read and write",
                    permissions: &[true, true],
                    obsolete: false,
                    default: true,
                },
            ],
            denied_permissions: &[],
            api_path: Some("/repo.git/"),
            save_identity_caps: false,
            expect_app_hooks: false,
        });

        let spk_bytes = SpkBuilder::new()
            .manifest_capnp(manifest_bytes.clone())
            .bridge_config_capnp(bc_bytes)
            .file(SpkFile::executable("start.sh", b"#!/bin/sh\n".to_vec()))
            .pack(&key);

        let spk = Spk::verify_strict(&spk_bytes).unwrap();
        let manifest = SpkManifest::from_spk(&spk).unwrap();
        let bc = manifest.bridge_config.as_ref().unwrap();
        assert_eq!(bc.api_port, Some(8000));
        assert_eq!(bc.api_path.as_deref(), Some("/repo.git/"));
        assert_eq!(bc.permissions, vec!["read", "write"]);
        assert_eq!(bc.roles.len(), 2);
        assert_eq!(
            manifest.resolve_role_permissions("guest").unwrap(),
            vec!["read"]
        );
        assert_eq!(
            manifest.resolve_role_permissions("developer").unwrap(),
            vec!["read", "write"]
        );

        // Escalation 1: Cap'n Proto role claims 3 permission bits when only 2 permissions exist -> REFUSED!
        let bad_bc = write_bridge_config(&WireBridgeConfig {
            app_title: "GitWeb",
            permissions: &[WirePermissionDef {
                name: "read",
                title: "Read",
                obsolete: false,
            }],
            roles: &[WireRoleDef {
                title: "escalator",
                verb_phrase: "escalates",
                permissions: &[true, true],
                obsolete: false,
                default: false,
            }],
            denied_permissions: &[],
            api_path: None,
            save_identity_caps: false,
            expect_app_hooks: false,
        });
        assert!(matches!(
            SpkManifest::from_capnp_with_bridge_config(&manifest_bytes, Some(&bad_bc)),
            Err(ManifestError::RolePermissionEscalation { .. })
        ));

        // Escalation 2: JSON manifest role references undeclared `"admin"` permission -> REFUSED!
        let bad_json = r#"{
          "app_id": "ignored",
          "app_title": "App",
          "app_version": 1,
          "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/run"] },
          "bridge_config": {
            "api_port": 8000,
            "permissions": ["view"],
            "roles": [{ "title": "viewer", "permissions": ["view", "admin"] }]
          }
        }"#;
        assert!(matches!(
            SpkManifest::from_json(bad_json),
            Err(ManifestError::RolePermissionEscalation { .. })
        ));
    }
}
