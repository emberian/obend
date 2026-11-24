//! Fixed-width little-endian `u64`-limb Montgomery arithmetic (CIOS, Koç–Acar–Kaliski 1996),
//! runtime-parameterised by an odd modulus `p < 2^(64N)`.
//!
//! One generic engine carries every prime/composite modulus in the workspace: P-256 / P-384 base
//! and scalar fields (`N = 4 / 6`), Curve25519 `p` and `ℓ` (`N = 4`), BLS12-381 `Fp` / `Fr`
//! (`N = 6 / 4`), and RSA moduli up to 4096 bits (`N = 64`, upper limbs may be zero).
//!
//! Values passed to [`Mont::mul`], [`Mont::add`], [`Mont::sub`] must be fully reduced (`< p`);
//! every operation returns a fully reduced value. Verification paths handle public data only, so
//! the engine is variable-time (documented; not used with long-term secrets outside fixtures).
//!
//! Context construction and the field operations are `const fn`, so a modulus and the constants
//! derived from it can be evaluated at compile time (as [`crate::ed25519`] does). Encoders write
//! into caller buffers; the `alloc` feature adds `Vec`-returning forms.

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// Little-endian 64-bit limbs.
pub type Limbs<const N: usize> = [u64; N];

#[inline(always)]
const fn mac(acc: u64, a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = acc as u128 + a as u128 * b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128)
        .wrapping_sub(b as u128)
        .wrapping_sub(borrow as u128);
    (t as u64, ((t >> 64) as u64) & 1)
}

/// `a >= b` on equal-width limb arrays.
pub const fn limbs_ge<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> bool {
    let mut i = N;
    while i > 0 {
        i -= 1;
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

/// `a == b`, usable in constant evaluation.
pub(crate) const fn limbs_eq<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> bool {
    let mut i = 0;
    while i < N {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// `a - b` (wrapping), returning `(difference, borrow)`.
pub const fn limbs_sub<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> (Limbs<N>, u64) {
    let mut out = [0u64; N];
    let mut borrow = 0u64;
    let mut i = 0;
    while i < N {
        let (d, br) = sbb(a[i], b[i], borrow);
        out[i] = d;
        borrow = br;
        i += 1;
    }
    (out, borrow)
}

/// `a + b` (wrapping), returning `(sum, carry)`.
pub const fn limbs_add<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> (Limbs<N>, u64) {
    let mut out = [0u64; N];
    let mut carry = 0u64;
    let mut i = 0;
    while i < N {
        let (s, c) = adc(a[i], b[i], carry);
        out[i] = s;
        carry = c;
        i += 1;
    }
    (out, carry)
}

pub const fn limbs_is_zero<const N: usize>(a: &Limbs<N>) -> bool {
    let mut i = 0;
    while i < N {
        if a[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

pub const fn limbs_from_u64<const N: usize>(v: u64) -> Limbs<N> {
    let mut out = [0u64; N];
    out[0] = v;
    out
}

/// Number of significant bits.
pub const fn limbs_bits<const N: usize>(a: &Limbs<N>) -> usize {
    let mut i = N;
    while i > 0 {
        i -= 1;
        if a[i] != 0 {
            return 64 * i + (64 - a[i].leading_zeros() as usize);
        }
    }
    0
}

pub const fn limbs_bit<const N: usize>(a: &Limbs<N>, i: usize) -> bool {
    i < 64 * N && (a[i / 64] >> (i % 64)) & 1 == 1
}

/// Big-endian bytes (any length `<= 8N` after stripping leading zeros) to limbs.
pub fn limbs_from_be<const N: usize>(bytes: &[u8]) -> Option<Limbs<N>> {
    let first_nz = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    let bytes = &bytes[first_nz..];
    if bytes.len() > 8 * N {
        return None;
    }
    let mut out = [0u64; N];
    for (i, &b) in bytes.iter().rev().enumerate() {
        out[i / 8] |= u64::from(b) << (8 * (i % 8));
    }
    Some(out)
}

/// Writes `a` as exactly `out.len()` big-endian bytes. `None`, with `out` untouched, if the value
/// does not fit.
pub fn limbs_to_be_into<const N: usize>(a: &Limbs<N>, out: &mut [u8]) -> Option<()> {
    let len = out.len();
    if limbs_bits(a).div_ceil(8) > len {
        return None;
    }
    out.fill(0);
    for i in 0..len.min(8 * N) {
        out[len - 1 - i] = (a[i / 8] >> (8 * (i % 8))) as u8;
    }
    Some(())
}

/// Limbs to exactly `len` big-endian bytes (`None` if the value does not fit).
#[cfg(feature = "alloc")]
pub fn limbs_to_be<const N: usize>(a: &Limbs<N>, len: usize) -> Option<Vec<u8>> {
    let mut out = vec![0u8; len];
    limbs_to_be_into(a, &mut out)?;
    Some(out)
}

/// Parse a big-endian hex constant, skipping ASCII whitespace and `_` (panics on malformed input;
/// constants only, so in a constant the panic is a compile error).
pub const fn limbs_from_hex<const N: usize>(hex: &str) -> Limbs<N> {
    let bytes = hex.as_bytes();
    let mut out = [0u64; N];
    let mut digits = 0;
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        let c = bytes[i];
        let d = match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ if c.is_ascii_whitespace() || c == b'_' => continue,
            _ => panic!("limbs_from_hex: non-hex digit"),
        };
        assert!(digits < 16 * N, "limbs_from_hex: constant too wide");
        out[digits / 16] |= (d as u64) << (4 * (digits % 16));
        digits += 1;
    }
    out
}

/// `2x mod p` for `x < p`.
const fn double_mod<const N: usize>(x: &Limbs<N>, p: &Limbs<N>) -> Limbs<N> {
    let (s, carry) = limbs_add(x, x);
    if carry != 0 || limbs_ge(&s, p) {
        limbs_sub(&s, p).0
    } else {
        s
    }
}

/// Montgomery context for an odd modulus `p` with `R = 2^(64N)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mont<const N: usize> {
    p: Limbs<N>,
    /// `-p^{-1} mod 2^64`.
    pinv: u64,
    /// `R^2 mod p`.
    r2: Limbs<N>,
    /// `R mod p` (Montgomery form of 1).
    one: Limbs<N>,
    /// `p - 2` (Fermat inversion exponent; meaningful for prime `p`).
    p_minus_2: Limbs<N>,
}

impl<const N: usize> Mont<N> {
    /// Build a context; returns `None` for zero-width, even, or `< 3` moduli.
    pub const fn new(p: Limbs<N>) -> Option<Self> {
        if N == 0 || p[0] & 1 == 0 || limbs_bits(&p) < 2 {
            return None;
        }
        // Newton's iteration doubles the correct low bits of `p^{-1} mod 2^64`: 1 -> 64 in six.
        let mut inv = 1u64;
        let mut step = 0;
        while step < 6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p[0].wrapping_mul(inv)));
            step += 1;
        }
        let pinv = inv.wrapping_neg();
        // x = 1; double 64N times -> R mod p; double 64N more -> R^2 mod p.
        let mut x = limbs_from_u64::<N>(1);
        let mut k = 0;
        while k < 64 * N {
            x = double_mod(&x, &p);
            k += 1;
        }
        let one = x;
        while k < 128 * N {
            x = double_mod(&x, &p);
            k += 1;
        }
        let r2 = x;
        let p_minus_2 = limbs_sub(&p, &limbs_from_u64::<N>(2)).0;
        Some(Self {
            p,
            pinv,
            r2,
            one,
            p_minus_2,
        })
    }

    pub const fn from_hex(hex: &str) -> Self {
        match Self::new(limbs_from_hex(hex)) {
            Some(m) => m,
            None => panic!("Mont::from_hex: odd modulus"),
        }
    }

    pub const fn modulus(&self) -> &Limbs<N> {
        &self.p
    }

    pub const fn modulus_bits(&self) -> usize {
        limbs_bits(&self.p)
    }

    /// Montgomery form of 1.
    pub const fn one(&self) -> Limbs<N> {
        self.one
    }

    pub const fn zero(&self) -> Limbs<N> {
        [0u64; N]
    }

    /// Montgomery product `a * b * R^{-1} mod p` (CIOS).
    pub const fn mul(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let mut t = [0u64; N];
        let mut t_n = 0u64;
        let mut i = 0;
        while i < N {
            let b_limb = b[i];
            let mut c = 0u64;
            let mut j = 0;
            while j < N {
                let (lo, hi) = mac(t[j], a[j], b_limb, c);
                t[j] = lo;
                c = hi;
                j += 1;
            }
            let (s, c2) = adc(t_n, c, 0);
            t_n = s;
            let t_n1 = c2;
            let m = t[0].wrapping_mul(self.pinv);
            let (_, mut c) = mac(t[0], m, self.p[0], 0);
            let mut j = 1;
            while j < N {
                let (lo, hi) = mac(t[j], m, self.p[j], c);
                t[j - 1] = lo;
                c = hi;
                j += 1;
            }
            let (s, c3) = adc(t_n, c, 0);
            t[N - 1] = s;
            t_n = t_n1 + c3;
            i += 1;
        }
        if t_n != 0 || limbs_ge(&t, &self.p) {
            limbs_sub(&t, &self.p).0
        } else {
            t
        }
    }

    pub const fn square(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, a)
    }

    pub const fn add(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let (s, carry) = limbs_add(a, b);
        if carry != 0 || limbs_ge(&s, &self.p) {
            limbs_sub(&s, &self.p).0
        } else {
            s
        }
    }

    pub const fn sub(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let (d, borrow) = limbs_sub(a, b);
        if borrow != 0 {
            limbs_add(&d, &self.p).0
        } else {
            d
        }
    }

    pub const fn neg(&self, a: &Limbs<N>) -> Limbs<N> {
        if limbs_is_zero(a) {
            *a
        } else {
            limbs_sub(&self.p, a).0
        }
    }

    pub const fn double(&self, a: &Limbs<N>) -> Limbs<N> {
        self.add(a, a)
    }

    /// Canonical integer (`< p`) to Montgomery form.
    pub const fn to_mont(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, &self.r2)
    }

    /// Montgomery form to canonical integer.
    pub const fn from_mont(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, &limbs_from_u64::<N>(1))
    }

    pub const fn from_u64(&self, v: u64) -> Limbs<N> {
        let reduced = if limbs_bits(&self.p) <= 64 {
            v % self.p[0]
        } else {
            v
        };
        self.to_mont(&limbs_from_u64::<N>(reduced))
    }

    /// Strict big-endian decoding: `None` unless the integer is `< p`. Returns Montgomery form.
    pub fn from_be_strict(&self, bytes: &[u8]) -> Option<Limbs<N>> {
        let x = limbs_from_be::<N>(bytes)?;
        if limbs_ge(&x, &self.p) {
            return None;
        }
        Some(self.to_mont(&x))
    }

    /// Reduce an arbitrary-length big-endian integer modulo `p`. Returns Montgomery form.
    pub fn from_be_reduce(&self, bytes: &[u8]) -> Limbs<N> {
        // Horner over 32-bit digits: acc = acc * 2^32 + d (all in Montgomery form). A leading
        // partial digit is the integer its bytes spell.
        let base = self.from_u64(1u64 << 32);
        let (head, digits) = bytes.split_at(bytes.len() % 4);
        let mut first = [0u8; 4];
        first[4 - head.len()..].copy_from_slice(head);
        let mut acc = self.from_u64(u64::from(u32::from_be_bytes(first)));
        for chunk in digits.as_chunks::<4>().0 {
            let d = u64::from(u32::from_be_bytes(*chunk));
            acc = self.add(&self.mul(&acc, &base), &self.from_u64(d));
        }
        acc
    }

    /// Montgomery form to exactly `out.len()` big-endian bytes of the canonical integer (panics if
    /// the representative is wider than `out`).
    pub fn to_be_into(&self, a: &Limbs<N>, out: &mut [u8]) {
        limbs_to_be_into(&self.from_mont(a), out).expect("Mont::to_be_into: width too small");
    }

    /// Montgomery form to exactly `len` big-endian bytes of the canonical integer.
    #[cfg(feature = "alloc")]
    pub fn to_be(&self, a: &Limbs<N>, len: usize) -> Vec<u8> {
        let mut out = vec![0u8; len];
        self.to_be_into(a, &mut out);
        out
    }

    /// `base^exp` with `base` in Montgomery form and `exp` a canonical limb integer.
    pub const fn pow_limbs<const M: usize>(&self, base: &Limbs<N>, exp: &Limbs<M>) -> Limbs<N> {
        let mut acc = self.one;
        let mut i = limbs_bits(exp);
        while i > 0 {
            i -= 1;
            acc = self.square(&acc);
            if limbs_bit(exp, i) {
                acc = self.mul(&acc, base);
            }
        }
        acc
    }

    /// `base^exp` with a big-endian byte exponent.
    pub fn pow_be(&self, base: &Limbs<N>, exp: &[u8]) -> Limbs<N> {
        let mut acc = self.one;
        for &byte in exp {
            for bit in (0..8).rev() {
                acc = self.square(&acc);
                if (byte >> bit) & 1 == 1 {
                    acc = self.mul(&acc, base);
                }
            }
        }
        acc
    }

    /// Fermat inverse `a^(p-2)` (prime `p`; returns 0 for 0).
    pub const fn inv(&self, a: &Limbs<N>) -> Limbs<N> {
        self.pow_limbs(a, &self.p_minus_2)
    }

    pub const fn is_zero(&self, a: &Limbs<N>) -> bool {
        limbs_is_zero(a)
    }

    pub fn eq(&self, a: &Limbs<N>, b: &Limbs<N>) -> bool {
        a == b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const P256: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";

    #[test]
    fn small_prime_field_roundtrip() {
        // p = 2^61 - 1 in a 2-limb context exercises zero upper limbs.
        let m = Mont::<2>::new([(1u64 << 61) - 1, 0]).unwrap();
        let a = m.from_u64(123_456_789);
        let b = m.from_u64(987_654_321);
        let prod = m.from_mont(&m.mul(&a, &b));
        // The product is below the modulus 2^61 - 1.
        assert_eq!(prod[0], 123_456_789u64 * 987_654_321);
        let inv = m.inv(&a);
        assert_eq!(m.mul(&inv, &a), m.one());
        assert_eq!(m.add(&m.sub(&a, &b), &b), a);
        assert!(Mont::<2>::new([10, 0]).is_none());
        assert!(Mont::<2>::new([1, 0]).is_none());
        assert!(Mont::<0>::new([]).is_none());
    }

    #[test]
    fn reduce_matches_strict_for_small_inputs() {
        let m = Mont::<4>::from_hex(P256);
        let bytes = [0x12u8, 0x34, 0x56, 0x78, 0x9a];
        assert_eq!(m.from_be_reduce(&bytes), m.from_be_strict(&bytes).unwrap());
        // p itself reduces to zero and is refused by the strict decoder.
        let mut p_bytes = [0u8; 32];
        limbs_to_be_into(m.modulus(), &mut p_bytes).unwrap();
        assert!(m.from_be_strict(&p_bytes).is_none());
        assert!(m.is_zero(&m.from_be_reduce(&p_bytes)));
    }

    #[test]
    fn reduce_handles_every_partial_leading_digit() {
        // Every input length, including the empty one and lengths past the modulus width.
        let m = Mont::<4>::from_hex(P256);
        assert!(m.is_zero(&m.from_be_reduce(&[])));
        // `2^256 mod p` in Montgomery form: `R mod p` is the canonical value of `one`.
        let r256 = m.to_mont(&m.one());
        let wide: std::vec::Vec<u8> = (1..=41u8).collect();
        for len in 0..=wide.len() {
            let bytes = &wide[wide.len() - len..];
            let want = if len <= 32 {
                m.from_be_strict(bytes).unwrap()
            } else {
                // hi * 2^256 + lo, both parts below p.
                let (hi, lo) = bytes.split_at(len - 32);
                let hi = m.from_be_strict(hi).unwrap();
                m.add(&m.mul(&hi, &r256), &m.from_be_strict(lo).unwrap())
            };
            assert_eq!(m.from_be_reduce(bytes), want, "length {len}");
        }
    }

    #[test]
    fn hex_constants_skip_separators_and_encode_back() {
        let a = limbs_from_hex::<2>("0123_4567 89ab\tcdef\nFEDC_BA98_7654_3210");
        assert_eq!(a, [0xFEDC_BA98_7654_3210, 0x0123_4567_89ab_cdef]);
        let mut out = [0u8; 17];
        limbs_to_be_into(&a, &mut out).unwrap();
        assert_eq!(out[0], 0);
        assert_eq!(limbs_from_be::<2>(&out), Some(a));
        assert!(limbs_to_be_into(&a, &mut [0u8; 15]).is_none());
        assert!(limbs_from_be::<1>(&out).is_none());
        let m = Mont::<4>::from_hex(P256);
        let mut enc = [0u8; 32];
        m.to_be_into(&m.from_u64(0x0102), &mut enc);
        assert_eq!(&enc[29..], &[0, 1, 2]);
        assert!(enc[..29].iter().all(|&b| b == 0));
    }

    #[test]
    fn contexts_evaluate_at_compile_time() {
        const M: Mont<4> = Mont::from_hex(P256);
        const TWO_INV: Limbs<4> = M.inv(&M.from_u64(2));
        assert_eq!(M, Mont::<4>::from_hex(P256));
        assert_eq!(M.mul(&TWO_INV, &M.from_u64(2)), M.one());
    }
}
