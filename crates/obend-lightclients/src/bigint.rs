//! Fixed-width little-endian `u64`-limb Montgomery arithmetic (CIOS, Koç–Acar–Kaliski 1996),
//! runtime-parameterised by an odd modulus `p < 2^(64N)`.
//!
//! One generic engine carries every prime/composite modulus in this crate: P-256 / P-384 base
//! and scalar fields (`N = 4 / 6`), Curve25519 `p` and `ℓ` (`N = 4`), BLS12-381 `Fp` / `Fr`
//! (`N = 6 / 4`), and RSA moduli up to 4096 bits (`N = 64`, upper limbs may be zero).
//!
//! Values passed to [`Mont::mul`], [`Mont::add`], [`Mont::sub`] must be fully reduced (`< p`);
//! every operation returns a fully reduced value. Verification paths handle public data only, so
//! the engine is variable-time (documented; not used with long-term secrets outside fixtures).

/// Little-endian 64-bit limbs.
pub type Limbs<const N: usize> = [u64; N];

#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = u128::from(acc) + u128::from(a) * u128::from(b) + u128::from(carry);
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = u128::from(a) + u128::from(b) + u128::from(carry);
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = u128::from(a)
        .wrapping_sub(u128::from(b))
        .wrapping_sub(u128::from(borrow));
    (t as u64, ((t >> 64) as u64) & 1)
}

/// `a >= b` on equal-width limb arrays.
pub fn limbs_ge<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> bool {
    for i in (0..N).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

/// `a - b` (wrapping), returning `(difference, borrow)`.
pub fn limbs_sub<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> (Limbs<N>, u64) {
    let mut out = [0u64; N];
    let mut borrow = 0u64;
    for i in 0..N {
        let (d, br) = sbb(a[i], b[i], borrow);
        out[i] = d;
        borrow = br;
    }
    (out, borrow)
}

/// `a + b` (wrapping), returning `(sum, carry)`.
pub fn limbs_add<const N: usize>(a: &Limbs<N>, b: &Limbs<N>) -> (Limbs<N>, u64) {
    let mut out = [0u64; N];
    let mut carry = 0u64;
    for i in 0..N {
        let (s, c) = adc(a[i], b[i], carry);
        out[i] = s;
        carry = c;
    }
    (out, carry)
}

pub fn limbs_is_zero<const N: usize>(a: &Limbs<N>) -> bool {
    a.iter().all(|&x| x == 0)
}

pub fn limbs_from_u64<const N: usize>(v: u64) -> Limbs<N> {
    let mut out = [0u64; N];
    out[0] = v;
    out
}

/// Number of significant bits.
pub fn limbs_bits<const N: usize>(a: &Limbs<N>) -> usize {
    for i in (0..N).rev() {
        if a[i] != 0 {
            return 64 * i + (64 - a[i].leading_zeros() as usize);
        }
    }
    0
}

pub fn limbs_bit<const N: usize>(a: &Limbs<N>, i: usize) -> bool {
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

/// Limbs to exactly `len` big-endian bytes (`None` if the value does not fit).
pub fn limbs_to_be<const N: usize>(a: &Limbs<N>, len: usize) -> Option<Vec<u8>> {
    if limbs_bits(a) > 8 * len {
        return None;
    }
    let mut out = vec![0u8; len];
    for i in 0..len.min(8 * N) {
        out[len - 1 - i] = (a[i / 8] >> (8 * (i % 8))) as u8;
    }
    Some(out)
}

/// Parse a big-endian hex constant (panics on malformed input; constants only).
pub fn limbs_from_hex<const N: usize>(hex: &str) -> Limbs<N> {
    let digits: Vec<u8> = hex
        .bytes()
        .filter(|c| !c.is_ascii_whitespace() && *c != b'_')
        .map(|c| match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => panic!("limbs_from_hex: non-hex digit"),
        })
        .collect();
    assert!(digits.len() <= 16 * N, "limbs_from_hex: constant too wide");
    let mut out = [0u64; N];
    for (i, &d) in digits.iter().rev().enumerate() {
        out[i / 16] |= u64::from(d) << (4 * (i % 16));
    }
    out
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
    pub fn new(p: Limbs<N>) -> Option<Self> {
        if N == 0 || p[0] & 1 == 0 || (limbs_bits(&p) < 2) {
            return None;
        }
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p[0].wrapping_mul(inv)));
        }
        let pinv = inv.wrapping_neg();
        // x = 1; double 64N times -> R mod p; double 64N more -> R^2 mod p.
        let mut x = limbs_from_u64::<N>(1);
        let double = |x: &Limbs<N>| -> Limbs<N> {
            let (s, carry) = limbs_add(x, x);
            if carry != 0 || limbs_ge(&s, &p) {
                limbs_sub(&s, &p).0
            } else {
                s
            }
        };
        for _ in 0..64 * N {
            x = double(&x);
        }
        let one = x;
        for _ in 0..64 * N {
            x = double(&x);
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

    pub fn from_hex(hex: &str) -> Self {
        Self::new(limbs_from_hex(hex)).expect("Mont::from_hex: odd modulus")
    }

    pub fn modulus(&self) -> &Limbs<N> {
        &self.p
    }

    pub fn modulus_bits(&self) -> usize {
        limbs_bits(&self.p)
    }

    /// Montgomery form of 1.
    pub fn one(&self) -> Limbs<N> {
        self.one
    }

    pub fn zero(&self) -> Limbs<N> {
        [0u64; N]
    }

    /// Montgomery product `a * b * R^{-1} mod p` (CIOS).
    pub fn mul(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let mut t = [0u64; N];
        let mut t_n = 0u64;
        for &b_limb in b {
            let mut c = 0u64;
            for j in 0..N {
                let (lo, hi) = mac(t[j], a[j], b_limb, c);
                t[j] = lo;
                c = hi;
            }
            let (s, c2) = adc(t_n, c, 0);
            t_n = s;
            let t_n1 = c2;
            let m = t[0].wrapping_mul(self.pinv);
            let (_, mut c) = mac(t[0], m, self.p[0], 0);
            for j in 1..N {
                let (lo, hi) = mac(t[j], m, self.p[j], c);
                t[j - 1] = lo;
                c = hi;
            }
            let (s, c3) = adc(t_n, c, 0);
            t[N - 1] = s;
            t_n = t_n1 + c3;
        }
        if t_n != 0 || limbs_ge(&t, &self.p) {
            limbs_sub(&t, &self.p).0
        } else {
            t
        }
    }

    pub fn square(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, a)
    }

    pub fn add(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let (s, carry) = limbs_add(a, b);
        if carry != 0 || limbs_ge(&s, &self.p) {
            limbs_sub(&s, &self.p).0
        } else {
            s
        }
    }

    pub fn sub(&self, a: &Limbs<N>, b: &Limbs<N>) -> Limbs<N> {
        let (d, borrow) = limbs_sub(a, b);
        if borrow != 0 {
            limbs_add(&d, &self.p).0
        } else {
            d
        }
    }

    pub fn neg(&self, a: &Limbs<N>) -> Limbs<N> {
        if limbs_is_zero(a) {
            *a
        } else {
            limbs_sub(&self.p, a).0
        }
    }

    pub fn double(&self, a: &Limbs<N>) -> Limbs<N> {
        self.add(a, a)
    }

    /// Canonical integer (`< p`) to Montgomery form.
    pub fn to_mont(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, &self.r2)
    }

    /// Montgomery form to canonical integer.
    pub fn from_mont(&self, a: &Limbs<N>) -> Limbs<N> {
        self.mul(a, &limbs_from_u64::<N>(1))
    }

    pub fn from_u64(&self, v: u64) -> Limbs<N> {
        let reduced = if limbs_bits(&self.p) <= 64 {
            v % self.p[0]
        } else {
            v
        };
        let x = limbs_from_u64::<N>(reduced);
        self.to_mont(&x)
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
        // Horner over 32-bit digits: acc = acc * 2^32 + d (all in Montgomery form).
        let base = self.from_u64(1u64 << 32);
        let mut acc = self.zero();
        let pad = (4 - bytes.len() % 4) % 4;
        let mut buf = vec![0u8; pad];
        buf.extend_from_slice(bytes);
        for chunk in buf.as_chunks::<4>().0 {
            let d = u64::from(u32::from_be_bytes(*chunk));
            acc = self.add(&self.mul(&acc, &base), &self.from_u64(d));
        }
        acc
    }

    /// Montgomery form to exactly `len` big-endian bytes of the canonical integer.
    pub fn to_be(&self, a: &Limbs<N>, len: usize) -> Vec<u8> {
        limbs_to_be(&self.from_mont(a), len).expect("Mont::to_be: width too small")
    }

    /// `base^exp` with `base` in Montgomery form and `exp` a canonical limb integer.
    pub fn pow_limbs<const M: usize>(&self, base: &Limbs<N>, exp: &Limbs<M>) -> Limbs<N> {
        let mut acc = self.one;
        for i in (0..limbs_bits(exp)).rev() {
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
    pub fn inv(&self, a: &Limbs<N>) -> Limbs<N> {
        self.pow_limbs(a, &self.p_minus_2)
    }

    pub fn is_zero(&self, a: &Limbs<N>) -> bool {
        limbs_is_zero(a)
    }

    pub fn eq(&self, a: &Limbs<N>, b: &Limbs<N>) -> bool {
        a == b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    }

    #[test]
    fn reduce_matches_strict_for_small_inputs() {
        let m =
            Mont::<4>::from_hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
        let bytes = [0x12u8, 0x34, 0x56, 0x78, 0x9a];
        assert_eq!(m.from_be_reduce(&bytes), m.from_be_strict(&bytes).unwrap());
        // p itself reduces to zero and is refused by the strict decoder.
        let p_bytes = limbs_to_be(m.modulus(), 32).unwrap();
        assert!(m.from_be_strict(&p_bytes).is_none());
        assert!(m.is_zero(&m.from_be_reduce(&p_bytes)));
    }
}
