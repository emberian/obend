//! FIPS 186-5 ECDSA over P-256 (`secp256r1`) and P-384 (`secp384r1`), RFC 5280
//! `SubjectPublicKeyInfo` / `AlgorithmIdentifier` codecs, and one signature-verification dispatch
//! covering ECDSA, RFC 8017 RSA (PKCS#1 v1.5 and PSS, see [`crate::rsa`]) and RFC 8032 Ed25519
//! (see [`crate::ed25519`]). Pure Rust, zero external crates.
//!
//! ECDSA verification enforces: `0 < r, s < n`; public point on `y² = x³ − 3x + b` with
//! coordinates `< p` and not the point at infinity (cofactor 1, so on-curve ⇒ prime-order group);
//! strict DER `Ecdsa-Sig-Value` (minimal positive INTEGERs, no trailing bytes) or fixed-width
//! `r ‖ s`; `R = u₁G + u₂Q ≠ O` and `x(R) mod n = r`.
//!
//! [`FixtureSigner`] produces deterministic signatures (RFC 6979 for ECDSA) for conformance
//! fixtures. It is variable-time and must never hold production keys.

use std::sync::OnceLock;

use crate::bigint::{limbs_from_be, limbs_from_hex, limbs_ge, limbs_is_zero, Limbs, Mont};
use crate::ed25519;
use crate::rsa;
use crate::sha256::{hmac_sha256, sha256};
use crate::sha512::{hmac_sha384, sha384, sha512};

// ---------------------------------------------------------------------------
// Hashes & errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HashAlg {
    Sha256,
    Sha384,
}

impl HashAlg {
    pub fn digest(self, msg: &[u8]) -> Vec<u8> {
        match self {
            Self::Sha256 => sha256(msg).to_vec(),
            Self::Sha384 => sha384(msg).to_vec(),
        }
    }

    pub fn output_len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
        }
    }

    pub(crate) fn hmac(self, key: &[u8], data: &[u8]) -> Vec<u8> {
        match self {
            Self::Sha256 => hmac_sha256(key, data).to_vec(),
            Self::Sha384 => hmac_sha384(key, data).to_vec(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CryptoError {
    MalformedDer,
    UnsupportedAlgorithm,
    UnsupportedCurve,
    InvalidFieldElement,
    PointNotOnCurve,
    PointAtInfinity,
    /// `r` or `s` outside `[1, n − 1]`.
    ScalarOutOfRange,
    BadSignatureLength,
    KeyAlgorithmMismatch,
    RsaModulusSize,
    RsaBadExponent,
    RsaSignatureOutOfRange,
    BadPadding,
    InvalidEd25519Key,
    SignatureMismatch,
}

// ---------------------------------------------------------------------------
// Minimal strict DER
// ---------------------------------------------------------------------------

/// Parse one DER TLV (single-byte tag, minimal definite length). Returns `(tag, value, rest)`.
pub fn der_tlv(input: &[u8]) -> Result<(u8, &[u8], &[u8]), CryptoError> {
    let e = CryptoError::MalformedDer;
    let &tag = input.first().ok_or(e)?;
    if tag & 0x1f == 0x1f {
        return Err(e);
    }
    let &lb = input.get(1).ok_or(e)?;
    let (len, hdr) = if lb & 0x80 == 0 {
        (usize::from(lb), 2usize)
    } else {
        let k = usize::from(lb & 0x7f);
        if k == 0 || k > 4 {
            return Err(e);
        }
        let bytes = input.get(2..2 + k).ok_or(e)?;
        if bytes[0] == 0 {
            return Err(e);
        }
        let len = bytes.iter().fold(0usize, |a, &b| (a << 8) | usize::from(b));
        if len < 0x80 {
            return Err(e);
        }
        (len, 2 + k)
    };
    let end = hdr.checked_add(len).ok_or(e)?;
    let value = input.get(hdr..end).ok_or(e)?;
    Ok((tag, value, &input[end..]))
}

/// Expect a TLV with `tag`; returns `(value, rest)`.
pub fn der_expect(input: &[u8], tag: u8) -> Result<(&[u8], &[u8]), CryptoError> {
    let (t, v, rest) = der_tlv(input)?;
    if t != tag {
        return Err(CryptoError::MalformedDer);
    }
    Ok((v, rest))
}

/// Strict DER non-negative INTEGER content to big-endian magnitude (empty for zero).
pub fn der_uint(content: &[u8]) -> Result<&[u8], CryptoError> {
    let e = CryptoError::MalformedDer;
    match content {
        [] => Err(e),
        [b, ..] if b & 0x80 != 0 => Err(e),
        [0] => Ok(&content[1..]),
        [0, b, ..] if b & 0x80 == 0 => Err(e),
        [0, ..] => Ok(&content[1..]),
        _ => Ok(content),
    }
}

/// DER-encode one TLV.
pub fn der_encode(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    let n = body.len();
    if n < 0x80 {
        out.push(n as u8);
    } else {
        let bytes: Vec<u8> = n
            .to_be_bytes()
            .iter()
            .copied()
            .skip_while(|&b| b == 0)
            .collect();
        out.push(0x80 | bytes.len() as u8);
        out.extend_from_slice(&bytes);
    }
    out.extend_from_slice(body);
    out
}

/// DER-encode a non-negative INTEGER from a big-endian magnitude.
pub fn der_encode_uint(mag: &[u8]) -> Vec<u8> {
    let first = mag.iter().position(|&b| b != 0).unwrap_or(mag.len());
    let mag = &mag[first..];
    let mut body = Vec::with_capacity(mag.len() + 1);
    if mag.is_empty() || mag[0] & 0x80 != 0 {
        body.push(0);
    }
    body.extend_from_slice(mag);
    der_encode(0x02, &body)
}

// ---------------------------------------------------------------------------
// Short-Weierstrass a = -3 prime-order curves (P-256, P-384)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct Jac<const N: usize> {
    x: Limbs<N>,
    y: Limbs<N>,
    z: Limbs<N>,
}

struct Curve<const N: usize> {
    fp: Mont<N>,
    fq: Mont<N>,
    n: Limbs<N>,
    b: Limbs<N>,
    g: Jac<N>,
    /// Field / scalar byte length (32 or 48).
    len: usize,
    hash: HashAlg,
}

fn p256() -> &'static Curve<4> {
    static C: OnceLock<Curve<4>> = OnceLock::new();
    C.get_or_init(|| {
        Curve::new(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
            "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
            "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
            "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
            32,
            HashAlg::Sha256,
        )
    })
}

fn p384() -> &'static Curve<6> {
    static C: OnceLock<Curve<6>> = OnceLock::new();
    C.get_or_init(|| {
        Curve::new(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
            "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
            "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
            "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
            "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
            48,
            HashAlg::Sha384,
        )
    })
}

impl<const N: usize> Curve<N> {
    fn new(p: &str, n: &str, b: &str, gx: &str, gy: &str, len: usize, hash: HashAlg) -> Self {
        let fp = Mont::<N>::from_hex(p);
        let n_l = limbs_from_hex::<N>(n);
        let fq = Mont::<N>::new(n_l).expect("odd prime order");
        let b = fp.to_mont(&limbs_from_hex::<N>(b));
        let g = Jac {
            x: fp.to_mont(&limbs_from_hex::<N>(gx)),
            y: fp.to_mont(&limbs_from_hex::<N>(gy)),
            z: fp.one(),
        };
        Self {
            fp,
            fq,
            n: n_l,
            b,
            g,
            len,
            hash,
        }
    }

    fn infinity(&self) -> Jac<N> {
        Jac {
            x: self.fp.one(),
            y: self.fp.one(),
            z: self.fp.zero(),
        }
    }

    fn is_inf(&self, p: &Jac<N>) -> bool {
        limbs_is_zero(&p.z)
    }

    /// `dbl-2001-b` (a = −3).
    fn double(&self, p: &Jac<N>) -> Jac<N> {
        let f = &self.fp;
        if self.is_inf(p) {
            return *p;
        }
        let delta = f.square(&p.z);
        let gamma = f.square(&p.y);
        let beta = f.mul(&p.x, &gamma);
        let t = f.mul(&f.sub(&p.x, &delta), &f.add(&p.x, &delta));
        let alpha = f.add(&f.double(&t), &t);
        let beta4 = f.double(&f.double(&beta));
        let x3 = f.sub(&f.square(&alpha), &f.double(&beta4));
        let yz = f.add(&p.y, &p.z);
        let z3 = f.sub(&f.sub(&f.square(&yz), &gamma), &delta);
        let g2 = f.square(&gamma);
        let g8 = f.double(&f.double(&f.double(&g2)));
        let y3 = f.sub(&f.mul(&alpha, &f.sub(&beta4, &x3)), &g8);
        Jac {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// General Jacobian addition with doubling / inverse special cases.
    fn add(&self, p: &Jac<N>, q: &Jac<N>) -> Jac<N> {
        let f = &self.fp;
        if self.is_inf(p) {
            return *q;
        }
        if self.is_inf(q) {
            return *p;
        }
        let z1z1 = f.square(&p.z);
        let z2z2 = f.square(&q.z);
        let u1 = f.mul(&p.x, &z2z2);
        let u2 = f.mul(&q.x, &z1z1);
        let s1 = f.mul(&f.mul(&p.y, &q.z), &z2z2);
        let s2 = f.mul(&f.mul(&q.y, &p.z), &z1z1);
        let h = f.sub(&u2, &u1);
        let r = f.sub(&s2, &s1);
        if f.is_zero(&h) {
            return if f.is_zero(&r) {
                self.double(p)
            } else {
                self.infinity()
            };
        }
        let hh = f.square(&h);
        let hhh = f.mul(&h, &hh);
        let v = f.mul(&u1, &hh);
        let x3 = f.sub(&f.sub(&f.square(&r), &hhh), &f.double(&v));
        let y3 = f.sub(&f.mul(&r, &f.sub(&v, &x3)), &f.mul(&s1, &hhh));
        let z3 = f.mul(&f.mul(&p.z, &q.z), &h);
        Jac {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Variable-time double-and-add; `k` canonical.
    fn mul(&self, p: &Jac<N>, k: &Limbs<N>) -> Jac<N> {
        let mut acc = self.infinity();
        for i in (0..crate::bigint::limbs_bits(k)).rev() {
            acc = self.double(&acc);
            if crate::bigint::limbs_bit(k, i) {
                acc = self.add(&acc, p);
            }
        }
        acc
    }

    /// Affine `(x, y)` in Montgomery form, `None` at infinity.
    fn to_affine(&self, p: &Jac<N>) -> Option<(Limbs<N>, Limbs<N>)> {
        if self.is_inf(p) {
            return None;
        }
        let f = &self.fp;
        let zi = f.inv(&p.z);
        let zi2 = f.square(&zi);
        Some((f.mul(&p.x, &zi2), f.mul(&p.y, &f.mul(&zi2, &zi))))
    }

    fn on_curve(&self, x: &Limbs<N>, y: &Limbs<N>) -> bool {
        let f = &self.fp;
        let x3 = f.mul(&f.square(x), x);
        let three_x = f.add(&f.double(x), x);
        let rhs = f.add(&f.sub(&x3, &three_x), &self.b);
        f.square(y) == rhs
    }

    /// Strict SEC1 uncompressed decoding (`0x04 ‖ X ‖ Y`, `X, Y < p`, on-curve).
    fn decode_sec1(&self, bytes: &[u8]) -> Result<Jac<N>, CryptoError> {
        if bytes.len() != 1 + 2 * self.len {
            return Err(CryptoError::InvalidFieldElement);
        }
        if bytes[0] != 0x04 {
            // 0x00 would encode infinity; compressed forms are not accepted.
            return Err(if bytes[0] == 0x00 {
                CryptoError::PointAtInfinity
            } else {
                CryptoError::InvalidFieldElement
            });
        }
        let x = self
            .fp
            .from_be_strict(&bytes[1..1 + self.len])
            .ok_or(CryptoError::InvalidFieldElement)?;
        let y = self
            .fp
            .from_be_strict(&bytes[1 + self.len..])
            .ok_or(CryptoError::InvalidFieldElement)?;
        if !self.on_curve(&x, &y) {
            return Err(CryptoError::PointNotOnCurve);
        }
        Ok(Jac {
            x,
            y,
            z: self.fp.one(),
        })
    }

    fn encode_sec1(&self, p: &Jac<N>) -> Vec<u8> {
        let (x, y) = self.to_affine(p).expect("finite point");
        let mut out = vec![0x04];
        out.extend_from_slice(&self.fp.to_be(&x, self.len));
        out.extend_from_slice(&self.fp.to_be(&y, self.len));
        out
    }

    /// Canonical scalar in `[1, n − 1]` from a big-endian magnitude.
    fn scalar(&self, bytes: &[u8]) -> Result<Limbs<N>, CryptoError> {
        let k = limbs_from_be::<N>(bytes).ok_or(CryptoError::ScalarOutOfRange)?;
        if limbs_is_zero(&k) || limbs_ge(&k, &self.n) {
            return Err(CryptoError::ScalarOutOfRange);
        }
        Ok(k)
    }

    /// `bits2int(digest) mod n` (FIPS 186-5 §6.4.1 / RFC 6979 §2.3.2), Montgomery form in `fq`.
    /// `n` has exactly `8 * len` bits for both curves, so truncation is byte-aligned.
    fn digest_to_scalar(&self, digest: &[u8]) -> Limbs<N> {
        let take = digest.len().min(self.len);
        self.fq.from_be_reduce(&digest[..take])
    }

    fn verify(&self, q: &Jac<N>, digest: &[u8], r: &[u8], s: &[u8]) -> Result<(), CryptoError> {
        if self.is_inf(q) {
            return Err(CryptoError::PointAtInfinity);
        }
        let fq = &self.fq;
        let r_l = self.scalar(r)?;
        let s_l = self.scalar(s)?;
        let e = self.digest_to_scalar(digest);
        let r_m = fq.to_mont(&r_l);
        let w = fq.inv(&fq.to_mont(&s_l));
        let u1 = fq.from_mont(&fq.mul(&e, &w));
        let u2 = fq.from_mont(&fq.mul(&r_m, &w));
        let big_r = self.add(&self.mul(&self.g, &u1), &self.mul(q, &u2));
        let (x, _) = self
            .to_affine(&big_r)
            .ok_or(CryptoError::SignatureMismatch)?;
        let v = fq.from_be_reduce(&self.fp.to_be(&x, self.len));
        if v == r_m {
            Ok(())
        } else {
            Err(CryptoError::SignatureMismatch)
        }
    }

    /// RFC 6979 deterministic ECDSA (HMAC with the curve's hash). Fixture use only.
    fn sign(&self, d: &Limbs<N>, digest: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let fq = &self.fq;
        let hl = self.hash.output_len();
        let x = crate::bigint::limbs_to_be(d, self.len).expect("scalar width");
        let h1 = fq.to_be(&self.digest_to_scalar(digest), self.len);
        let mut v = vec![0x01u8; hl];
        let mut k = vec![0x00u8; hl];
        let seed = |k: &mut Vec<u8>, v: &mut Vec<u8>, tag: u8| {
            let mut m = v.clone();
            m.push(tag);
            m.extend_from_slice(&x);
            m.extend_from_slice(&h1);
            *k = self.hash.hmac(k, &m);
            *v = self.hash.hmac(k, v);
        };
        seed(&mut k, &mut v, 0x00);
        seed(&mut k, &mut v, 0x01);
        loop {
            let mut t = Vec::new();
            while t.len() < self.len {
                v = self.hash.hmac(&k, &v);
                t.extend_from_slice(&v);
            }
            if let Ok(kk) = self.scalar(&t[..self.len]) {
                if let Some((rx, _)) = self.to_affine(&self.mul(&self.g, &kk)) {
                    let r = fq.from_be_reduce(&self.fp.to_be(&rx, self.len));
                    if !fq.is_zero(&r) {
                        let e = self.digest_to_scalar(digest);
                        let kinv = fq.inv(&fq.to_mont(&kk));
                        let s = fq.mul(&kinv, &fq.add(&e, &fq.mul(&r, &fq.to_mont(d))));
                        if !fq.is_zero(&s) {
                            return (fq.to_be(&r, self.len), fq.to_be(&s, self.len));
                        }
                    }
                }
            }
            let mut m = v.clone();
            m.push(0x00);
            k = self.hash.hmac(&k, &m);
            v = self.hash.hmac(&k, &v);
        }
    }

    /// Fixture scalar `SHA-512(tag ‖ seed) mod n`, mapped away from zero.
    fn fixture_scalar(&self, seed: &[u8]) -> Limbs<N> {
        let mut pre = b"OBEND.FIXTURE.ECDSA/v1".to_vec();
        pre.extend_from_slice(seed);
        let d = self.fq.from_mont(&self.fq.from_be_reduce(&sha512(&pre)));
        if limbs_is_zero(&d) {
            crate::bigint::limbs_from_u64::<N>(1)
        } else {
            d
        }
    }
}

/// Strict DER `Ecdsa-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }` to magnitudes.
pub fn parse_ecdsa_der(sig: &[u8]) -> Result<(Vec<u8>, Vec<u8>), CryptoError> {
    let (body, rest) = der_expect(sig, 0x30)?;
    if !rest.is_empty() {
        return Err(CryptoError::MalformedDer);
    }
    let (r, body) = der_expect(body, 0x02)?;
    let (s, body) = der_expect(body, 0x02)?;
    if !body.is_empty() {
        return Err(CryptoError::MalformedDer);
    }
    Ok((der_uint(r)?.to_vec(), der_uint(s)?.to_vec()))
}

pub fn encode_ecdsa_der(r: &[u8], s: &[u8]) -> Vec<u8> {
    let mut body = der_encode_uint(r);
    body.extend_from_slice(&der_encode_uint(s));
    der_encode(0x30, &body)
}

// ---------------------------------------------------------------------------
// SubjectPublicKeyInfo & AlgorithmIdentifier (RFC 5280 / 5480 / 4055 / 8410)
// ---------------------------------------------------------------------------

const OID_EC_PUBLIC_KEY: &[u8] = &[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const OID_P256: &[u8] = &[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
const OID_P384: &[u8] = &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x22];
const OID_RSA_ENCRYPTION: &[u8] = &[
    0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01,
];
const OID_ED25519: &[u8] = &[0x06, 0x03, 0x2b, 0x65, 0x70];
const DER_NULL: &[u8] = &[0x05, 0x00];

/// A parsed, validated subject public key (EC points are SEC1 uncompressed and on-curve).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubjectPublicKey {
    P256([u8; 65]),
    P384([u8; 97]),
    Rsa { n: Vec<u8>, e: Vec<u8> },
    Ed25519([u8; 32]),
}

impl SubjectPublicKey {
    /// Strictly parse a full DER `SubjectPublicKeyInfo` TLV (no trailing bytes).
    pub fn from_spki_der(der: &[u8]) -> Result<Self, CryptoError> {
        let (spki, rest) = der_expect(der, 0x30)?;
        if !rest.is_empty() {
            return Err(CryptoError::MalformedDer);
        }
        let (alg, rest) = der_expect(spki, 0x30)?;
        let (bits, rest) = der_expect(rest, 0x03)?;
        if !rest.is_empty() || bits.first() != Some(&0) {
            return Err(CryptoError::MalformedDer);
        }
        let key = &bits[1..];
        if alg.starts_with(OID_EC_PUBLIC_KEY) {
            let curve = &alg[OID_EC_PUBLIC_KEY.len()..];
            if curve == OID_P256 {
                p256().decode_sec1(key)?;
                let mut out = [0u8; 65];
                out.copy_from_slice(key);
                Ok(Self::P256(out))
            } else if curve == OID_P384 {
                p384().decode_sec1(key)?;
                let mut out = [0u8; 97];
                out.copy_from_slice(key);
                Ok(Self::P384(out))
            } else {
                Err(CryptoError::UnsupportedCurve)
            }
        } else if alg.starts_with(OID_RSA_ENCRYPTION) {
            if &alg[OID_RSA_ENCRYPTION.len()..] != DER_NULL {
                return Err(CryptoError::MalformedDer);
            }
            let (seq, rest) = der_expect(key, 0x30)?;
            if !rest.is_empty() {
                return Err(CryptoError::MalformedDer);
            }
            let (n, seq) = der_expect(seq, 0x02)?;
            let (e, seq) = der_expect(seq, 0x02)?;
            if !seq.is_empty() {
                return Err(CryptoError::MalformedDer);
            }
            let (n, e) = (der_uint(n)?.to_vec(), der_uint(e)?.to_vec());
            rsa::validate_public_key(&n, &e)?;
            Ok(Self::Rsa { n, e })
        } else if alg == OID_ED25519 {
            let pk: [u8; 32] = key.try_into().map_err(|_| CryptoError::InvalidEd25519Key)?;
            if !ed25519::validate_public_key(&pk) {
                return Err(CryptoError::InvalidEd25519Key);
            }
            Ok(Self::Ed25519(pk))
        } else {
            Err(CryptoError::UnsupportedAlgorithm)
        }
    }

    /// Canonical DER `SubjectPublicKeyInfo`.
    pub fn to_spki_der(&self) -> Vec<u8> {
        let (alg_body, key): (Vec<u8>, Vec<u8>) = match self {
            Self::P256(p) => ([OID_EC_PUBLIC_KEY, OID_P256].concat(), p.to_vec()),
            Self::P384(p) => ([OID_EC_PUBLIC_KEY, OID_P384].concat(), p.to_vec()),
            Self::Rsa { n, e } => {
                let mut body = der_encode_uint(n);
                body.extend_from_slice(&der_encode_uint(e));
                (
                    [OID_RSA_ENCRYPTION, DER_NULL].concat(),
                    der_encode(0x30, &body),
                )
            }
            Self::Ed25519(p) => (OID_ED25519.to_vec(), p.to_vec()),
        };
        let mut bits = vec![0u8];
        bits.extend_from_slice(&key);
        let mut body = der_encode(0x30, &alg_body);
        body.extend_from_slice(&der_encode(0x03, &bits));
        der_encode(0x30, &body)
    }
}

/// Signature algorithms accepted by [`verify_signature`]. ECDSA variants pair the curve with its
/// FIPS 186-5 hash (P-256/SHA-256, P-384/SHA-384); PSS uses MGF1 with the same hash, salt length
/// equal to the hash length, trailer field 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureAlgorithm {
    EcdsaP256Sha256,
    EcdsaP384Sha384,
    RsaPkcs1Sha256,
    RsaPkcs1Sha384,
    RsaPssSha256,
    RsaPssSha384,
    Ed25519,
}

const ALGID_ECDSA_SHA256: &[u8] = &[
    0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02,
];
const ALGID_ECDSA_SHA384: &[u8] = &[
    0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03,
];
const ALGID_RSA_SHA256: &[u8] = &[
    0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00,
];
const ALGID_RSA_SHA384: &[u8] = &[
    0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c, 0x05, 0x00,
];
/// RSASSA-PSS AlgorithmIdentifiers exactly as emitted by OpenSSL / pyca (hash & MGF1 AlgIds carry
/// explicit NULL parameters; saltLength = hLen; trailerField omitted = 1).
const ALGID_PSS_SHA256: &[u8] = &[
    0x30, 0x41, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a, 0x30, 0x34, 0xa0,
    0x0f, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00,
    0xa1, 0x1c, 0x30, 0x1a, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30,
    0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0xa2, 0x03,
    0x02, 0x01, 0x20,
];
const ALGID_PSS_SHA384: &[u8] = &[
    0x30, 0x41, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a, 0x30, 0x34, 0xa0,
    0x0f, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00,
    0xa1, 0x1c, 0x30, 0x1a, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30,
    0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00, 0xa2, 0x03,
    0x02, 0x01, 0x30,
];
/// RSASSA-PSS AlgorithmIdentifiers with explicit `[3] trailerField = 1` (`a3 03 02 01 01`), as
/// emitted by real AMD KDS Genoa/Milan/Turin ARK & ASK RSA-4096 certificates.
const ALGID_PSS_SHA256_TF1: &[u8] = &[
    0x30, 0x46, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a, 0x30, 0x39, 0xa0,
    0x0f, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00,
    0xa1, 0x1c, 0x30, 0x1a, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30,
    0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0xa2, 0x03,
    0x02, 0x01, 0x20, 0xa3, 0x03, 0x02, 0x01, 0x01,
];
const ALGID_PSS_SHA384_TF1: &[u8] = &[
    0x30, 0x46, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a, 0x30, 0x39, 0xa0,
    0x0f, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00,
    0xa1, 0x1c, 0x30, 0x1a, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30,
    0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00, 0xa2, 0x03,
    0x02, 0x01, 0x30, 0xa3, 0x03, 0x02, 0x01, 0x01,
];
const ALGID_ED25519: &[u8] = &[0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70];

impl SignatureAlgorithm {
    const ALL: [(Self, &'static [u8]); 7] = [
        (Self::EcdsaP256Sha256, ALGID_ECDSA_SHA256),
        (Self::EcdsaP384Sha384, ALGID_ECDSA_SHA384),
        (Self::RsaPkcs1Sha256, ALGID_RSA_SHA256),
        (Self::RsaPkcs1Sha384, ALGID_RSA_SHA384),
        (Self::RsaPssSha256, ALGID_PSS_SHA256),
        (Self::RsaPssSha384, ALGID_PSS_SHA384),
        (Self::Ed25519, ALGID_ED25519),
    ];

    /// Map a full DER `AlgorithmIdentifier` TLV to a supported algorithm (accepting RFC 4055 §2.1
    /// RSASSA-PSS parameters with either explicit `NULL` or absent hash parameters and omitted or
    /// explicit `trailerField = 1`).
    pub fn from_algorithm_identifier_der(der: &[u8]) -> Result<Self, CryptoError> {
        let (tag, body, rest) = der_tlv(der)?;
        if tag != 0x30 || !rest.is_empty() {
            return Err(CryptoError::MalformedDer);
        }
        if der == ALGID_PSS_SHA256_TF1 {
            return Ok(Self::RsaPssSha256);
        }
        if der == ALGID_PSS_SHA384_TF1 {
            return Ok(Self::RsaPssSha384);
        }
        if let Some((a, _)) = Self::ALL.iter().find(|(_, enc)| *enc == der) {
            return Ok(*a);
        }
        // RFC 4055 §3.1 structural RSASSA-PSS AlgorithmIdentifier parser (accepting absent or NULL
        // parameters inside SHA-256/SHA-384 hashAlgorithm and mgf1 AlgorithmIdentifiers).
        const OID_RSASSA_PSS: &[u8] = &[
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a,
        ];
        const OID_MGF1: &[u8] = &[
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08,
        ];
        const OID_SHA256_TLV: &[u8] = &[
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
        ];
        const OID_SHA384_TLV: &[u8] = &[
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02,
        ];
        if let Some(params_tlv) = body.strip_prefix(OID_RSASSA_PSS) {
            let (pseq, end) = der_expect(params_tlv, 0x30)?;
            if !end.is_empty() {
                return Err(CryptoError::MalformedDer);
            }
            let parse_sha2_alg = |alg_tlv: &[u8]| -> Result<HashAlg, CryptoError> {
                let (ab, aend) = der_expect(alg_tlv, 0x30)?;
                if !aend.is_empty() {
                    return Err(CryptoError::MalformedDer);
                }
                if let Some(rem) = ab.strip_prefix(OID_SHA256_TLV) {
                    if rem.is_empty() || rem == DER_NULL {
                        return Ok(HashAlg::Sha256);
                    }
                } else if let Some(rem) = ab.strip_prefix(OID_SHA384_TLV) {
                    if rem.is_empty() || rem == DER_NULL {
                        return Ok(HashAlg::Sha384);
                    }
                }
                Err(CryptoError::UnsupportedAlgorithm)
            };
            let (h_box, rem) = der_expect(pseq, 0xa0)?;
            let hash_alg = parse_sha2_alg(h_box)?;
            let (m_box, rem) = der_expect(rem, 0xa1)?;
            let (m_body, mend) = der_expect(m_box, 0x30)?;
            if !mend.is_empty() {
                return Err(CryptoError::MalformedDer);
            }
            let mgf_param = m_body
                .strip_prefix(OID_MGF1)
                .ok_or(CryptoError::UnsupportedAlgorithm)?;
            if parse_sha2_alg(mgf_param)? != hash_alg {
                return Err(CryptoError::UnsupportedAlgorithm);
            }
            let (s_box, rem) = der_expect(rem, 0xa2)?;
            let (s_int, send) = der_expect(s_box, 0x02)?;
            if !send.is_empty() || der_uint(s_int)? != [hash_alg.output_len() as u8] {
                return Err(CryptoError::UnsupportedAlgorithm);
            }
            if !rem.is_empty() && rem != [0xa3, 0x03, 0x02, 0x01, 0x01] {
                return Err(CryptoError::UnsupportedAlgorithm);
            }
            return Ok(match hash_alg {
                HashAlg::Sha256 => Self::RsaPssSha256,
                HashAlg::Sha384 => Self::RsaPssSha384,
            });
        }
        Err(CryptoError::UnsupportedAlgorithm)
    }

    pub fn algorithm_identifier_der(self) -> Vec<u8> {
        Self::ALL
            .iter()
            .find(|(a, _)| *a == self)
            .map(|(_, enc)| enc.to_vec())
            .expect("every algorithm has an encoding")
    }

    pub fn hash(self) -> HashAlg {
        match self {
            Self::EcdsaP256Sha256 | Self::RsaPkcs1Sha256 | Self::RsaPssSha256 => HashAlg::Sha256,
            Self::EcdsaP384Sha384 | Self::RsaPkcs1Sha384 | Self::RsaPssSha384 => HashAlg::Sha384,
            // Ed25519 hashes internally with SHA-512; this value is unused for it.
            Self::Ed25519 => HashAlg::Sha384,
        }
    }
}

// ---------------------------------------------------------------------------
// Verification dispatch
// ---------------------------------------------------------------------------

fn ecdsa_verify_parts(
    key: &SubjectPublicKey,
    alg: SignatureAlgorithm,
    msg: &[u8],
    r: &[u8],
    s: &[u8],
) -> Result<(), CryptoError> {
    match (key, alg) {
        (SubjectPublicKey::P256(pk), SignatureAlgorithm::EcdsaP256Sha256) => {
            let c = p256();
            c.verify(&c.decode_sec1(pk)?, &sha256(msg), r, s)
        }
        (SubjectPublicKey::P384(pk), SignatureAlgorithm::EcdsaP384Sha384) => {
            let c = p384();
            c.verify(&c.decode_sec1(pk)?, &sha384(msg), r, s)
        }
        _ => Err(CryptoError::KeyAlgorithmMismatch),
    }
}

/// Verify `sig` over `msg` under `key` with `alg`. ECDSA signatures are DER `Ecdsa-Sig-Value`;
/// RSA signatures are exactly `k` bytes; Ed25519 signatures are 64 bytes (`verify_strict`).
pub fn verify_signature(
    key: &SubjectPublicKey,
    alg: SignatureAlgorithm,
    msg: &[u8],
    sig: &[u8],
) -> Result<(), CryptoError> {
    use SignatureAlgorithm as A;
    match (key, alg) {
        (SubjectPublicKey::P256(_), A::EcdsaP256Sha256)
        | (SubjectPublicKey::P384(_), A::EcdsaP384Sha384) => {
            let (r, s) = parse_ecdsa_der(sig)?;
            ecdsa_verify_parts(key, alg, msg, &r, &s)
        }
        (SubjectPublicKey::Rsa { n, e }, A::RsaPkcs1Sha256 | A::RsaPkcs1Sha384) => {
            rsa::verify_pkcs1v15(n, e, alg.hash(), msg, sig)
        }
        (SubjectPublicKey::Rsa { n, e }, A::RsaPssSha256 | A::RsaPssSha384) => {
            rsa::verify_pss(n, e, alg.hash(), msg, sig, alg.hash().output_len())
        }
        (SubjectPublicKey::Ed25519(pk), A::Ed25519) => {
            let sig: &[u8; 64] = sig
                .try_into()
                .map_err(|_| CryptoError::BadSignatureLength)?;
            if ed25519::verify_strict(pk, msg, sig) {
                Ok(())
            } else {
                Err(CryptoError::SignatureMismatch)
            }
        }
        _ => Err(CryptoError::KeyAlgorithmMismatch),
    }
}

/// Verify a fixed-width big-endian `r ‖ s` ECDSA signature (COSE, SPDM, TDX, SEV-SNP layouts).
pub fn verify_ecdsa_raw(
    key: &SubjectPublicKey,
    alg: SignatureAlgorithm,
    msg: &[u8],
    r_s: &[u8],
) -> Result<(), CryptoError> {
    let len = match alg {
        SignatureAlgorithm::EcdsaP256Sha256 => 32,
        SignatureAlgorithm::EcdsaP384Sha384 => 48,
        _ => return Err(CryptoError::KeyAlgorithmMismatch),
    };
    if r_s.len() != 2 * len {
        return Err(CryptoError::BadSignatureLength);
    }
    ecdsa_verify_parts(key, alg, msg, &r_s[..len], &r_s[len..])
}

// ---------------------------------------------------------------------------
// Deterministic fixture signer (tests / conformance fixtures only)
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum FixtureKey {
    P256(Limbs<4>),
    P384(Limbs<6>),
    Ed25519([u8; 32]),
    Rsa(&'static rsa::FixtureRsaKey),
}

/// Deterministic signer for conformance fixtures. **Variable-time; never use with real keys.**
#[derive(Clone)]
pub struct FixtureSigner {
    key: FixtureKey,
}

impl FixtureSigner {
    pub fn p256(seed: &[u8]) -> Self {
        Self {
            key: FixtureKey::P256(p256().fixture_scalar(seed)),
        }
    }

    pub fn p384(seed: &[u8]) -> Self {
        Self {
            key: FixtureKey::P384(p384().fixture_scalar(seed)),
        }
    }

    /// Fixture from an explicit P-256 private scalar (KAT reproduction); `None` if out of range.
    pub fn p256_from_scalar(d_be: &[u8]) -> Option<Self> {
        Some(Self {
            key: FixtureKey::P256(p256().scalar(d_be).ok()?),
        })
    }

    /// Fixture from an explicit P-384 private scalar (KAT reproduction); `None` if out of range.
    pub fn p384_from_scalar(d_be: &[u8]) -> Option<Self> {
        Some(Self {
            key: FixtureKey::P384(p384().scalar(d_be).ok()?),
        })
    }

    pub fn ed25519(seed: &[u8]) -> Self {
        let mut pre = b"OBEND.FIXTURE.ED25519/v1".to_vec();
        pre.extend_from_slice(seed);
        Self {
            key: FixtureKey::Ed25519(sha256(&pre)),
        }
    }

    /// Embedded RSA fixture key (`e = 65537`); `bits` must be 2048, 3072 or 4096.
    pub fn rsa(bits: usize) -> Self {
        Self {
            key: FixtureKey::Rsa(rsa::fixture_key(bits).expect("fixture RSA size 2048/3072/4096")),
        }
    }

    pub fn public_key(&self) -> SubjectPublicKey {
        match &self.key {
            FixtureKey::P256(d) => {
                let c = p256();
                let mut out = [0u8; 65];
                out.copy_from_slice(&c.encode_sec1(&c.mul(&c.g, d)));
                SubjectPublicKey::P256(out)
            }
            FixtureKey::P384(d) => {
                let c = p384();
                let mut out = [0u8; 97];
                out.copy_from_slice(&c.encode_sec1(&c.mul(&c.g, d)));
                SubjectPublicKey::P384(out)
            }
            FixtureKey::Ed25519(seed) => {
                SubjectPublicKey::Ed25519(ed25519::fixture_public_key(seed))
            }
            FixtureKey::Rsa(k) => SubjectPublicKey::Rsa {
                n: k.n(),
                e: vec![0x01, 0x00, 0x01],
            },
        }
    }

    /// Fixed-width `r ‖ s` ECDSA signature. Panics if the key is not ECDSA for `alg`.
    pub fn sign_ecdsa_raw(&self, alg: SignatureAlgorithm, msg: &[u8]) -> Vec<u8> {
        let (r, s) = match (&self.key, alg) {
            (FixtureKey::P256(d), SignatureAlgorithm::EcdsaP256Sha256) => {
                p256().sign(d, &sha256(msg))
            }
            (FixtureKey::P384(d), SignatureAlgorithm::EcdsaP384Sha384) => {
                p384().sign(d, &sha384(msg))
            }
            _ => panic!("FixtureSigner::sign_ecdsa_raw: key/algorithm mismatch"),
        };
        [r, s].concat()
    }

    /// Signature in the encoding [`verify_signature`] expects. Panics on key/algorithm mismatch.
    pub fn sign(&self, alg: SignatureAlgorithm, msg: &[u8]) -> Vec<u8> {
        use SignatureAlgorithm as A;
        match (&self.key, alg) {
            (FixtureKey::P256(_), A::EcdsaP256Sha256)
            | (FixtureKey::P384(_), A::EcdsaP384Sha384) => {
                let raw = self.sign_ecdsa_raw(alg, msg);
                let (r, s) = raw.split_at(raw.len() / 2);
                encode_ecdsa_der(r, s)
            }
            (FixtureKey::Ed25519(seed), A::Ed25519) => ed25519::fixture_sign(seed, msg).to_vec(),
            (FixtureKey::Rsa(k), A::RsaPkcs1Sha256 | A::RsaPkcs1Sha384) => {
                rsa::fixture_sign_pkcs1v15(k, alg.hash(), msg)
            }
            (FixtureKey::Rsa(k), A::RsaPssSha256 | A::RsaPssSha384) => {
                rsa::fixture_sign_pss(k, alg.hash(), msg)
            }
            _ => panic!("FixtureSigner::sign: key/algorithm mismatch"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn generators_on_curve_and_order_n() {
        let c = p256();
        assert!(c.on_curve(&c.g.x, &c.g.y));
        assert!(c.is_inf(&c.mul(&c.g, &c.n)));
        let c = p384();
        assert!(c.on_curve(&c.g.x, &c.g.y));
        assert!(c.is_inf(&c.mul(&c.g, &c.n)));
    }

    /// RFC 6979 §A.2.5 (P-256, SHA-256, "sample") and §A.2.6 (P-384, SHA-384, "sample"),
    /// reproduced independently with pyca/cryptography 50.0.2 `deterministic_signing=True`.
    #[test]
    fn rfc6979_known_answers() {
        let s = FixtureSigner::p256_from_scalar(&h(
            "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
        ))
        .unwrap();
        let SubjectPublicKey::P256(pk) = s.public_key() else {
            panic!()
        };
        assert_eq!(
            pk.to_vec(),
            h("0460fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299")
        );
        let sig = s.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP256Sha256, b"sample");
        assert_eq!(sig, h("efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8"));
        assert!(verify_ecdsa_raw(
            &s.public_key(),
            SignatureAlgorithm::EcdsaP256Sha256,
            b"sample",
            &sig
        )
        .is_ok());

        let s = FixtureSigner::p384_from_scalar(&h(
            "6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d896d5724e4c70a825f872c9ea60d2edf5",
        ))
        .unwrap();
        let sig = s.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP384Sha384, b"sample");
        assert_eq!(sig, h("94edbb92a5ecb8aad4736e56c691916b3f88140666ce9fa73d64c4ea95ad133c81a648152e44acf96e36dd1e80fabe4699ef4aeb15f178cea1fe40db2603138f130e740a19624526203b6351d0a3a94fa329c145786e679e7b82c71a38628ac8"));
        assert!(verify_ecdsa_raw(
            &s.public_key(),
            SignatureAlgorithm::EcdsaP384Sha384,
            b"sample",
            &sig
        )
        .is_ok());
    }

    #[test]
    fn range_and_curve_refusals() {
        let s = FixtureSigner::p256(b"range");
        let pk = s.public_key();
        let msg = b"range-check";
        let raw = s.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP256Sha256, msg);
        assert!(verify_ecdsa_raw(&pk, SignatureAlgorithm::EcdsaP256Sha256, msg, &raw).is_ok());
        let n = h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        // r = 0, s = 0, s = n, r = n refused before any curve arithmetic.
        let zero = [0u8; 32];
        for (r, s_) in [
            (&zero[..], &raw[32..]),
            (&raw[..32], &zero[..]),
            (&raw[..32], &n[..]),
            (&n[..], &raw[32..]),
        ] {
            let sig = [r, s_].concat();
            assert_eq!(
                verify_ecdsa_raw(&pk, SignatureAlgorithm::EcdsaP256Sha256, msg, &sig),
                Err(CryptoError::ScalarOutOfRange)
            );
        }
        // Malleated s' = n - s is a valid ECDSA signature mathematically; we accept it (FIPS 186-5
        // has no low-s rule) but it must still verify only for the same message.
        // Off-curve point: flip one bit of Y.
        let SubjectPublicKey::P256(mut bad) = pk.clone() else {
            panic!()
        };
        bad[64] ^= 1;
        assert_eq!(
            SubjectPublicKey::from_spki_der(&SubjectPublicKey::P256(bad).to_spki_der()),
            Err(CryptoError::PointNotOnCurve)
        );
        assert!(verify_ecdsa_raw(
            &SubjectPublicKey::P256(bad),
            SignatureAlgorithm::EcdsaP256Sha256,
            msg,
            &raw
        )
        .is_err());
        // Key/algorithm confusion is refused.
        assert_eq!(
            verify_ecdsa_raw(&pk, SignatureAlgorithm::EcdsaP384Sha384, msg, &[0u8; 96]),
            Err(CryptoError::KeyAlgorithmMismatch)
        );
    }

    #[test]
    fn der_signature_strictness() {
        let s = FixtureSigner::p384(b"der");
        let msg = b"der-check";
        let der = s.sign(SignatureAlgorithm::EcdsaP384Sha384, msg);
        assert!(verify_signature(
            &s.public_key(),
            SignatureAlgorithm::EcdsaP384Sha384,
            msg,
            &der
        )
        .is_ok());
        let mut trailing = der.clone();
        trailing.push(0);
        assert!(verify_signature(
            &s.public_key(),
            SignatureAlgorithm::EcdsaP384Sha384,
            msg,
            &trailing
        )
        .is_err());
        // Non-minimal INTEGER (extra leading zero) is refused.
        let (r, sv) = parse_ecdsa_der(&der).unwrap();
        let mut body = der_encode(0x02, &[&[0u8, 0u8][..], &r].concat());
        body.extend_from_slice(&der_encode_uint(&sv));
        let bad = der_encode(0x30, &body);
        assert!(verify_signature(
            &s.public_key(),
            SignatureAlgorithm::EcdsaP384Sha384,
            msg,
            &bad
        )
        .is_err());
    }

    #[test]
    fn spki_and_algid_roundtrip() {
        for s in [
            FixtureSigner::p256(b"a"),
            FixtureSigner::p384(b"b"),
            FixtureSigner::ed25519(b"c"),
            FixtureSigner::rsa(2048),
        ] {
            let pk = s.public_key();
            assert_eq!(
                SubjectPublicKey::from_spki_der(&pk.to_spki_der()).unwrap(),
                pk
            );
        }
        for (a, _) in SignatureAlgorithm::ALL {
            assert_eq!(
                SignatureAlgorithm::from_algorithm_identifier_der(&a.algorithm_identifier_der())
                    .unwrap(),
                a
            );
        }
    }
}
