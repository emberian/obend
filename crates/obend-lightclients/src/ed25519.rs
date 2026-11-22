//! Pure-Rust RFC 8032 Ed25519 (`verify_strict` + deterministic fixture signing) over the generic
//! [`crate::bigint::Mont`] engine and in-crate FIPS 180-4 SHA-512 (zero external crates).
//!
//! `verify_strict` matches the `ed25519-dalek` strict policy:
//! 1. `S` must be canonical (`S < ℓ`);
//! 2. `A` and `R` are decoded strictly (RFC 8032 §5.1.3: `y < p`, on-curve, no negative zero);
//! 3. small-order `A` or `R` (`[8]P = O`) is refused;
//! 4. the cofactorless equation `[S]B = R + [k]A` must hold, `k = SHA-512(R ‖ A ‖ M) mod ℓ`.

use std::sync::OnceLock;

use crate::bigint::{limbs_from_be, limbs_ge, limbs_from_hex, Limbs, Mont};
use crate::sha512::Sha512;

type Fe = Limbs<4>;

struct Ctx {
    f: Mont<4>,
    l: Mont<4>,
    l_limbs: Fe,
    d: Fe,
    d2: Fe,
    sqrt_m1: Fe,
    p58: Fe,
    base: Point,
}

#[derive(Clone, Copy, Debug)]
struct Point {
    x: Fe,
    y: Fe,
    z: Fe,
    t: Fe,
}

fn ctx() -> &'static Ctx {
    static CTX: OnceLock<Ctx> = OnceLock::new();
    CTX.get_or_init(|| {
        let f = Mont::<4>::from_hex(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed",
        );
        let l_limbs =
            limbs_from_hex::<4>("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");
        let l = Mont::<4>::new(l_limbs).expect("odd group order");
        // d = -121665 / 121666 (RFC 8032 §5.1).
        let d = f.mul(&f.neg(&f.from_u64(121_665)), &f.inv(&f.from_u64(121_666)));
        let d2 = f.double(&d);
        // sqrt(-1) = 2^((p-1)/4), (p-1)/4 = 2^253 - 5.
        let e14 = limbs_from_hex::<4>(
            "1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb",
        );
        let sqrt_m1 = f.pow_limbs(&f.from_u64(2), &e14);
        // (p-5)/8 = 2^252 - 3.
        let p58 = limbs_from_hex::<4>(
            "0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd",
        );
        let mut c = Ctx {
            f,
            l,
            l_limbs,
            d,
            d2,
            sqrt_m1,
            p58,
            base: Point {
                x: [0; 4],
                y: [0; 4],
                z: [0; 4],
                t: [0; 4],
            },
        };
        // B has y = 4/5 and even x (sign bit 0).
        let y = f.mul(&f.from_u64(4), &f.inv(&f.from_u64(5)));
        let mut enc = le_bytes(&f, &y);
        enc[31] &= 0x7f;
        c.base = decode_with(&c, &enc).expect("canonical Ed25519 basepoint");
        c
    })
}

fn le_bytes(f: &Mont<4>, a: &Fe) -> [u8; 32] {
    let be = f.to_be(a, 32);
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = be[31 - i];
    }
    out
}

fn reversed(b: &[u8]) -> Vec<u8> {
    b.iter().rev().copied().collect()
}

impl Point {
    fn identity(f: &Mont<4>) -> Self {
        Self {
            x: f.zero(),
            y: f.one(),
            z: f.one(),
            t: f.zero(),
        }
    }

    /// Unified extended-coordinates addition for `a = -1` (Hisil–Wong–Carter–Dawson 2008).
    fn add(&self, o: &Self, c: &Ctx) -> Self {
        let f = &c.f;
        let a = f.mul(&f.sub(&self.y, &self.x), &f.sub(&o.y, &o.x));
        let b = f.mul(&f.add(&self.y, &self.x), &f.add(&o.y, &o.x));
        let cc = f.mul(&f.mul(&self.t, &c.d2), &o.t);
        let dd = f.double(&f.mul(&self.z, &o.z));
        let e = f.sub(&b, &a);
        let ff = f.sub(&dd, &cc);
        let g = f.add(&dd, &cc);
        let h = f.add(&b, &a);
        Self {
            x: f.mul(&e, &ff),
            y: f.mul(&g, &h),
            t: f.mul(&e, &h),
            z: f.mul(&ff, &g),
        }
    }

    /// Variable-time double-and-add with a big-endian scalar.
    fn mul_be(&self, scalar_be: &[u8], c: &Ctx) -> Self {
        let mut acc = Self::identity(&c.f);
        for &byte in scalar_be {
            for bit in (0..8).rev() {
                acc = acc.add(&acc, c);
                if (byte >> bit) & 1 == 1 {
                    acc = acc.add(self, c);
                }
            }
        }
        acc
    }

    fn eq_proj(&self, o: &Self, f: &Mont<4>) -> bool {
        f.mul(&self.x, &o.z) == f.mul(&o.x, &self.z) && f.mul(&self.y, &o.z) == f.mul(&o.y, &self.z)
    }

    fn is_small_order(&self, c: &Ctx) -> bool {
        let p2 = self.add(self, c);
        let p4 = p2.add(&p2, c);
        let p8 = p4.add(&p4, c);
        p8.eq_proj(&Self::identity(&c.f), &c.f)
    }

    fn encode(&self, f: &Mont<4>) -> [u8; 32] {
        let zi = f.inv(&self.z);
        let x = f.mul(&self.x, &zi);
        let y = f.mul(&self.y, &zi);
        let mut out = le_bytes(f, &y);
        out[31] |= (le_bytes(f, &x)[0] & 1) << 7;
        out
    }
}

/// Strict RFC 8032 §5.1.3 decoding.
fn decode_with(c: &Ctx, bytes: &[u8; 32]) -> Option<Point> {
    let f = &c.f;
    let sign = bytes[31] >> 7;
    let mut yb = *bytes;
    yb[31] &= 0x7f;
    let y = f.from_be_strict(&reversed(&yb))?;
    let y2 = f.square(&y);
    let u = f.sub(&y2, &f.one());
    let v = f.add(&f.mul(&c.d, &y2), &f.one());
    let v3 = f.mul(&f.square(&v), &v);
    let v7 = f.mul(&f.square(&v3), &v);
    let mut x = f.mul(&f.mul(&u, &v3), &f.pow_limbs(&f.mul(&u, &v7), &c.p58));
    let vx2 = f.mul(&v, &f.square(&x));
    if vx2 == u {
    } else if vx2 == f.neg(&u) {
        x = f.mul(&x, &c.sqrt_m1);
    } else {
        return None;
    }
    if f.is_zero(&x) && sign == 1 {
        return None;
    }
    if (le_bytes(f, &x)[0] & 1) != sign {
        x = f.neg(&x);
    }
    Some(Point {
        x,
        y,
        z: f.one(),
        t: f.mul(&x, &y),
    })
}

/// `SHA-512(parts...) mod ℓ`, interpreted little-endian (RFC 8032 §5.1.6/§5.1.7). Montgomery form.
fn hash_mod_l(c: &Ctx, parts: &[&[u8]]) -> Fe {
    let mut h = Sha512::new();
    for p in parts {
        h.update(p);
    }
    let digest = h.finalize_vec();
    c.l.from_be_reduce(&reversed(&digest))
}

/// Validate that `public_key` is a canonical RFC 8032 §5.1.3 point encoding AND is not in the
/// 8-torsion small-order subgroup (`[8]A != O`).
pub fn validate_public_key(public_key: &[u8; 32]) -> bool {
    let c = ctx();
    decode_with(c, public_key).is_some_and(|a| !a.is_small_order(c))
}

/// Strict Ed25519 verification (see module docs). Returns `true` iff the signature is valid.
pub fn verify_strict(public_key: &[u8; 32], msg: &[u8], signature: &[u8; 64]) -> bool {
    let c = ctx();
    let mut r_bytes = [0u8; 32];
    r_bytes.copy_from_slice(&signature[..32]);
    let s_be = reversed(&signature[32..]);
    let Some(s_limbs) = limbs_from_be::<4>(&s_be) else {
        return false;
    };
    if limbs_ge(&s_limbs, &c.l_limbs) {
        return false;
    }
    let Some(a) = decode_with(c, public_key) else {
        return false;
    };
    let Some(r) = decode_with(c, &r_bytes) else {
        return false;
    };
    if a.is_small_order(c) || r.is_small_order(c) {
        return false;
    }
    let k = hash_mod_l(c, &[&r_bytes, public_key, msg]);
    let k_be = c.l.to_be(&k, 32);
    let sb = c.base.mul_be(&s_be, c);
    let rhs = r.add(&a.mul_be(&k_be, c), c);
    sb.eq_proj(&rhs, &c.f)
}

fn expand_seed(seed: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
    let mut h = Sha512::new();
    h.update(seed);
    let d = h.finalize_vec();
    let mut a = [0u8; 32];
    a.copy_from_slice(&d[..32]);
    a[0] &= 248;
    a[31] &= 127;
    a[31] |= 64;
    let mut prefix = [0u8; 32];
    prefix.copy_from_slice(&d[32..]);
    (a, prefix)
}

/// RFC 8032 public key for a 32-byte seed. Fixture/KAT use: variable-time.
pub fn fixture_public_key(seed: &[u8; 32]) -> [u8; 32] {
    let c = ctx();
    let (a, _) = expand_seed(seed);
    c.base.mul_be(&reversed(&a), c).encode(&c.f)
}

/// RFC 8032 deterministic signature. Fixture/KAT use only: variable-time, not side-channel safe.
pub fn fixture_sign(seed: &[u8; 32], msg: &[u8]) -> [u8; 64] {
    let c = ctx();
    let (a, prefix) = expand_seed(seed);
    let a_be = reversed(&a);
    let pk = c.base.mul_be(&a_be, c).encode(&c.f);
    let r = hash_mod_l(c, &[&prefix, msg]);
    let r_point = c.base.mul_be(&c.l.to_be(&r, 32), c).encode(&c.f);
    let k = hash_mod_l(c, &[&r_point, &pk, msg]);
    let a_m = c.l.from_be_reduce(&a_be);
    let s = c.l.add(&r, &c.l.mul(&k, &a_m));
    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_point);
    sig[32..].copy_from_slice(&reversed(&c.l.to_be(&s, 32)));
    sig
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
    fn a32(v: &[u8]) -> [u8; 32] {
        v.try_into().unwrap()
    }
    fn a64(v: &[u8]) -> [u8; 64] {
        v.try_into().unwrap()
    }

    /// RFC 8032 §7.1 TEST 1..3 (cross-checked with pyca/cryptography 50.0.2).
    const KATS: [(&str, &str, &str, &str); 3] = [
        ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60", "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a", "", "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
        ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb", "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c", "72", "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"),
        ("c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7", "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025", "af82", "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"),
    ];

    #[test]
    fn rfc8032_known_answers_sign_and_verify() {
        for (seed, pk, msg, sig) in KATS {
            let seed = a32(&h(seed));
            let pk = a32(&h(pk));
            let sig = a64(&h(sig));
            let msg = h(msg);
            assert_eq!(fixture_public_key(&seed), pk);
            assert_eq!(fixture_sign(&seed, &msg), sig);
            assert!(verify_strict(&pk, &msg, &sig));
            let mut bad = sig;
            bad[5] ^= 1;
            assert!(!verify_strict(&pk, &msg, &bad));
            let mut wrong_msg = msg.clone();
            wrong_msg.push(0);
            assert!(!verify_strict(&pk, &wrong_msg, &sig));
        }
    }

    #[test]
    fn strict_policy_refusals() {
        let (seed, pk, _, sig) = KATS[0];
        let pk = a32(&h(pk));
        let sig = a64(&h(sig));
        let _ = seed;
        // Non-canonical S + ℓ (malleability) is refused.
        let l_le = reversed(&h("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"));
        let mut s_plus_l = [0u8; 64];
        s_plus_l[..32].copy_from_slice(&sig[..32]);
        let mut carry = 0u16;
        for i in 0..32 {
            let v = u16::from(sig[32 + i]) + u16::from(l_le[i]) + carry;
            s_plus_l[32 + i] = v as u8;
            carry = v >> 8;
        }
        assert_eq!(carry, 0);
        assert!(!verify_strict(&pk, b"", &s_plus_l));
        // Small-order public key (identity, y = 1) with R = identity and S = 0 satisfies the
        // cofactorless equation for every message; verify_strict must refuse it.
        let mut ident = [0u8; 32];
        ident[0] = 1;
        let mut forged = [0u8; 64];
        forged[..32].copy_from_slice(&ident);
        assert!(!verify_strict(&ident, b"any message", &forged));
        // Non-canonical y >= p encoding of the public key is refused.
        let mut noncanon = [0xffu8; 32];
        noncanon[0] = 0xee; // p + 1 = 2^255 - 18
        noncanon[31] = 0x7f;
        assert!(!verify_strict(&noncanon, b"", &sig));
    }
}
