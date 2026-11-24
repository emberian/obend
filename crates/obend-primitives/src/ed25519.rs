//! Pure-Rust RFC 8032 Ed25519 (`verify_strict` + deterministic fixture signing) over the generic
//! [`crate::bigint::Mont`] engine and [`crate::sha512`] (zero external crates).
//!
//! `verify_strict` matches the `ed25519-dalek` strict policy:
//! 1. `S` must be canonical (`S < ℓ`);
//! 2. `A` and `R` are decoded strictly (RFC 8032 §5.1.3: `y < p`, on-curve, no negative zero);
//! 3. small-order `A` or `R` (`[8]P = O`) is refused;
//! 4. the cofactorless equation `[S]B = R + [k]A` must hold, `k = SHA-512(R ‖ A ‖ M) mod ℓ`.
//!
//! The curve constants `d` and `sqrt(-1)` and the base point are derived from their RFC 8032 §5.1
//! definitions during constant evaluation, so nothing is initialised at run time.

use crate::bigint::{limbs_eq, limbs_from_be, limbs_from_hex, limbs_ge, Limbs, Mont};
use crate::sha512::{sha512, Sha512};

type Fe = Limbs<4>;

/// The base field, `p = 2^255 - 19`.
const F: Mont<4> =
    Mont::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");
/// The order of the base point, `ℓ = 2^252 + 27742317777372353535851937790883648493`.
const L_LIMBS: Fe =
    limbs_from_hex("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");
const L: Mont<4> = match Mont::new(L_LIMBS) {
    Some(l) => l,
    None => panic!("odd group order"),
};
/// `d = -121665 / 121666` (RFC 8032 §5.1).
const D: Fe = F.mul(&F.neg(&F.from_u64(121_665)), &F.inv(&F.from_u64(121_666)));
const D2: Fe = F.double(&D);
/// `sqrt(-1) = 2^((p-1)/4)`, `(p-1)/4 = 2^253 - 5`.
const SQRT_M1: Fe = F.pow_limbs(
    &F.from_u64(2),
    &limbs_from_hex::<4>("1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"),
);
/// `(p-5)/8 = 2^252 - 3`.
const P58: Fe = limbs_from_hex("0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd");
/// `B` has `y = 4/5` and even `x` (sign bit 0).
const BASE: Point = {
    let y = F.mul(&F.from_u64(4), &F.inv(&F.from_u64(5)));
    match recover_x(&y, 0) {
        Some(x) => Point::affine(x, y),
        None => panic!("canonical Ed25519 basepoint"),
    }
};

/// Extended twisted Edwards coordinates `(X : Y : Z : T)`, `x = X/Z`, `y = Y/Z`, `xy = T/Z`.
#[derive(Clone, Copy, Debug)]
struct Point {
    x: Fe,
    y: Fe,
    z: Fe,
    t: Fe,
}

impl Point {
    const IDENTITY: Self = Self {
        x: F.zero(),
        y: F.one(),
        z: F.one(),
        t: F.zero(),
    };

    const fn affine(x: Fe, y: Fe) -> Self {
        Self {
            x,
            y,
            z: F.one(),
            t: F.mul(&x, &y),
        }
    }

    /// Unified extended-coordinates addition for `a = -1` (Hisil–Wong–Carter–Dawson 2008).
    fn add(&self, o: &Self) -> Self {
        let a = F.mul(&F.sub(&self.y, &self.x), &F.sub(&o.y, &o.x));
        let b = F.mul(&F.add(&self.y, &self.x), &F.add(&o.y, &o.x));
        let c = F.mul(&F.mul(&self.t, &D2), &o.t);
        let d = F.double(&F.mul(&self.z, &o.z));
        let e = F.sub(&b, &a);
        let f = F.sub(&d, &c);
        let g = F.add(&d, &c);
        let h = F.add(&b, &a);
        Self {
            x: F.mul(&e, &f),
            y: F.mul(&g, &h),
            t: F.mul(&e, &h),
            z: F.mul(&f, &g),
        }
    }

    /// Variable-time double-and-add with a big-endian scalar.
    fn mul_be(&self, scalar_be: &[u8]) -> Self {
        let mut acc = Self::IDENTITY;
        for &byte in scalar_be {
            for bit in (0..8).rev() {
                acc = acc.add(&acc);
                if (byte >> bit) & 1 == 1 {
                    acc = acc.add(self);
                }
            }
        }
        acc
    }

    fn eq_proj(&self, o: &Self) -> bool {
        F.mul(&self.x, &o.z) == F.mul(&o.x, &self.z) && F.mul(&self.y, &o.z) == F.mul(&o.y, &self.z)
    }

    fn is_small_order(&self) -> bool {
        let p2 = self.add(self);
        let p4 = p2.add(&p2);
        let p8 = p4.add(&p4);
        p8.eq_proj(&Self::IDENTITY)
    }

    fn encode(&self) -> [u8; 32] {
        let zi = F.inv(&self.z);
        let x = F.mul(&self.x, &zi);
        let y = F.mul(&self.y, &zi);
        let mut out = le_bytes(&y);
        out[31] |= (le_bytes(&x)[0] & 1) << 7;
        out
    }
}

/// Canonical little-endian encoding of a field element in Montgomery form.
fn le_bytes(a: &Fe) -> [u8; 32] {
    let mut out = [0u8; 32];
    F.to_be_into(a, &mut out);
    out.reverse();
    out
}

/// Canonical big-endian encoding of a scalar in Montgomery form modulo `ℓ`.
fn scalar_be(s: &Fe) -> [u8; 32] {
    let mut out = [0u8; 32];
    L.to_be_into(s, &mut out);
    out
}

/// The `x` with sign bit `sign` on the curve at `y` (RFC 8032 §5.1.3 steps 2-4), if any.
const fn recover_x(y: &Fe, sign: u8) -> Option<Fe> {
    let y2 = F.square(y);
    let u = F.sub(&y2, &F.one());
    let v = F.add(&F.mul(&D, &y2), &F.one());
    let v3 = F.mul(&F.square(&v), &v);
    let v7 = F.mul(&F.square(&v3), &v);
    let mut x = F.mul(&F.mul(&u, &v3), &F.pow_limbs(&F.mul(&u, &v7), &P58));
    let vx2 = F.mul(&v, &F.square(&x));
    if !limbs_eq(&vx2, &u) {
        if limbs_eq(&vx2, &F.neg(&u)) {
            x = F.mul(&x, &SQRT_M1);
        } else {
            return None;
        }
    }
    if F.is_zero(&x) && sign == 1 {
        return None;
    }
    if (F.from_mont(&x)[0] & 1) as u8 != sign {
        x = F.neg(&x);
    }
    Some(x)
}

/// Strict RFC 8032 §5.1.3 decoding.
fn decode(bytes: &[u8; 32]) -> Option<Point> {
    let sign = bytes[31] >> 7;
    let mut y_be = *bytes;
    y_be[31] &= 0x7f;
    y_be.reverse();
    let y = F.from_be_strict(&y_be)?;
    Some(Point::affine(recover_x(&y, sign)?, y))
}

/// `SHA-512(parts...) mod ℓ`, interpreted little-endian (RFC 8032 §5.1.6/§5.1.7). Montgomery form.
fn hash_mod_l(parts: &[&[u8]]) -> Fe {
    let mut h = Sha512::new();
    for p in parts {
        h.update(p);
    }
    let mut digest = h.finalize();
    digest.reverse();
    L.from_be_reduce(&digest)
}

/// Validate that `public_key` is a canonical RFC 8032 §5.1.3 point encoding AND is not in the
/// 8-torsion small-order subgroup (`[8]A != O`).
pub fn validate_public_key(public_key: &[u8; 32]) -> bool {
    decode(public_key).is_some_and(|a| !a.is_small_order())
}

/// Strict Ed25519 verification (see module docs). Returns `true` iff the signature is valid.
pub fn verify_strict(public_key: &[u8; 32], msg: &[u8], signature: &[u8; 64]) -> bool {
    let mut r_bytes = [0u8; 32];
    r_bytes.copy_from_slice(&signature[..32]);
    let mut s_be = [0u8; 32];
    s_be.copy_from_slice(&signature[32..]);
    s_be.reverse();
    let Some(s_limbs) = limbs_from_be::<4>(&s_be) else {
        return false;
    };
    if limbs_ge(&s_limbs, &L_LIMBS) {
        return false;
    }
    let Some(a) = decode(public_key) else {
        return false;
    };
    let Some(r) = decode(&r_bytes) else {
        return false;
    };
    if a.is_small_order() || r.is_small_order() {
        return false;
    }
    let k = hash_mod_l(&[&r_bytes, public_key, msg]);
    let sb = BASE.mul_be(&s_be);
    let rhs = r.add(&a.mul_be(&scalar_be(&k)));
    sb.eq_proj(&rhs)
}

/// The clamped secret scalar `a`, big-endian, and the nonce prefix of a 32-byte seed.
fn expand_seed(seed: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
    let d = sha512(seed);
    let mut a = [0u8; 32];
    a.copy_from_slice(&d[..32]);
    a[0] &= 248;
    a[31] &= 127;
    a[31] |= 64;
    a.reverse();
    let mut prefix = [0u8; 32];
    prefix.copy_from_slice(&d[32..]);
    (a, prefix)
}

/// RFC 8032 public key for a 32-byte seed. Fixture/KAT use: variable-time.
pub fn fixture_public_key(seed: &[u8; 32]) -> [u8; 32] {
    let (a_be, _) = expand_seed(seed);
    BASE.mul_be(&a_be).encode()
}

/// RFC 8032 deterministic signature. Fixture/KAT use only: variable-time, not side-channel safe.
pub fn fixture_sign(seed: &[u8; 32], msg: &[u8]) -> [u8; 64] {
    let (a_be, prefix) = expand_seed(seed);
    let pk = BASE.mul_be(&a_be).encode();
    let r = hash_mod_l(&[&prefix, msg]);
    let r_point = BASE.mul_be(&scalar_be(&r)).encode();
    let k = hash_mod_l(&[&r_point, &pk, msg]);
    let a = L.from_be_reduce(&a_be);
    let mut s_le = scalar_be(&L.add(&r, &L.mul(&k, &a)));
    s_le.reverse();
    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_point);
    sig[32..].copy_from_slice(&s_le);
    sig
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec::Vec;

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

    /// The constant-evaluated values against the RFC 8032 §5.1 literals (Python cross-check).
    #[test]
    fn derived_constants_match_rfc_8032() {
        let canon = |hex: &str| limbs_from_hex::<4>(hex);
        assert_eq!(
            F.from_mont(&D),
            canon("52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3")
        );
        assert_eq!(
            F.from_mont(&SQRT_M1),
            canon("2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0")
        );
        assert_eq!(F.square(&SQRT_M1), F.neg(&F.one()));
        assert_eq!(
            F.from_mont(&BASE.x),
            canon("216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a")
        );
        assert_eq!(
            F.from_mont(&BASE.y),
            canon("6666666666666666666666666666666666666666666666666666666666666658")
        );
        assert_eq!(
            BASE.encode().to_vec(),
            h("5866666666666666666666666666666666666666666666666666666666666666")
        );
        assert_eq!(L, Mont::<4>::new(L_LIMBS).unwrap());
    }

    #[test]
    fn rfc8032_known_answers_sign_and_verify() {
        for (seed, pk, msg, sig) in KATS {
            let seed = a32(&h(seed));
            let pk = a32(&h(pk));
            let sig = a64(&h(sig));
            let msg = h(msg);
            assert_eq!(fixture_public_key(&seed), pk);
            assert!(validate_public_key(&pk));
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
        let (_, pk, _, sig) = KATS[0];
        let pk = a32(&h(pk));
        let sig = a64(&h(sig));
        // Non-canonical S + ℓ (malleability) is refused.
        let mut l_le = h("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");
        l_le.reverse();
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
        assert!(!validate_public_key(&ident));
        // Non-canonical y >= p encoding of the public key is refused.
        let mut noncanon = [0xffu8; 32];
        noncanon[0] = 0xee; // p + 1 = 2^255 - 18
        noncanon[31] = 0x7f;
        assert!(!verify_strict(&noncanon, b"", &sig));
        assert!(!validate_public_key(&noncanon));
        // x = 0 with the sign bit set ("negative zero", y = 1 with bit 255) is refused.
        let mut neg_zero = ident;
        neg_zero[31] |= 0x80;
        assert!(!validate_public_key(&neg_zero));
    }
}
