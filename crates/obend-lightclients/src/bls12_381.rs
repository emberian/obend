//! BLS12-381 in pure Rust over the crate's generic CIOS Montgomery engine ([`crate::bigint`]).
//!
//! * Tower: `Fp` (`Mont<6>`), `Fp2 = Fp[u]/(u^2 + 1)`, `Fp6 = Fp2[v]/(v^3 - (u + 1))`,
//!   `Fp12 = Fp6[w]/(w^2 - v)`.
//! * Curves: `E: y^2 = x^3 + 4` over `Fp` (G1) and the M-type sextic twist
//!   `E': y^2 = x^3 + 4(u + 1)` over `Fp2` (G2); Jacobian arithmetic for both.
//! * Encoding: ZCash compressed serialization (48 / 96 bytes; G2 is `x.c1 || x.c0`) with strict
//!   decoding (compression flag required, canonical infinity only, every coordinate `< p`) and a
//!   **mandatory** order-`r` subgroup check (`[r]P == O`) on every decoded point.
//! * Hashing: RFC 9380 `BLS12381G2_XMD:SHA-256_SSWU_RO_` (expand_message_xmd, hash_to_field with
//!   `m = 2, L = 64`, simplified SWU on the 3-isogenous `E2'`, the App. E.3 isogeny,
//!   `clear_cofactor` as scalar multiplication by `h_eff`).
//! * Pairing: optimal ate, Miller loop over `|x| = 0xd201000000010000` with affine lines of the
//!   untwisted point evaluated in `Fp12` (sign of `x` handled by conjugation), and the final
//!   exponentiation `f^((p^6 - 1) * ((p^6 + 1) / r))` = `f^((p^12 - 1) / r)`: the easy factor
//!   via conjugation and inversion, the rest by plain square-and-multiply. Correctness over speed.
//!
//! Verification paths handle public data only and the whole module is **variable time**. The
//! `fixture_*` signing helpers are deterministic test fixtures, NOT constant time, and must never
//! be used with real secret keys.

use crate::bigint::{
    limbs_add, limbs_bit, limbs_bits, limbs_from_hex, limbs_ge, limbs_is_zero, Limbs, Mont,
};
use std::sync::OnceLock;

/// Ethereum consensus proof-of-possession ciphersuite DST.
pub const DST_POP: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

const P_HEX: &str = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
const R_HEX: &str = "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001";
/// `|x|` for the BLS parameter `x = -0xd201000000010000`.
const X_ABS: u64 = 0xd201_0000_0001_0000;
/// RFC 9380 §8.8.2 `h_eff` for G2.
const H_EFF_HEX: &str = "bc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551";
/// `(p^6 + 1) / r` (exact; checked in tests: `(p^6 - 1) * E_HARD * r == p^12 - 1`).
const E_HARD_HEX: &str = "28b3148775037b6f235c55ca7566dbf85ae664cf5bb36579aea83c48c1dae0ec9031179bdeccad7375a3763bdf7ccf56fb1573beaa8c548ce0809bc5f61afb46e197bd2fa4899f0c50126c802eec85a2e707f08418554744497f8b2f2922967878febcb95d1f1304275ef499dffb12d6a874d21b73da2b822f514a9c4f6fee6a95db11e63f565e886c94c4f82384c3b5e2f557c0b15f27d7bd90935021c3f007c01e7ebe3afc816101ddd076117d1d615d49e2764d7bc3b5ef4b188a20b038ee1cd4778e0de7338259c22a12bd40224741b36fec77602d7271563890f1333a09c4497903f76e9cf0f70a61c791e209a5256de0381a168739e1cdc0705d6a";

const G1_X_HEX: &str = "17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
const G1_Y_HEX: &str = "08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
const G2_X0_HEX: &str = "024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8";
const G2_X1_HEX: &str = "13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e";
const G2_Y0_HEX: &str = "0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801";
const G2_Y1_HEX: &str = "0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be";

/// RFC 9380 App. E.3 3-isogeny constants `k_(i,j) = c0 + c1 * I` (extracted programmatically
/// from rfc9380.txt into `tests/vectors/bls/rfc9380_e3_iso3.txt`; equality checked in tests).
const ISO3: [(usize, usize, &str, &str); 13] = [
    (
        1,
        0,
        "05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6",
        "05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6",
    ),
    (
        1,
        1,
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a",
    ),
    (
        1,
        2,
        "11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e",
        "08ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d",
    ),
    (
        1,
        3,
        "171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        2,
        0,
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63",
    ),
    (
        2,
        1,
        "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c",
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f",
    ),
    (
        3,
        0,
        "1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706",
        "1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706",
    ),
    (
        3,
        1,
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be",
    ),
    (
        3,
        2,
        "11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c",
        "08ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f",
    ),
    (
        3,
        3,
        "124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        4,
        0,
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb",
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb",
    ),
    (
        4,
        1,
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3",
    ),
    (
        4,
        2,
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012",
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99",
    ),
];

// ---------------------------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------------------------

struct Ctx {
    fp: Mont<6>,
    fr: Mont<4>,
    r: Limbs<4>,
    p_plus1_div4: Limbs<6>,
    p_minus1_div2: Limbs<6>,
    h_eff: Limbs<10>,
    e_hard: Limbs<32>,
}

fn shr<const N: usize>(a: &Limbs<N>, k: u32) -> Limbs<N> {
    debug_assert!(k > 0 && k < 64);
    let mut o = [0u64; N];
    for i in 0..N {
        o[i] = a[i] >> k;
        if i + 1 < N {
            o[i] |= a[i + 1] << (64 - k);
        }
    }
    o
}

fn ctx() -> &'static Ctx {
    static C: OnceLock<Ctx> = OnceLock::new();
    C.get_or_init(|| {
        let fp = Mont::<6>::from_hex(P_HEX);
        let fr = Mont::<4>::from_hex(R_HEX);
        let p = *fp.modulus();
        let (pp1, carry) = limbs_add(&p, &[1, 0, 0, 0, 0, 0]);
        assert_eq!(carry, 0);
        Ctx {
            fp,
            fr,
            r: *fr.modulus(),
            p_plus1_div4: shr(&pp1, 2),
            p_minus1_div2: shr(&p, 1),
            h_eff: limbs_from_hex(H_EFF_HEX),
            e_hard: limbs_from_hex(E_HARD_HEX),
        }
    })
}

// ---------------------------------------------------------------------------------------------
// Fields
// ---------------------------------------------------------------------------------------------

trait Field: Copy + PartialEq + core::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn mul(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    /// Multiplicative inverse (`0 -> 0`).
    fn inv(&self) -> Self;
    fn is_zero(&self) -> bool;
    fn sqr(&self) -> Self {
        self.mul(self)
    }
    fn dbl(&self) -> Self {
        self.add(self)
    }
    fn pow<const M: usize>(&self, e: &Limbs<M>) -> Self {
        let mut acc = Self::one();
        for i in (0..limbs_bits(e)).rev() {
            acc = acc.sqr();
            if limbs_bit(e, i) {
                acc = acc.mul(self);
            }
        }
        acc
    }
}

/// `Fp` element in Montgomery form (always fully reduced, so derived equality is field equality).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fp(Limbs<6>);

impl Field for Fp {
    fn zero() -> Self {
        Fp([0; 6])
    }
    fn one() -> Self {
        Fp(ctx().fp.one())
    }
    fn add(&self, o: &Self) -> Self {
        Fp(ctx().fp.add(&self.0, &o.0))
    }
    fn sub(&self, o: &Self) -> Self {
        Fp(ctx().fp.sub(&self.0, &o.0))
    }
    fn mul(&self, o: &Self) -> Self {
        Fp(ctx().fp.mul(&self.0, &o.0))
    }
    fn neg(&self) -> Self {
        Fp(ctx().fp.neg(&self.0))
    }
    fn inv(&self) -> Self {
        Fp(ctx().fp.inv(&self.0))
    }
    fn is_zero(&self) -> bool {
        limbs_is_zero(&self.0)
    }
}

impl Fp {
    fn from_u64(v: u64) -> Self {
        Fp(ctx().fp.from_u64(v))
    }
    fn from_hex(h: &str) -> Self {
        let l = limbs_from_hex::<6>(h);
        assert!(
            !limbs_ge(&l, ctx().fp.modulus()),
            "Fp::from_hex: constant >= p"
        );
        Fp(ctx().fp.to_mont(&l))
    }
    fn canon(&self) -> Limbs<6> {
        ctx().fp.from_mont(&self.0)
    }
    fn from_be_strict(b: &[u8]) -> Option<Self> {
        ctx().fp.from_be_strict(b).map(Fp)
    }
    fn from_be_reduce(b: &[u8]) -> Self {
        Fp(ctx().fp.from_be_reduce(b))
    }
    fn to_be48(self) -> [u8; 48] {
        let v = ctx().fp.to_be(&self.0, 48);
        let mut o = [0u8; 48];
        o.copy_from_slice(&v);
        o
    }
    /// `p = 3 mod 4`: candidate `a^((p+1)/4)`, verified.
    fn sqrt(&self) -> Option<Self> {
        let s = self.pow(&ctx().p_plus1_div4);
        if s.sqr() == *self {
            Some(s)
        } else {
            None
        }
    }
    /// RFC 9380 `sgn0` (parity of the canonical integer).
    fn sgn0(&self) -> bool {
        self.canon()[0] & 1 == 1
    }
    /// ZCash "lexicographically largest": canonical value `> (p - 1) / 2`.
    fn lex_largest(&self) -> bool {
        let c = self.canon();
        c != ctx().p_minus1_div2 && limbs_ge(&c, &ctx().p_minus1_div2)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fp2 {
    c0: Fp,
    c1: Fp,
}

impl Field for Fp2 {
    fn zero() -> Self {
        Fp2::new(Fp::zero(), Fp::zero())
    }
    fn one() -> Self {
        Fp2::new(Fp::one(), Fp::zero())
    }
    fn add(&self, o: &Self) -> Self {
        Fp2::new(self.c0.add(&o.c0), self.c1.add(&o.c1))
    }
    fn sub(&self, o: &Self) -> Self {
        Fp2::new(self.c0.sub(&o.c0), self.c1.sub(&o.c1))
    }
    fn mul(&self, o: &Self) -> Self {
        let t0 = self.c0.mul(&o.c0);
        let t1 = self.c1.mul(&o.c1);
        let s = self.c0.add(&self.c1).mul(&o.c0.add(&o.c1));
        Fp2::new(t0.sub(&t1), s.sub(&t0).sub(&t1))
    }
    fn sqr(&self) -> Self {
        let a = self.c0.add(&self.c1).mul(&self.c0.sub(&self.c1));
        let b = self.c0.mul(&self.c1).dbl();
        Fp2::new(a, b)
    }
    fn neg(&self) -> Self {
        Fp2::new(self.c0.neg(), self.c1.neg())
    }
    fn inv(&self) -> Self {
        let t = self.c0.sqr().add(&self.c1.sqr()).inv();
        Fp2::new(self.c0.mul(&t), self.c1.mul(&t).neg())
    }
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
}

impl Fp2 {
    fn new(c0: Fp, c1: Fp) -> Self {
        Fp2 { c0, c1 }
    }
    fn from_u64(v: u64) -> Self {
        Fp2::new(Fp::from_u64(v), Fp::zero())
    }
    fn from_hex(h0: &str, h1: &str) -> Self {
        Fp2::new(Fp::from_hex(h0), Fp::from_hex(h1))
    }
    fn mul_fp(&self, s: &Fp) -> Self {
        Fp2::new(self.c0.mul(s), self.c1.mul(s))
    }
    /// Multiply by `xi = u + 1`.
    fn mul_xi(&self) -> Self {
        Fp2::new(self.c0.sub(&self.c1), self.c0.add(&self.c1))
    }
    /// Square root via the norm: `a` is a square iff `N(a) = c0^2 + c1^2` is a square in `Fp`.
    fn sqrt(&self) -> Option<Self> {
        if self.c1.is_zero() {
            if let Some(s) = self.c0.sqrt() {
                return Some(Fp2::new(s, Fp::zero()));
            }
            // -1 is a non-residue (p = 3 mod 4), so -c0 is a square and (s*u)^2 = -s^2 = c0.
            let s = self.c0.neg().sqrt()?;
            return Some(Fp2::new(Fp::zero(), s));
        }
        let s = self.c0.sqr().add(&self.c1.sqr()).sqrt()?;
        let half = Fp::from_u64(2).inv();
        let x0 = match self.c0.add(&s).mul(&half).sqrt() {
            Some(x) => x,
            None => self.c0.sub(&s).mul(&half).sqrt()?,
        };
        let r = Fp2::new(x0, self.c1.mul(&x0.dbl().inv()));
        if r.sqr() == *self {
            Some(r)
        } else {
            None
        }
    }
    /// RFC 9380 `sgn0` for `m = 2`.
    fn sgn0(&self) -> bool {
        self.c0.sgn0() || (self.c0.is_zero() && self.c1.sgn0())
    }
    /// ZCash ordering: compare `c1` first, `c0` when `c1 == 0`.
    fn lex_largest(&self) -> bool {
        if self.c1.is_zero() {
            self.c0.lex_largest()
        } else {
            self.c1.lex_largest()
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fp6 {
    c0: Fp2,
    c1: Fp2,
    c2: Fp2,
}

impl Field for Fp6 {
    fn zero() -> Self {
        Fp6 {
            c0: Fp2::zero(),
            c1: Fp2::zero(),
            c2: Fp2::zero(),
        }
    }
    fn one() -> Self {
        Fp6 {
            c0: Fp2::one(),
            c1: Fp2::zero(),
            c2: Fp2::zero(),
        }
    }
    fn add(&self, o: &Self) -> Self {
        Fp6 {
            c0: self.c0.add(&o.c0),
            c1: self.c1.add(&o.c1),
            c2: self.c2.add(&o.c2),
        }
    }
    fn sub(&self, o: &Self) -> Self {
        Fp6 {
            c0: self.c0.sub(&o.c0),
            c1: self.c1.sub(&o.c1),
            c2: self.c2.sub(&o.c2),
        }
    }
    fn mul(&self, o: &Self) -> Self {
        let (a0, a1, a2) = (&self.c0, &self.c1, &self.c2);
        let (b0, b1, b2) = (&o.c0, &o.c1, &o.c2);
        let t0 = a0.mul(b0);
        let t1 = a1.mul(b1);
        let t2 = a2.mul(b2);
        let c0 = a1
            .add(a2)
            .mul(&b1.add(b2))
            .sub(&t1)
            .sub(&t2)
            .mul_xi()
            .add(&t0);
        let c1 = a0
            .add(a1)
            .mul(&b0.add(b1))
            .sub(&t0)
            .sub(&t1)
            .add(&t2.mul_xi());
        let c2 = a0.add(a2).mul(&b0.add(b2)).sub(&t0).sub(&t2).add(&t1);
        Fp6 { c0, c1, c2 }
    }
    fn neg(&self) -> Self {
        Fp6 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
            c2: self.c2.neg(),
        }
    }
    fn inv(&self) -> Self {
        let (c0, c1, c2) = (&self.c0, &self.c1, &self.c2);
        let t0 = c0.sqr().sub(&c1.mul(c2).mul_xi());
        let t1 = c2.sqr().mul_xi().sub(&c0.mul(c1));
        let t2 = c1.sqr().sub(&c0.mul(c2));
        let d = c0
            .mul(&t0)
            .add(&c2.mul(&t1).add(&c1.mul(&t2)).mul_xi())
            .inv();
        Fp6 {
            c0: t0.mul(&d),
            c1: t1.mul(&d),
            c2: t2.mul(&d),
        }
    }
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }
}

impl Fp6 {
    /// Multiply by `v` (`v^3 = xi`).
    fn mul_by_v(&self) -> Self {
        Fp6 {
            c0: self.c2.mul_xi(),
            c1: self.c0,
            c2: self.c1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fp12 {
    c0: Fp6,
    c1: Fp6,
}

impl Field for Fp12 {
    fn zero() -> Self {
        Fp12 {
            c0: Fp6::zero(),
            c1: Fp6::zero(),
        }
    }
    fn one() -> Self {
        Fp12 {
            c0: Fp6::one(),
            c1: Fp6::zero(),
        }
    }
    fn add(&self, o: &Self) -> Self {
        Fp12 {
            c0: self.c0.add(&o.c0),
            c1: self.c1.add(&o.c1),
        }
    }
    fn sub(&self, o: &Self) -> Self {
        Fp12 {
            c0: self.c0.sub(&o.c0),
            c1: self.c1.sub(&o.c1),
        }
    }
    fn mul(&self, o: &Self) -> Self {
        let t0 = self.c0.mul(&o.c0);
        let t1 = self.c1.mul(&o.c1);
        let c1 = self
            .c0
            .add(&self.c1)
            .mul(&o.c0.add(&o.c1))
            .sub(&t0)
            .sub(&t1);
        Fp12 {
            c0: t0.add(&t1.mul_by_v()),
            c1,
        }
    }
    fn neg(&self) -> Self {
        Fp12 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }
    fn inv(&self) -> Self {
        let d = self.c0.sqr().sub(&self.c1.sqr().mul_by_v()).inv();
        Fp12 {
            c0: self.c0.mul(&d),
            c1: self.c1.mul(&d).neg(),
        }
    }
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
}

impl Fp12 {
    /// `f^(p^6)`: `w -> -w`.
    fn conj(&self) -> Self {
        Fp12 {
            c0: self.c0,
            c1: self.c1.neg(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Curves
// ---------------------------------------------------------------------------------------------

trait CurveField: Field {
    fn curve_b() -> Self;
}

impl CurveField for Fp {
    fn curve_b() -> Self {
        Fp::from_u64(4)
    }
}

impl CurveField for Fp2 {
    fn curve_b() -> Self {
        Fp2::new(Fp::from_u64(4), Fp::from_u64(4))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Aff<F> {
    x: F,
    y: F,
    inf: bool,
}

impl<F: CurveField> Aff<F> {
    fn identity() -> Self {
        Aff {
            x: F::zero(),
            y: F::zero(),
            inf: true,
        }
    }
    #[cfg(test)]
    fn on_curve(&self) -> bool {
        self.inf || self.y.sqr() == self.x.sqr().mul(&self.x).add(&F::curve_b())
    }
    fn neg(&self) -> Self {
        if self.inf {
            *self
        } else {
            Aff {
                x: self.x,
                y: self.y.neg(),
                inf: false,
            }
        }
    }
    fn to_jac(self) -> Jac<F> {
        if self.inf {
            Jac::identity()
        } else {
            Jac {
                x: self.x,
                y: self.y,
                z: F::one(),
            }
        }
    }
}

/// Jacobian `(X, Y, Z) ~ (X/Z^2, Y/Z^3)`; `Z = 0` is the point at infinity.
#[derive(Clone, Copy, Debug)]
struct Jac<F> {
    x: F,
    y: F,
    z: F,
}

impl<F: CurveField> Jac<F> {
    fn identity() -> Self {
        Jac {
            x: F::one(),
            y: F::one(),
            z: F::zero(),
        }
    }
    fn is_identity(&self) -> bool {
        self.z.is_zero()
    }
    fn to_affine(self) -> Aff<F> {
        if self.is_identity() {
            return Aff::identity();
        }
        let zi = self.z.inv();
        let zi2 = zi.sqr();
        Aff {
            x: self.x.mul(&zi2),
            y: self.y.mul(&zi2.mul(&zi)),
            inf: false,
        }
    }
    /// `dbl-2009-l` (a = 0).
    fn double(&self) -> Self {
        if self.is_identity() {
            return *self;
        }
        let a = self.x.sqr();
        let b = self.y.sqr();
        let c = b.sqr();
        let d = self.x.add(&b).sqr().sub(&a).sub(&c).dbl();
        let e = a.dbl().add(&a);
        let f = e.sqr();
        let x3 = f.sub(&d.dbl());
        let y3 = e.mul(&d.sub(&x3)).sub(&c.dbl().dbl().dbl());
        let z3 = self.y.mul(&self.z).dbl();
        Jac {
            x: x3,
            y: y3,
            z: z3,
        }
    }
    /// `add-2007-bl` with the doubling / inverse cases handled.
    fn add(&self, o: &Self) -> Self {
        if self.is_identity() {
            return *o;
        }
        if o.is_identity() {
            return *self;
        }
        let z1z1 = self.z.sqr();
        let z2z2 = o.z.sqr();
        let u1 = self.x.mul(&z2z2);
        let u2 = o.x.mul(&z1z1);
        let s1 = self.y.mul(&o.z).mul(&z2z2);
        let s2 = o.y.mul(&self.z).mul(&z1z1);
        if u1 == u2 {
            return if s1 == s2 {
                self.double()
            } else {
                Jac::identity()
            };
        }
        let h = u2.sub(&u1);
        let i = h.dbl().sqr();
        let j = h.mul(&i);
        let rr = s2.sub(&s1).dbl();
        let v = u1.mul(&i);
        let x3 = rr.sqr().sub(&j).sub(&v.dbl());
        let y3 = rr.mul(&v.sub(&x3)).sub(&s1.mul(&j).dbl());
        let z3 = self.z.add(&o.z).sqr().sub(&z1z1).sub(&z2z2).mul(&h);
        Jac {
            x: x3,
            y: y3,
            z: z3,
        }
    }
    fn mul_limbs<const M: usize>(&self, k: &Limbs<M>) -> Self {
        let mut acc = Jac::identity();
        for i in (0..limbs_bits(k)).rev() {
            acc = acc.double();
            if limbs_bit(k, i) {
                acc = acc.add(self);
            }
        }
        acc
    }
    #[cfg(test)]
    fn mul_be(&self, k: &[u8]) -> Self {
        let mut acc = Jac::identity();
        for &byte in k {
            for bit in (0..8).rev() {
                acc = acc.double();
                if (byte >> bit) & 1 == 1 {
                    acc = acc.add(self);
                }
            }
        }
        acc
    }
}

fn in_subgroup<F: CurveField>(p: &Aff<F>) -> bool {
    p.to_jac().mul_limbs(&ctx().r).is_identity()
}

// ---------------------------------------------------------------------------------------------
// Public point types and encodings
// ---------------------------------------------------------------------------------------------

/// Decoding / validation failures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlsError {
    /// The compression flag (bit 7 of byte 0) is clear: only compressed points are accepted.
    NotCompressed,
    /// Infinity flag set but the encoding is not exactly `0xc0 || 0...` (sign bit or x nonzero).
    NonCanonicalInfinity,
    /// A field element is `>= p`.
    NonCanonicalField,
    /// `x` does not lie on the curve (`x^3 + b` is not a square).
    NotOnCurve,
    /// The point is on the curve but not in the order-`r` subgroup.
    NotInSubgroup,
    /// IETF KeyValidate: the public key is the identity.
    IdentityPublicKey,
}

impl core::fmt::Display for BlsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            BlsError::NotCompressed => "compression flag not set",
            BlsError::NonCanonicalInfinity => "non-canonical point at infinity",
            BlsError::NonCanonicalField => "field element not canonical (>= p)",
            BlsError::NotOnCurve => "point not on curve",
            BlsError::NotInSubgroup => "point not in the order-r subgroup",
            BlsError::IdentityPublicKey => "public key is the identity",
        };
        f.write_str(s)
    }
}

impl std::error::Error for BlsError {}

/// A G1 point that passed decoding and the subgroup check (or was computed in-subgroup).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct G1Affine(Aff<Fp>);

/// A G2 point that passed decoding and the subgroup check (or was computed in-subgroup).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct G2Affine(Aff<Fp2>);

const FLAG_C: u8 = 0x80;
const FLAG_INF: u8 = 0x40;
const FLAG_SIGN: u8 = 0x20;

/// Returns `(infinity, sign)` after requiring the compression flag.
fn split_flags(b0: u8) -> Result<(bool, bool), BlsError> {
    if b0 & FLAG_C == 0 {
        return Err(BlsError::NotCompressed);
    }
    Ok((b0 & FLAG_INF != 0, b0 & FLAG_SIGN != 0))
}

fn g1_generator_aff() -> Aff<Fp> {
    Aff {
        x: Fp::from_hex(G1_X_HEX),
        y: Fp::from_hex(G1_Y_HEX),
        inf: false,
    }
}

fn g2_generator_aff() -> Aff<Fp2> {
    Aff {
        x: Fp2::from_hex(G2_X0_HEX, G2_X1_HEX),
        y: Fp2::from_hex(G2_Y0_HEX, G2_Y1_HEX),
        inf: false,
    }
}

impl G1Affine {
    pub fn generator() -> Self {
        G1Affine(g1_generator_aff())
    }
    pub fn is_identity(&self) -> bool {
        self.0.inf
    }
    pub fn to_compressed(&self) -> [u8; 48] {
        encode_g1(&self.0)
    }
}

impl G2Affine {
    pub fn generator() -> Self {
        G2Affine(g2_generator_aff())
    }
    pub fn is_identity(&self) -> bool {
        self.0.inf
    }
    pub fn to_compressed(&self) -> [u8; 96] {
        encode_g2(&self.0)
    }
}

fn encode_g1(p: &Aff<Fp>) -> [u8; 48] {
    let mut o = [0u8; 48];
    if p.inf {
        o[0] = FLAG_C | FLAG_INF;
        return o;
    }
    o = p.x.to_be48();
    o[0] |= FLAG_C;
    if p.y.lex_largest() {
        o[0] |= FLAG_SIGN;
    }
    o
}

fn encode_g2(p: &Aff<Fp2>) -> [u8; 96] {
    let mut o = [0u8; 96];
    if p.inf {
        o[0] = FLAG_C | FLAG_INF;
        return o;
    }
    o[..48].copy_from_slice(&p.x.c1.to_be48());
    o[48..].copy_from_slice(&p.x.c0.to_be48());
    o[0] |= FLAG_C;
    if p.y.lex_largest() {
        o[0] |= FLAG_SIGN;
    }
    o
}

/// Decode without the subgroup check (curve membership is implied by solving for `y`).
fn decode_g1_unchecked(b: &[u8; 48]) -> Result<Aff<Fp>, BlsError> {
    let (inf, sign) = split_flags(b[0])?;
    let mut xb = *b;
    xb[0] &= 0x1f;
    if inf {
        if sign || xb.iter().any(|&v| v != 0) {
            return Err(BlsError::NonCanonicalInfinity);
        }
        return Ok(Aff::identity());
    }
    let x = Fp::from_be_strict(&xb).ok_or(BlsError::NonCanonicalField)?;
    let mut y = x
        .sqr()
        .mul(&x)
        .add(&Fp::curve_b())
        .sqrt()
        .ok_or(BlsError::NotOnCurve)?;
    if y.lex_largest() != sign {
        y = y.neg();
    }
    Ok(Aff { x, y, inf: false })
}

fn decode_g2_unchecked(b: &[u8; 96]) -> Result<Aff<Fp2>, BlsError> {
    let (inf, sign) = split_flags(b[0])?;
    let mut xb = *b;
    xb[0] &= 0x1f;
    if inf {
        if sign || xb.iter().any(|&v| v != 0) {
            return Err(BlsError::NonCanonicalInfinity);
        }
        return Ok(Aff::identity());
    }
    let c1 = Fp::from_be_strict(&xb[..48]).ok_or(BlsError::NonCanonicalField)?;
    let c0 = Fp::from_be_strict(&xb[48..]).ok_or(BlsError::NonCanonicalField)?;
    let x = Fp2::new(c0, c1);
    let mut y = x
        .sqr()
        .mul(&x)
        .add(&Fp2::curve_b())
        .sqrt()
        .ok_or(BlsError::NotOnCurve)?;
    if y.lex_largest() != sign {
        y = y.neg();
    }
    Ok(Aff { x, y, inf: false })
}

/// Cheap curve-decode + sum of compressed G1 keys WITHOUT running 255-bit `[r]P` subgroup scalar
/// multiplications — used ONLY to verify a candidate committee's SSZ commitment against a trusted
/// `SyncCommittee` root BEFORE paying for full [`key_validate`] subgroup checks (anti-DoS).
pub(crate) fn aggregate_g1_compressed_unchecked(
    pubkeys: &[[u8; 48]],
) -> Result<[u8; 48], BlsError> {
    if pubkeys.is_empty() {
        return Err(BlsError::IdentityPublicKey);
    }
    let mut acc = Jac::<Fp>::identity();
    for pk in pubkeys {
        let p = decode_g1_unchecked(pk)?;
        if p.inf {
            return Err(BlsError::IdentityPublicKey);
        }
        acc = acc.add(&p.to_jac());
    }
    let aff = acc.to_affine();
    if aff.inf {
        return Err(BlsError::IdentityPublicKey);
    }
    Ok(encode_g1(&aff))
}

/// Strict ZCash-compressed G1 decoding with the mandatory subgroup check. The canonical
/// infinity encoding decodes to the identity; callers that must refuse it check `is_identity()`.
pub fn g1_from_compressed(b: &[u8; 48]) -> Result<G1Affine, BlsError> {
    let p = decode_g1_unchecked(b)?;
    if !in_subgroup(&p) {
        return Err(BlsError::NotInSubgroup);
    }
    Ok(G1Affine(p))
}

/// Strict ZCash-compressed G2 decoding (`x.c1 || x.c0`) with the mandatory subgroup check.
pub fn g2_from_compressed(b: &[u8; 96]) -> Result<G2Affine, BlsError> {
    let p = decode_g2_unchecked(b)?;
    if !in_subgroup(&p) {
        return Err(BlsError::NotInSubgroup);
    }
    Ok(G2Affine(p))
}

// ---------------------------------------------------------------------------------------------
// RFC 9380 hash_to_curve for G2
// ---------------------------------------------------------------------------------------------

fn expand_message_xmd(msg: &[u8], dst: &[u8], len: usize) -> Vec<u8> {
    let long_dst;
    let dst = if dst.len() > 255 {
        long_dst = crate::sha256(&[&b"H2C-OVERSIZE-DST-"[..], dst].concat());
        &long_dst[..]
    } else {
        dst
    };
    let ell = len.div_ceil(32);
    assert!(
        ell <= 255 && len <= 65535,
        "expand_message_xmd: output too long"
    );
    let mut dst_prime = dst.to_vec();
    dst_prime.push(dst.len() as u8);
    let mut m = vec![0u8; 64];
    m.extend_from_slice(msg);
    m.extend_from_slice(&(len as u16).to_be_bytes());
    m.push(0);
    m.extend_from_slice(&dst_prime);
    let b0 = crate::sha256(&m);
    let mut bi = crate::sha256(&[&b0[..], &[1u8], &dst_prime].concat());
    let mut out = bi.to_vec();
    for i in 2..=ell {
        let x: Vec<u8> = b0.iter().zip(bi.iter()).map(|(a, b)| a ^ b).collect();
        bi = crate::sha256(&[&x[..], &[i as u8], &dst_prime].concat());
        out.extend_from_slice(&bi);
    }
    out.truncate(len);
    out
}

/// `hash_to_field(msg, 2)` over `Fp2` with `L = 64`.
fn hash_to_field_fp2(msg: &[u8], dst: &[u8]) -> [Fp2; 2] {
    let b = expand_message_xmd(msg, dst, 2 * 2 * 64);
    let e = |j: usize| Fp::from_be_reduce(&b[64 * j..64 * (j + 1)]);
    [Fp2::new(e(0), e(1)), Fp2::new(e(2), e(3))]
}

/// Simplified SWU onto `E2': y^2 = x^3 + 240i x + 1012(1 + i)`, `Z = -(2 + i)` (RFC 9380 §6.6.2).
fn sswu_e2(u: &Fp2) -> Aff<Fp2> {
    let a = Fp2::new(Fp::zero(), Fp::from_u64(240));
    let b = Fp2::new(Fp::from_u64(1012), Fp::from_u64(1012));
    let z = Fp2::new(Fp::from_u64(2), Fp::from_u64(1)).neg();
    let zu2 = z.mul(&u.sqr());
    let den = zu2.sqr().add(&zu2);
    let x1 = if den.is_zero() {
        b.mul(&z.mul(&a).inv())
    } else {
        b.neg().mul(&a.inv()).mul(&Fp2::one().add(&den.inv()))
    };
    let g = |x: &Fp2| x.sqr().mul(x).add(&a.mul(x)).add(&b);
    let (x, mut y) = match g(&x1).sqrt() {
        Some(y) => (x1, y),
        None => {
            let x2 = zu2.mul(&x1);
            (
                x2,
                g(&x2)
                    .sqrt()
                    .expect("SSWU: g(x2) is square when g(x1) is not"),
            )
        }
    };
    if u.sgn0() != y.sgn0() {
        y = y.neg();
    }
    Aff { x, y, inf: false }
}

fn iso3_consts() -> &'static [[Fp2; 4]; 5] {
    static K: OnceLock<[[Fp2; 4]; 5]> = OnceLock::new();
    K.get_or_init(|| {
        let mut k = [[Fp2::zero(); 4]; 5];
        for (i, j, c0, c1) in ISO3 {
            k[i][j] = Fp2::from_hex(c0, c1);
        }
        k
    })
}

/// RFC 9380 App. E.3: 3-isogeny `E2' -> E2`.
fn iso3_map(p: &Aff<Fp2>) -> Aff<Fp2> {
    if p.inf {
        return *p;
    }
    let k = iso3_consts();
    let x = p.x;
    let x2 = x.sqr();
    let x3 = x2.mul(&x);
    let x_num = k[1][3]
        .mul(&x3)
        .add(&k[1][2].mul(&x2))
        .add(&k[1][1].mul(&x))
        .add(&k[1][0]);
    let x_den = x2.add(&k[2][1].mul(&x)).add(&k[2][0]);
    let y_num = k[3][3]
        .mul(&x3)
        .add(&k[3][2].mul(&x2))
        .add(&k[3][1].mul(&x))
        .add(&k[3][0]);
    let y_den = x3
        .add(&k[4][2].mul(&x2))
        .add(&k[4][1].mul(&x))
        .add(&k[4][0]);
    if x_den.is_zero() || y_den.is_zero() {
        return Aff::identity();
    }
    Aff {
        x: x_num.mul(&x_den.inv()),
        y: p.y.mul(&y_num).mul(&y_den.inv()),
        inf: false,
    }
}

fn map_to_curve_g2(u: &Fp2) -> Aff<Fp2> {
    iso3_map(&sswu_e2(u))
}

/// RFC 9380 `BLS12381G2_XMD:SHA-256_SSWU_RO_` with the given DST.
pub fn hash_to_g2(msg: &[u8], dst: &[u8]) -> G2Affine {
    let [u0, u1] = hash_to_field_fp2(msg, dst);
    let r = map_to_curve_g2(&u0)
        .to_jac()
        .add(&map_to_curve_g2(&u1).to_jac());
    G2Affine(r.mul_limbs(&ctx().h_eff).to_affine())
}

// ---------------------------------------------------------------------------------------------
// Pairing
// ---------------------------------------------------------------------------------------------

/// Line through the untwisted `T` with twisted slope `lam`, evaluated at `P` and scaled by `w^3`
/// (powers of `w` lie in the kernel of the final exponentiation):
/// `l * w^3 = (lam * x_T - y_T) - lam * x_P * v + y_P * v * w`.
fn line_eval(lam: &Fp2, t: &Aff<Fp2>, p: &Aff<Fp>) -> Fp12 {
    Fp12 {
        c0: Fp6 {
            c0: lam.mul(&t.x).sub(&t.y),
            c1: lam.mul_fp(&p.x).neg(),
            c2: Fp2::zero(),
        },
        c1: Fp6 {
            c0: Fp2::zero(),
            c1: Fp2::new(p.y, Fp::zero()),
            c2: Fp2::zero(),
        },
    }
}

/// Multi-Miller loop `prod f_{|x|, Q_i}(P_i)`, conjugated for `x < 0`. Inputs are non-identity
/// points of order `r`, so `T = [k]Q` never meets `O` or `±Q` for the prefixes `k` of `|x|`.
fn miller_loop(pairs: &[(Aff<Fp>, Aff<Fp2>)]) -> Fp12 {
    let three = Fp2::from_u64(3);
    let mut f = Fp12::one();
    let mut ts: Vec<Aff<Fp2>> = pairs.iter().map(|(_, q)| *q).collect();
    for i in (0..63).rev() {
        f = f.sqr();
        for (t, (p, _)) in ts.iter_mut().zip(pairs.iter()) {
            let lam = t.x.sqr().mul(&three).mul(&t.y.dbl().inv());
            f = f.mul(&line_eval(&lam, t, p));
            let x3 = lam.sqr().sub(&t.x.dbl());
            let y3 = lam.mul(&t.x.sub(&x3)).sub(&t.y);
            *t = Aff {
                x: x3,
                y: y3,
                inf: false,
            };
        }
        if (X_ABS >> i) & 1 == 1 {
            for (t, (p, q)) in ts.iter_mut().zip(pairs.iter()) {
                let lam = q.y.sub(&t.y).mul(&q.x.sub(&t.x).inv());
                f = f.mul(&line_eval(&lam, t, p));
                let x3 = lam.sqr().sub(&t.x).sub(&q.x);
                let y3 = lam.mul(&t.x.sub(&x3)).sub(&t.y);
                *t = Aff {
                    x: x3,
                    y: y3,
                    inf: false,
                };
            }
        }
    }
    f.conj()
}

/// `f^((p^12 - 1) / r) = (f^(p^6) / f)^((p^6 + 1) / r)`.
fn final_exponentiation(f: &Fp12) -> Fp12 {
    if f.is_zero() {
        return Fp12::zero();
    }
    f.conj().mul(&f.inv()).pow(&ctx().e_hard)
}

fn pairing_product(pairs: &[(Aff<Fp>, Aff<Fp2>)]) -> Fp12 {
    let v: Vec<(Aff<Fp>, Aff<Fp2>)> = pairs
        .iter()
        .filter(|(p, q)| !p.inf && !q.inf)
        .copied()
        .collect();
    if v.is_empty() {
        return Fp12::one();
    }
    final_exponentiation(&miller_loop(&v))
}

/// `prod e(P_i, Q_i) == 1` (pairs with an identity component contribute 1).
pub fn pairing_product_is_one(pairs: &[(G1Affine, G2Affine)]) -> bool {
    let v: Vec<(Aff<Fp>, Aff<Fp2>)> = pairs.iter().map(|(p, q)| (p.0, q.0)).collect();
    pairing_product(&v) == Fp12::one()
}

// ---------------------------------------------------------------------------------------------
// BLS signatures (Ethereum: minimal-pubkey-size, proof-of-possession ciphersuite)
// ---------------------------------------------------------------------------------------------

/// Sum of G1 points (identity for the empty slice).
pub fn aggregate_g1(points: &[G1Affine]) -> G1Affine {
    let s = points
        .iter()
        .fold(Jac::<Fp>::identity(), |acc, p| acc.add(&p.0.to_jac()));
    G1Affine(s.to_affine())
}

/// IETF `KeyValidate`: strict decode + subgroup check, identity refused.
pub fn key_validate(pk: &[u8; 48]) -> Result<G1Affine, BlsError> {
    let p = g1_from_compressed(pk)?;
    if p.is_identity() {
        return Err(BlsError::IdentityPublicKey);
    }
    Ok(p)
}

/// IETF `FastAggregateVerify` (`draft-irtf-cfrg-bls-signature` §3.3.4) with [`DST_POP`].
///
/// **Caller security precondition:** Every key in `pubkeys` MUST come from a registry or consensus
/// committee where proof-of-possession (`PoP`) was verified at key registration (or be pinned by a
/// trusted `SyncCommittee` commitment, as in [`crate::verify_eth_header_s11`]); without PoP, an
/// adversary choosing a key as a function of honest keys can mount a rogue-key attack.
///
/// Refuses an empty key set, any identity key, an identity aggregate key, and a signature that
/// fails strict decoding, the subgroup check, or is the identity; then checks
/// `e(aggpk, H(msg)) == e(G1, sig)`.
pub fn fast_aggregate_verify(pubkeys: &[G1Affine], msg: &[u8], sig: &[u8; 96]) -> bool {
    if pubkeys.is_empty() || pubkeys.iter().any(G1Affine::is_identity) {
        return false;
    }
    let agg = aggregate_g1(pubkeys);
    if agg.is_identity() {
        return false;
    }
    let s = match g2_from_compressed(sig) {
        Ok(s) if !s.is_identity() => s,
        _ => return false,
    };
    let h = hash_to_g2(msg, DST_POP);
    pairing_product(&[(agg.0, h.0), (g1_generator_aff().neg(), s.0)]) == Fp12::one()
}

/// IETF `Verify` with [`DST_POP`] (same refusals as [`fast_aggregate_verify`]).
pub fn verify(pk: &G1Affine, msg: &[u8], sig: &[u8; 96]) -> bool {
    fast_aggregate_verify(core::slice::from_ref(pk), msg, sig)
}

/// Byte-slice wrapper around [`key_validate`] + [`fast_aggregate_verify`]: validates every
/// compressed G1 public key (strict ZCash encoding, order-`r` subgroup, non-identity) and
/// verifies the compressed G2 aggregate signature under [`DST_POP`].
pub fn fast_aggregate_verify_bytes(pubkeys: &[[u8; 48]], msg: &[u8], sig: &[u8; 96]) -> bool {
    if pubkeys.is_empty() {
        return false;
    }
    let mut validated = Vec::with_capacity(pubkeys.len());
    for pk in pubkeys {
        let Ok(p) = key_validate(pk) else {
            return false;
        };
        validated.push(p);
    }
    fast_aggregate_verify(&validated, msg, sig)
}

/// Fixture-only scalar: big-endian `sk` reduced mod `r`; panics on zero.
fn fixture_scalar(sk: &[u8; 32]) -> Limbs<4> {
    let fr = &ctx().fr;
    let k = fr.from_mont(&fr.from_be_reduce(sk));
    assert!(!limbs_is_zero(&k), "fixture: secret key is zero mod r");
    k
}

/// TEST FIXTURE (NOT constant time): `[sk mod r] G1`, compressed. Panics if `sk = 0 mod r`.
pub fn fixture_sk_to_pk(sk: &[u8; 32]) -> [u8; 48] {
    encode_g1(
        &g1_generator_aff()
            .to_jac()
            .mul_limbs(&fixture_scalar(sk))
            .to_affine(),
    )
}

/// TEST FIXTURE (NOT constant time): `[sk mod r] H(msg)` under [`DST_POP`], compressed.
pub fn fixture_sign(sk: &[u8; 32], msg: &[u8]) -> [u8; 96] {
    let k = fixture_scalar(sk);
    let h = hash_to_g2(msg, DST_POP);
    encode_g2(&h.0.to_jac().mul_limbs(&k).to_affine())
}

/// TEST FIXTURE: sum of signatures (each strictly decoded and subgroup-checked; panics on an
/// invalid one). The empty slice yields the identity encoding.
pub fn fixture_aggregate_signatures(sigs: &[[u8; 96]]) -> [u8; 96] {
    let s = sigs.iter().fold(Jac::<Fp2>::identity(), |acc, b| {
        let p = g2_from_compressed(b).expect("fixture_aggregate_signatures: invalid signature");
        acc.add(&p.0.to_jac())
    });
    encode_g2(&s.to_affine())
}

#[cfg(test)]
mod tests;
