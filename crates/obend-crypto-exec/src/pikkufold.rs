//! `PikkuFold` (`ePrint 2026/1809`) + `Akita` (`ePrint 2026/1983`) Track L Lattice-SIS Engine
//! & Salted Zero-Knowledge `SameOpening` Dark Bazaar Clearing Proof (`K5`–`K7`):
//! - Dedicated partially-splitting cyclotomic ring $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$
//!   over 60-bit prime $q_{\text{lat}} = 2^{60} - 107 \equiv 5 \pmod 8$ (`X^{64}+1 = (X^{32}-\zeta)(X^{32}+\zeta)`,
//!   avoiding Goldilocks linear splitting `F10` while keeping unboxed `[i64; 64]` arithmetic overflow-free!)
//! - **0-multiplication** Kronecker ternary $\{-1, 0, +1\}$ witness projection (`PikkuFold`)
//! - $\ge 145$-bit single-round invertible ring challenge space (`squeeze_invertible_ring_challenge`)
//! - Explicit per-round $\ell_\infty$ norm budget tracking (`F11`) & linear 2-to-1 witness folding
//! - Recursive `Akita` split-and-fold MSIS + linear-form opening proof down to dimension 1
//! - Constructive discrepancy witness extractor `extract_sis_collision` (`SisBreak`, closing `F1`/`F2`)
//! - Salted zero-knowledge `commit_private_order` + `SmudgeSafe` + KKT zero-gap `SameOpening` Dark Bazaar proof (`K7`).

#![allow(clippy::needless_range_loop)]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::canopy::{
    CanopyBatchedProof, CanopyCommitment, CanopyError, CanopyParams, canopy_commit, canopy_open,
    canopy_verify,
};
use crate::goldilocks::{
    CanonicalLift, CanonicalLiftError, Goldilocks, GoldilocksExt2, mle_eval_base_at_ext2,
};
use crate::transcript::{
    Cshake256Xof, DUAL_TRACK1_LABEL, DUAL_TRACK2_LABEL, FenziTranscript, InstanceBound,
    RelationBound, Unbound, cshake256_32, leb128,
};

/// Cyclotomic power-of-two ring degree $d = 64$ for $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$.
pub const RING_DEGREE: usize = 64;

/// Half-degree $d / 2 = 32$ of the two irreducible Lyubashevsky–Seiler CRT factors $X^{32} \mp \zeta$.
pub const HALF_RING_DEGREE: usize = RING_DEGREE / 2;

/// Dedicated 60-bit lattice prime $q_{\text{lat}} = 2^{60} - 107 = 1\_152\_921\_504\_606\_846\_869 \equiv 5 \pmod 8$.
pub const Q_LAT: i64 = (1i64 << 60) - 107;

/// Centered half-modulus $\lfloor q_{\text{lat}} / 2 \rfloor = 576\_460\_752\_303\_423\_434$.
pub const HALF_Q_LAT: i64 = (Q_LAT - 1) / 2;

/// Primitive 4th root of unity $\zeta = 383\_824\_447\_308\_448\_458 \bmod q_{\text{lat}}$ ($\zeta^2 \equiv -1$).
pub const Q_LAT_ZETA: i64 = 383_824_447_308_448_458;

/// Conservative non-wrapping $\ell_\infty$ norm ceiling $< q_{\text{lat}} / 4$.
pub const MAX_SAFE_SIS_NORM: u64 = (Q_LAT as u64) / 4 - 1;

/// Base-$2^{16}$ Goldilocks limb bound ($65535$).
pub const GADGET_LIMB_MAX: u64 = 0xFFFF;

/// Maximum $\ell_1$ norm of a canonical base-5 invertible ring challenge $c \in \{-2,-1,0,1,2\}^{64} \setminus \{0\}$
/// (`|C^+_{<=96}| > 2^{147.5}`, giving $\le 4 / |C^+_{<=96}| < 2^{-145} \ll 2^{-128}$ single-round soundness!).
pub const AKITA_CHALLENGE_MAX_L1: u64 = 96;

/// Domain customizations and labels.
pub const PIKKUFOLD_CRS_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.PIKKUFOLD.CRS/v1";
pub const AKITA_PARAMS_DIGEST_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.AKITA.PARAMS_DIGEST/v1";
pub const AKITA_CHALLENGE_XOF_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.AKITA.RING_CHALLENGE/v1";
pub const AKITA_PARAMS_LABEL: &[u8] = b"AKITA.LATTICE.PARAMS";
pub const AKITA_ROUND_LABEL: &[u8] = b"AKITA.SPLITFOLD.ROUND";
pub const AKITA_KRON_LABEL: &[u8] = b"PIKKUFOLD.KRONECKER.PROJ";
pub const AKITA_FINAL_LABEL: &[u8] = b"AKITA.FINAL.WITNESS";
pub const DARK_BAZAAR_PROTO_ID: &str = "OBEND.DARKBAZAAR.SAMEOPENING/v2";

/// Errors emitted by `PikkuFold`, `Akita`, and `SameOpening` Dark Bazaar operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LatticeError {
    InvalidMatrixDimensions {
        rows: usize,
        cols: usize,
    },
    MatrixEntryCountMismatch {
        expected: usize,
        actual: usize,
    },
    WitnessLengthMismatch {
        expected: usize,
        actual: usize,
    },
    WitnessNormExceeded {
        actual: u64,
        bound: u64,
    },
    NormBudgetOverflow {
        next_bound: u64,
        ceiling: u64,
    },
    OutOfBoundsColumn {
        col: usize,
        cols: usize,
    },
    OutOfBoundsSlot {
        slot: usize,
    },
    KroneckerArityMismatch {
        expected_len: usize,
        actual_len: usize,
    },
    InvalidGadgetLimb(i64),
    NonCanonicalGoldilocks(CanonicalLiftError),
    AkitaRoundCountMismatch {
        expected: usize,
        actual: usize,
    },
    AkitaCrossCommitmentSumMismatch {
        round: usize,
    },
    AkitaFinalCommitmentMismatch,
    AkitaKroneckerProjectionMismatch,
    ZeroNormBoundOnNonZeroCommitment,
    NoCollisionWitnessIsIdentical,
    CommitmentsDoNotMatch,
    ExtractedVectorNotInKernel,
    /// `SameOpening` Dark Bazaar errors (`K7`, closing `F6` & `F7`):
    MaxBitsExceedsCanonical63(u32),
    BitWitnessLengthExceeded {
        max_bits: u32,
        actual_len: usize,
    },
    BlindingNormExceeded {
        actual: u64,
        max_allowed: u64,
    },
    UnsmudgedOrInsufficientNoiseBudget,
    DecryptionMarginWrapped,
    DuplicateOrIdenticalMarketAssets,
    OrderWitnessCountMismatch {
        expected: usize,
        actual: usize,
    },
    DuplicateAccountOrder(u64),
    CommitmentMismatchAtOrder(usize),
    ZeroKnowledgeRelationFailedAtOrder(usize),
    FlowConservationFailed,
    NegativeOrExcessFillAtOrder(usize),
    NonZeroPrimalDualKktGap {
        primal: i128,
        dual: i128,
    },
    CanopyFailure(CanopyError),
}

impl fmt::Display for LatticeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl From<CanonicalLiftError> for LatticeError {
    fn from(e: CanonicalLiftError) -> Self {
        Self::NonCanonicalGoldilocks(e)
    }
}

impl From<CanopyError> for LatticeError {
    fn from(e: CanopyError) -> Self {
        Self::CanopyFailure(e)
    }
}

// ============================================================================
// 1. Dedicated Cyclotomic Ring R_{q_lat} = Z_{q_lat}[X] / (X^64 + 1)
// ============================================================================

#[inline]
pub const fn center_mod_q(x: i128) -> i64 {
    let q = Q_LAT as i128;
    let mut r = (x % q) as i64;
    if r < 0 {
        r += Q_LAT;
    }
    if r > HALF_Q_LAT {
        r -= Q_LAT;
    }
    r
}

#[inline]
const fn mod_pos_q(x: i128) -> i64 {
    let q = Q_LAT as i128;
    let mut r = (x % q) as i64;
    if r < 0 {
        r += Q_LAT;
    }
    r
}

#[inline]
fn mod_pow_q(mut base: i64, mut exp: u64) -> i64 {
    let mut acc = 1i64;
    base = mod_pos_q(base as i128);
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = mod_pos_q((acc as i128) * (base as i128));
        }
        base = mod_pos_q((base as i128) * (base as i128));
        exp >>= 1;
    }
    acc
}

#[inline]
fn mod_inv_q(a: i64) -> Option<i64> {
    let c = mod_pos_q(a as i128);
    if c == 0 {
        None
    } else {
        Some(mod_pow_q(c, (Q_LAT as u64) - 2))
    }
}

/// Element of $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$ stored as an unboxed
/// centered `[i64; 64]` coefficient array in $[-\lfloor q_{\text{lat}}/2 \rfloor, \lfloor q_{\text{lat}}/2 \rfloor]$.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct RingElem {
    coeffs: [i64; RING_DEGREE],
}

impl Default for RingElem {
    fn default() -> Self {
        Self::zero()
    }
}

impl fmt::Debug for RingElem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RingElem(c0={}, c1={}, norm_inf={})",
            self.coeffs[0],
            self.coeffs[1],
            self.norm_inf()
        )
    }
}

impl RingElem {
    #[inline]
    pub const fn zero() -> Self {
        Self {
            coeffs: [0i64; RING_DEGREE],
        }
    }

    #[inline]
    pub const fn one() -> Self {
        let mut coeffs = [0i64; RING_DEGREE];
        coeffs[0] = 1;
        Self { coeffs }
    }

    #[inline]
    pub const fn constant(c: i64) -> Self {
        let mut coeffs = [0i64; RING_DEGREE];
        coeffs[0] = center_mod_q(c as i128);
        Self { coeffs }
    }

    /// Construct from an unboxed `[i64; 64]` array, centering each entry modulo $q_{\text{lat}}$.
    pub fn from_coeffs(raw: [i64; RING_DEGREE]) -> Self {
        let mut coeffs = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            coeffs[i] = center_mod_q(raw[i] as i128);
        }
        Self { coeffs }
    }

    /// Construct from a slice of length $\le 64$, zero-padding higher degrees.
    pub fn from_i64_slice(slice: &[i64]) -> Result<Self, LatticeError> {
        if slice.len() > RING_DEGREE {
            return Err(LatticeError::OutOfBoundsSlot { slot: slice.len() });
        }
        let mut coeffs = [0i64; RING_DEGREE];
        for (i, &v) in slice.iter().enumerate() {
            coeffs[i] = center_mod_q(v as i128);
        }
        Ok(Self { coeffs })
    }

    /// Unboxed read-only slice view over centered coefficients.
    #[inline]
    pub const fn coeffs(&self) -> &[i64; RING_DEGREE] {
        &self.coeffs
    }

    #[inline]
    pub const fn as_slice(&self) -> &[i64] {
        &self.coeffs
    }

    /// Exact centered $\ell_\infty$ norm $\max_{0 \le i < d} |c_i|$.
    #[inline]
    pub fn norm_inf(&self) -> u64 {
        let mut m = 0u64;
        for &c in &self.coeffs {
            let abs = c.unsigned_abs();
            if abs > m {
                m = abs;
            }
        }
        m
    }

    /// Exact centered $\ell_1$ norm $\sum_{i=0}^{d-1} |c_i|$ (bounds multiplicative norm expansion!).
    #[inline]
    pub fn norm_l1(&self) -> u64 {
        let mut s = 0u64;
        for &c in &self.coeffs {
            s = s.saturating_add(c.unsigned_abs());
        }
        s
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.coeffs.iter().all(|&c| c == 0)
    }

    #[inline]
    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            let mut s = self.coeffs[i] + rhs.coeffs[i];
            if s > HALF_Q_LAT {
                s -= Q_LAT;
            } else if s < -HALF_Q_LAT {
                s += Q_LAT;
            }
            out[i] = s;
        }
        Self { coeffs: out }
    }

    #[inline]
    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            let mut d = self.coeffs[i] - rhs.coeffs[i];
            if d > HALF_Q_LAT {
                d -= Q_LAT;
            } else if d < -HALF_Q_LAT {
                d += Q_LAT;
            }
            out[i] = d;
        }
        Self { coeffs: out }
    }

    #[inline]
    pub fn neg(&self) -> Self {
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            out[i] = -self.coeffs[i];
        }
        Self { coeffs: out }
    }

    #[inline]
    pub fn scalar_mul(&self, s: i64) -> Self {
        let s128 = s as i128;
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            out[i] = center_mod_q((self.coeffs[i] as i128) * s128);
        }
        Self { coeffs: out }
    }

    /// **0-multiplication** negacyclic monomial shift: computes $(\text{sign} \cdot X^{\text{exp}}) \cdot \text{self} \bmod (X^d + 1)$
    /// where `sign` $\in \{-1, +1\}$ and `exp < d`, preserving $\|\text{out}\|_\infty == \|\text{self}\|_\infty$!
    pub fn mul_signed_monomial(&self, sign: i64, exp: usize) -> Self {
        debug_assert!(sign == 1 || sign == -1);
        let shift = exp & (RING_DEGREE - 1);
        let flip = if ((exp / RING_DEGREE) & 1) == 1 {
            -sign
        } else {
            sign
        };
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            if i + shift < RING_DEGREE {
                out[i + shift] = if flip == 1 {
                    self.coeffs[i]
                } else {
                    -self.coeffs[i]
                };
            } else {
                // X^d = -1 in R_{q_lat}
                let idx = i + shift - RING_DEGREE;
                out[idx] = if flip == 1 {
                    -self.coeffs[i]
                } else {
                    self.coeffs[i]
                };
            }
        }
        Self { coeffs: out }
    }

    /// Negacyclic product in $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$ using lazy `i128`
    /// accumulation (`64 * 2^94 << 2^127` — exactly ONE modular reduction per output slot!).
    pub fn mul(&self, rhs: &Self) -> Self {
        let mut acc = [0i128; RING_DEGREE];
        for i in 0..RING_DEGREE {
            let ai = self.coeffs[i] as i128;
            if ai == 0 {
                continue;
            }
            for j in 0..(RING_DEGREE - i) {
                acc[i + j] += ai * (rhs.coeffs[j] as i128);
            }
            for j in (RING_DEGREE - i)..RING_DEGREE {
                acc[i + j - RING_DEGREE] -= ai * (rhs.coeffs[j] as i128);
            }
        }
        let mut out = [0i64; RING_DEGREE];
        for k in 0..RING_DEGREE {
            out[k] = center_mod_q(acc[k]);
        }
        Self { coeffs: out }
    }

    /// Exact multiplicative inverse in $R_{q_{\text{lat}}} \cong \mathbb{F}_{q_{\text{lat}}}[X]/(X^{32} - \zeta) \times
    /// \mathbb{F}_{q_{\text{lat}}}[X]/(X^{32} + \zeta)$ via CRT + Extended GCD over $\mathbb{F}_{q_{\text{lat}}}[X]$.
    ///
    /// By Lyubashevsky–Seiler (Eurocrypt 2018), **every** non-zero element with
    /// $\|y\|_\infty < \frac{1}{\sqrt{2}} \sqrt{q_{\text{lat}}} \approx 1.18 \times 10^7$ is guaranteed invertible!
    pub fn inv(&self) -> Option<Self> {
        // Project onto a_minus = a mod (X^32 - zeta) and a_plus = a mod (X^32 + zeta)
        let mut a_minus = [0i64; HALF_RING_DEGREE];
        let mut a_plus = [0i64; HALF_RING_DEGREE];
        for i in 0..HALF_RING_DEGREE {
            let z_hi = (Q_LAT_ZETA as i128) * (self.coeffs[i + HALF_RING_DEGREE] as i128);
            a_minus[i] = mod_pos_q((self.coeffs[i] as i128) + z_hi);
            a_plus[i] = mod_pos_q((self.coeffs[i] as i128) - z_hi);
        }

        let inv_minus = poly32_inv_mod_binom(&a_minus, mod_pos_q(-(Q_LAT_ZETA as i128)))?;
        let inv_plus = poly32_inv_mod_binom(&a_plus, Q_LAT_ZETA)?;

        // Reconstruct via CRT:
        // b[i]      = (inv_minus[i] + inv_plus[i]) / 2
        // b[i + 32] = (inv_minus[i] - inv_plus[i]) / (2 * zeta)
        let inv_2 = mod_inv_q(2)?;
        let inv_2zeta = mod_inv_q(mod_pos_q(2 * (Q_LAT_ZETA as i128)))?;

        let mut out = [0i64; RING_DEGREE];
        for i in 0..HALF_RING_DEGREE {
            let sum = (inv_minus[i] as i128) + (inv_plus[i] as i128);
            let diff = (inv_minus[i] as i128) - (inv_plus[i] as i128);
            out[i] = center_mod_q(sum * (inv_2 as i128));
            out[i + HALF_RING_DEGREE] = center_mod_q(diff * (inv_2zeta as i128));
        }
        Some(Self { coeffs: out })
    }

    /// Canonical 512-byte (`64 * 8`) big-endian signed `i64` encoding.
    pub fn to_be_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(RING_DEGREE * 8);
        for &c in &self.coeffs {
            out.extend_from_slice(&c.to_be_bytes());
        }
        out
    }

    /// Strict canonical decoding rejecting out-of-range coefficients outside $[- \lfloor q/2 \rfloor, \lfloor q/2 \rfloor]$.
    pub fn from_be_bytes_canonical(bytes: &[u8]) -> Result<Self, LatticeError> {
        if bytes.len() != RING_DEGREE * 8 {
            return Err(LatticeError::OutOfBoundsSlot { slot: bytes.len() });
        }
        let mut coeffs = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&bytes[8 * i..8 * i + 8]);
            let val = i64::from_be_bytes(arr);
            if !(-HALF_Q_LAT..=HALF_Q_LAT).contains(&val) {
                return Err(LatticeError::InvalidGadgetLimb(val));
            }
            coeffs[i] = val;
        }
        Ok(Self { coeffs })
    }
}

/// Extended Euclidean Algorithm in $\mathbb{F}_{q_{\text{lat}}}[X]$ modulo $X^{32} + c_0$.
fn poly32_inv_mod_binom(
    a: &[i64; HALF_RING_DEGREE],
    c0_const: i64,
) -> Option<[i64; HALF_RING_DEGREE]> {
    fn trim_deg(p: &mut Vec<i64>) {
        while p.len() > 1 && *p.last().unwrap() == 0 {
            p.pop();
        }
    }
    fn poly_div_rem(num: &[i64], den: &[i64]) -> Option<(Vec<i64>, Vec<i64>)> {
        let mut rem = num.to_vec();
        trim_deg(&mut rem);
        let mut d = den.to_vec();
        trim_deg(&mut d);
        if d.len() == 1 && d[0] == 0 {
            return None;
        }
        let deg_d = d.len() - 1;
        if rem.len() - 1 < deg_d || (rem.len() == 1 && rem[0] == 0) {
            return Some((vec![0], rem));
        }
        let lead_inv = mod_inv_q(d[deg_d])?;
        let mut quot = vec![0i64; rem.len() - deg_d];
        while rem.len() > deg_d && !(rem.len() == 1 && rem[0] == 0) {
            let cur_deg = rem.len() - 1;
            let shift = cur_deg - deg_d;
            let factor = mod_pos_q((rem[cur_deg] as i128) * (lead_inv as i128));
            quot[shift] = factor;
            for i in 0..=deg_d {
                let sub = mod_pos_q((factor as i128) * (d[i] as i128));
                rem[i + shift] = mod_pos_q((rem[i + shift] as i128) - (sub as i128));
            }
            trim_deg(&mut rem);
            if shift == 0 {
                break;
            }
        }
        trim_deg(&mut quot);
        Some((quot, rem))
    }
    fn poly_mul(x: &[i64], y: &[i64]) -> Vec<i64> {
        let mut out = vec![0i64; x.len() + y.len() - 1];
        for (i, &xi) in x.iter().enumerate() {
            if xi == 0 {
                continue;
            }
            for (j, &yj) in y.iter().enumerate() {
                out[i + j] = mod_pos_q((out[i + j] as i128) + (xi as i128) * (yj as i128));
            }
        }
        trim_deg(&mut out);
        out
    }
    fn poly_sub(x: &[i64], y: &[i64]) -> Vec<i64> {
        let n = x.len().max(y.len());
        let mut out = vec![0i64; n];
        for i in 0..n {
            let xi = if i < x.len() { x[i] } else { 0 };
            let yi = if i < y.len() { y[i] } else { 0 };
            out[i] = mod_pos_q((xi as i128) - (yi as i128));
        }
        trim_deg(&mut out);
        out
    }

    let mut modulus = vec![0i64; HALF_RING_DEGREE + 1];
    modulus[0] = mod_pos_q(c0_const as i128);
    modulus[HALF_RING_DEGREE] = 1;

    let mut r0 = modulus.clone();
    let mut r1 = a.to_vec();
    trim_deg(&mut r1);
    if r1.len() == 1 && r1[0] == 0 {
        return None;
    }

    let mut t0 = vec![0i64];
    let mut t1 = vec![1i64];

    while !(r1.len() == 1 && r1[0] == 0) {
        let (q, r_next) = poly_div_rem(&r0, &r1)?;
        let qt1 = poly_mul(&q, &t1);
        let (_, t_next) = poly_div_rem(&poly_sub(&t0, &qt1), &modulus)?;
        r0 = r1;
        r1 = r_next;
        t0 = t1;
        t1 = t_next;
    }

    // Irreducibility check: gcd must have degree 0 and non-zero constant!
    if r0.len() != 1 || r0[0] == 0 {
        return None;
    }
    let scale = mod_inv_q(r0[0])?;
    let mut out = [0i64; HALF_RING_DEGREE];
    for (i, &ti) in t0.iter().enumerate().take(HALF_RING_DEGREE) {
        out[i] = mod_pos_q((ti as i128) * (scale as i128));
    }
    Some(out)
}

// ============================================================================
// 2. 0-Multiplication Kronecker Ternary {-1, 0, +1} Projection (`PikkuFold`)
// ============================================================================

/// Ternary coefficient in $\{-1, 0, +1\}$ (`Obend.Crypto.DualSpine.TernaryCoeff`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i8)]
pub enum TernaryTrit {
    NegOne = -1,
    Zero = 0,
    PosOne = 1,
}

impl TernaryTrit {
    #[inline]
    pub const fn from_i8(v: i8) -> Option<Self> {
        match v {
            -1 => Some(Self::NegOne),
            0 => Some(Self::Zero),
            1 => Some(Self::PosOne),
            _ => None,
        }
    }

    #[inline]
    pub const fn mul_trit(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::PosOne, x) | (x, Self::PosOne) => x,
            (Self::NegOne, Self::NegOne) => Self::PosOne,
        }
    }
}

/// Number of non-zero ($\pm 1$) entries in a ternary row (`ternaryRowWeight` in `DualSpine.lean`).
pub fn ternary_row_weight(row: &[TernaryTrit]) -> usize {
    row.iter().filter(|&&t| t != TernaryTrit::Zero).count()
}

/// **0-multiplication** inner product $\langle \mathbf{t}, \mathbf{w} \rangle \in R_{q_{\text{lat}}}$
/// using pure `i128` additions and subtractions (`0` ring or integer multiplications, `0` overflow!).
pub fn apply_ternary_row_0mul(
    trits: &[TernaryTrit],
    witness: &[RingElem],
) -> Result<RingElem, LatticeError> {
    if trits.len() != witness.len() {
        return Err(LatticeError::WitnessLengthMismatch {
            expected: trits.len(),
            actual: witness.len(),
        });
    }
    let mut acc = [0i128; RING_DEGREE];
    for (&trit, ring_elem) in trits.iter().zip(witness.iter()) {
        match trit {
            TernaryTrit::Zero => continue,
            TernaryTrit::PosOne => {
                let c = ring_elem.coeffs();
                for k in 0..RING_DEGREE {
                    acc[k] += c[k] as i128;
                }
            }
            TernaryTrit::NegOne => {
                let c = ring_elem.coeffs();
                for k in 0..RING_DEGREE {
                    acc[k] -= c[k] as i128;
                }
            }
        }
    }
    let mut out = [0i64; RING_DEGREE];
    for k in 0..RING_DEGREE {
        out[k] = center_mod_q(acc[k]);
    }
    Ok(RingElem { coeffs: out })
}

/// **0-multiplication** matrix projection `P * w` for a ternary matrix `rows` (`PikkuFold 2026/1809`).
pub fn apply_ternary_matrix_0mul(
    rows: &[Vec<TernaryTrit>],
    witness: &[RingElem],
) -> Result<Vec<RingElem>, LatticeError> {
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        out.push(apply_ternary_row_0mul(row, witness)?);
    }
    Ok(out)
}

/// Expand the $k$-fold Kronecker ternary tensor $\bigotimes_{j=0}^{k-1} (t_{j,0}, t_{j,1}) \in \{-1, 0, +1\}^{2^k}$
/// using pure sign logic (**0 multiplications**!).
pub fn expand_kronecker_ternary(trit_pairs: &[[TernaryTrit; 2]]) -> Vec<TernaryTrit> {
    let mut vec = vec![TernaryTrit::PosOne];
    for &[t0, t1] in trit_pairs {
        let mut next = Vec::with_capacity(vec.len() * 2);
        for &cur in &vec {
            next.push(cur.mul_trit(t0));
            next.push(cur.mul_trit(t1));
        }
        vec = next;
    }
    vec
}

/// **0-multiplication** butterfly tree fold of `witness` ($|\mathbf{w}| = 2^k$) against a Kronecker
/// ternary challenge `trit_pairs` (`PikkuFold` structured witness folding!).
pub fn kronecker_ternary_fold_0mul(
    witness: &[RingElem],
    trit_pairs: &[[TernaryTrit; 2]],
) -> Result<RingElem, LatticeError> {
    let expected_len = 1usize << trit_pairs.len();
    if witness.len() != expected_len {
        return Err(LatticeError::KroneckerArityMismatch {
            expected_len,
            actual_len: witness.len(),
        });
    }
    let mut layer = witness.to_vec();
    for &[t0, t1] in trit_pairs.iter().rev() {
        let half = layer.len() >> 1;
        let mut next = Vec::with_capacity(half);
        for j in 0..half {
            let a = match t0 {
                TernaryTrit::Zero => RingElem::zero(),
                TernaryTrit::PosOne => layer[2 * j],
                TernaryTrit::NegOne => layer[2 * j].neg(),
            };
            let b = match t1 {
                TernaryTrit::Zero => RingElem::zero(),
                TernaryTrit::PosOne => layer[2 * j + 1],
                TernaryTrit::NegOne => layer[2 * j + 1].neg(),
            };
            next.push(a.add(&b));
        }
        layer = next;
    }
    Ok(layer[0])
}

// ============================================================================
// 3. Validated Module-SIS Parameters, Commitments & 16-Bit Goldilocks Bridge
// ============================================================================

/// Validated Module-SIS public matrix $A \in R_{q_{\text{lat}}}^{m \times n}$ (`cols = n` power of two).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeParams {
    pub rows: usize,
    pub cols: usize,
    pub crs_seed: [u8; 32],
    /// Row-major `rows * cols` matrix over $R_{q_{\text{lat}}}$.
    pub matrix: Vec<RingElem>,
}

impl LatticeParams {
    /// Expand a verifiable nothing-up-my-sleeve Module-SIS matrix from `crs_seed` via `cSHAKE256`.
    pub fn expand_from_seed(
        crs_seed: [u8; 32],
        rows: usize,
        cols: usize,
    ) -> Result<Self, LatticeError> {
        if rows == 0 || cols == 0 || !cols.is_power_of_two() {
            return Err(LatticeError::InvalidMatrixDimensions { rows, cols });
        }
        let mut matrix = Vec::with_capacity(rows * cols);
        for r in 0..rows {
            for c in 0..cols {
                let mut xof = Cshake256Xof::new(PIKKUFOLD_CRS_CUSTOMIZATION);
                xof.absorb(&crs_seed);
                xof.absorb(&(r as u64).to_be_bytes());
                xof.absorb(&(c as u64).to_be_bytes());
                let mut coeffs = [0i64; RING_DEGREE];
                let mut buf = [0u8; 8];
                for slot in &mut coeffs {
                    xof.squeeze(&mut buf);
                    let raw = u64::from_le_bytes(buf);
                    *slot = center_mod_q(raw as i128);
                }
                matrix.push(RingElem { coeffs });
            }
        }
        Ok(Self {
            rows,
            cols,
            crs_seed,
            matrix,
        })
    }

    /// Construct from an explicit matrix slice, strictly validating non-empty dimensions (`F1` guard).
    pub fn from_validated_matrix(
        rows: usize,
        cols: usize,
        matrix: Vec<RingElem>,
    ) -> Result<Self, LatticeError> {
        if rows == 0 || cols == 0 || !cols.is_power_of_two() {
            return Err(LatticeError::InvalidMatrixDimensions { rows, cols });
        }
        let expected = rows * cols;
        if matrix.len() != expected {
            return Err(LatticeError::MatrixEntryCountMismatch {
                expected,
                actual: matrix.len(),
            });
        }
        Ok(Self {
            rows,
            cols,
            crs_seed: [0u8; 32],
            matrix,
        })
    }

    /// Domain-separated 256-bit `cSHAKE256` commitment over `rows`, `cols`, `crs_seed`, and every
    /// ring entry of `self.matrix` (so both seeded and explicit matrices are injectively bound!).
    pub fn transcript_digest(&self) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(AKITA_PARAMS_DIGEST_CUSTOMIZATION);
        xof.absorb(&(self.rows as u64).to_be_bytes());
        xof.absorb(&(self.cols as u64).to_be_bytes());
        xof.absorb(&self.crs_seed);
        xof.absorb(&(self.matrix.len() as u64).to_be_bytes());
        for entry in &self.matrix {
            xof.absorb(&entry.to_be_bytes());
        }
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }
}

/// Bind `LatticeParams` (`rows`, `cols`, `crs_seed`, and full matrix digest) together with
/// `extra_circuit_desc` inside `FenziTranscript::bind_relation`.
pub fn bind_akita_relation(
    tr: FenziTranscript<Unbound>,
    protocol_id: &str,
    vk_digest: &[u8; 32],
    params: &LatticeParams,
    extra_circuit_desc: &[u8],
) -> FenziTranscript<RelationBound> {
    let params_digest = params.transcript_digest();
    let mut circuit_desc = Vec::with_capacity(48 + extra_circuit_desc.len());
    circuit_desc.extend_from_slice(&params_digest);
    circuit_desc.extend_from_slice(&(params.rows as u64).to_be_bytes());
    circuit_desc.extend_from_slice(&(params.cols as u64).to_be_bytes());
    circuit_desc.extend_from_slice(&leb128(extra_circuit_desc.len()));
    circuit_desc.extend_from_slice(extra_circuit_desc);
    tr.bind_relation(protocol_id, vk_digest, &circuit_desc)
}

/// Module-SIS commitment syndrome $t = A \cdot \mathbf{w} \in R_{q_{\text{lat}}}^m$.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeCommitment {
    pub cols: u32,
    pub syndrome: Vec<RingElem>,
}

impl LatticeCommitment {
    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 + self.syndrome.len() * RING_DEGREE * 8);
        out.extend_from_slice(&self.cols.to_be_bytes());
        out.extend_from_slice(&leb128(self.syndrome.len()));
        for elem in &self.syndrome {
            out.extend_from_slice(&elem.to_be_bytes());
        }
        out
    }
}

#[inline]
pub fn max_witness_norm_inf(witness: &[RingElem]) -> u64 {
    witness.iter().map(RingElem::norm_inf).max().unwrap_or(0)
}

fn mat_vec_mul_submatrix(
    rows: usize,
    cols: usize,
    matrix: &[RingElem],
    witness: &[RingElem],
) -> Vec<RingElem> {
    debug_assert_eq!(matrix.len(), rows * cols);
    debug_assert_eq!(witness.len(), cols);
    let mut out = Vec::with_capacity(rows);
    for r in 0..rows {
        let mut acc = RingElem::zero();
        let row_off = r * cols;
        for c in 0..cols {
            if !witness[c].is_zero() {
                acc = acc.add(&matrix[row_off + c].mul(&witness[c]));
            }
        }
        out.push(acc);
    }
    out
}

/// Commit a fixed-length short ring witness $\mathbf{w} \in R_{q_{\text{lat}}}^n$.
/// Strictly enforces `witness.len() == params.cols` (defeating `F1` trailing-limb truncation!).
pub fn commit_ring_witness(
    params: &LatticeParams,
    witness: &[RingElem],
) -> Result<LatticeCommitment, LatticeError> {
    if witness.len() != params.cols {
        return Err(LatticeError::WitnessLengthMismatch {
            expected: params.cols,
            actual: witness.len(),
        });
    }
    let syndrome = mat_vec_mul_submatrix(params.rows, params.cols, &params.matrix, witness);
    Ok(LatticeCommitment {
        cols: params.cols as u32,
        syndrome,
    })
}

/// `Akita` (`2026/1983`) / `Twist & Shout` $O(m)$ sparse one-hot commitment:
/// commits to standard basis unit $e_{\text{col}} \cdot X^{\text{slot}}$ using **0 multiplications**!
pub fn commit_one_hot_ring(
    params: &LatticeParams,
    col: usize,
    slot: usize,
) -> Result<LatticeCommitment, LatticeError> {
    if col >= params.cols {
        return Err(LatticeError::OutOfBoundsColumn {
            col,
            cols: params.cols,
        });
    }
    if slot >= RING_DEGREE {
        return Err(LatticeError::OutOfBoundsSlot { slot });
    }
    let mut syndrome = Vec::with_capacity(params.rows);
    for r in 0..params.rows {
        let entry = &params.matrix[r * params.cols + col];
        syndrome.push(entry.mul_signed_monomial(1, slot));
    }
    Ok(LatticeCommitment {
        cols: params.cols as u32,
        syndrome,
    })
}

/// Pack canonical 64-bit `Goldilocks` scalars into base-$2^{16}$ short `RingElem`s
/// (16 scalars = 64 limbs $\in [0, 65535]$ per `RingElem`), padded to `target_cols` ($\ge 2$ power of two).
pub fn pack_goldilocks_to_ring_witness(
    scalars: &[Goldilocks],
    target_cols: usize,
) -> Result<Vec<RingElem>, LatticeError> {
    let min_rings = (scalars.len() * 4).div_ceil(RING_DEGREE).max(1);
    if !target_cols.is_power_of_two() || target_cols < min_rings {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: 1,
            cols: target_cols,
        });
    }
    let mut out = vec![RingElem::zero(); target_cols];
    for (idx, &x) in scalars.iter().enumerate() {
        let v = x.to_canonical_u64();
        let limbs = [
            (v & 0xFFFF) as i64,
            ((v >> 16) & 0xFFFF) as i64,
            ((v >> 32) & 0xFFFF) as i64,
            ((v >> 48) & 0xFFFF) as i64,
        ];
        let base_slot = idx * 4;
        let ring_idx = base_slot / RING_DEGREE;
        let coeff_off = base_slot % RING_DEGREE;
        out[ring_idx].coeffs[coeff_off..coeff_off + 4].copy_from_slice(&limbs);
    }
    Ok(out)
}

/// Unpack `num_scalars` canonical `Goldilocks` elements from base-$2^{16}$ `RingElem`s,
/// strictly validating each limb $\in [0, 65535]$ AND `CanonicalLift` (`val < p`)!
pub fn unpack_ring_witness_to_goldilocks(
    witness: &[RingElem],
    num_scalars: usize,
) -> Result<Vec<Goldilocks>, LatticeError> {
    if witness.len() * RING_DEGREE < num_scalars * 4 {
        return Err(LatticeError::WitnessLengthMismatch {
            expected: (num_scalars * 4).div_ceil(RING_DEGREE),
            actual: witness.len(),
        });
    }
    let mut out = Vec::with_capacity(num_scalars);
    for idx in 0..num_scalars {
        let base_slot = idx * 4;
        let ring_idx = base_slot / RING_DEGREE;
        let coeff_off = base_slot % RING_DEGREE;
        let mut limbs = [0u64; 4];
        for l in 0..4 {
            let raw = witness[ring_idx].coeffs[coeff_off + l];
            if !(0..=(GADGET_LIMB_MAX as i64)).contains(&raw) {
                return Err(LatticeError::InvalidGadgetLimb(raw));
            }
            limbs[l] = raw as u64;
        }
        let val = limbs[0] | (limbs[1] << 16) | (limbs[2] << 32) | (limbs[3] << 48);
        out.push(Goldilocks::from_canonical(val)?);
    }
    // All trailing slots must be zero so padding cannot smuggle shadow data
    for slot in (num_scalars * 4)..(witness.len() * RING_DEGREE) {
        let raw = witness[slot / RING_DEGREE].coeffs[slot % RING_DEGREE];
        if raw != 0 {
            return Err(LatticeError::InvalidGadgetLimb(raw));
        }
    }
    Ok(out)
}

// ============================================================================
// 4. Linear 2-to-1 Witness Folding & Recursive `Akita` Split-and-Fold Opening
// ============================================================================

/// Folded witness + updated norm budget produced by `fold_witness_2_to_1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedWitnessState {
    pub witness: Vec<RingElem>,
    pub commitment: LatticeCommitment,
    pub tracked_norm_bound: u64,
}

/// Linear 2-to-1 homomorphic witness & commitment folding over $R_{q_{\text{lat}}}$ with explicit
/// $\ell_\infty$ norm guard and tracked norm budget (`F11` defense!).
pub fn fold_witness_2_to_1(
    params: &LatticeParams,
    w_left: &[RingElem],
    comm_left: &LatticeCommitment,
    w_right: &[RingElem],
    comm_right: &LatticeCommitment,
    challenge: &RingElem,
    input_norm_bound: u64,
) -> Result<FoldedWitnessState, LatticeError> {
    if w_left.len() != params.cols || w_right.len() != params.cols {
        return Err(LatticeError::WitnessLengthMismatch {
            expected: params.cols,
            actual: w_left.len().min(w_right.len()),
        });
    }
    let norm_l = max_witness_norm_inf(w_left);
    if norm_l > input_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: norm_l,
            bound: input_norm_bound,
        });
    }
    let norm_r = max_witness_norm_inf(w_right);
    if norm_r > input_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: norm_r,
            bound: input_norm_bound,
        });
    }

    let chal_l1 = challenge.norm_l1();
    let next_bound = input_norm_bound.saturating_add(chal_l1.saturating_mul(input_norm_bound));
    if next_bound > MAX_SAFE_SIS_NORM {
        return Err(LatticeError::NormBudgetOverflow {
            next_bound,
            ceiling: MAX_SAFE_SIS_NORM,
        });
    }

    let mut folded_w = Vec::with_capacity(params.cols);
    for (wl, wr) in w_left.iter().zip(w_right.iter()) {
        folded_w.push(wl.add(&challenge.mul(wr)));
    }
    let mut folded_syn = Vec::with_capacity(params.rows);
    for (sl, sr) in comm_left.syndrome.iter().zip(comm_right.syndrome.iter()) {
        folded_syn.push(sl.add(&challenge.mul(sr)));
    }

    Ok(FoldedWitnessState {
        witness: folded_w,
        commitment: LatticeCommitment {
            cols: params.cols as u32,
            syndrome: folded_syn,
        },
        tracked_norm_bound: next_bound,
    })
}

/// One recursive split-and-fold round in an `Akita` (`2026/1983`) MSIS opening proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AkitaFoldRound {
    pub t_ll: Vec<RingElem>,
    pub t_mid: Vec<RingElem>,
    pub t_rr: Vec<RingElem>,
    pub k_ll: RingElem,
    pub k_mid: RingElem,
    pub k_rr: RingElem,
}

/// Complete `Akita` (`2026/1983`) + `PikkuFold` (`2026/1809`) recursive split-and-fold MSIS proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AkitaFoldProof {
    pub initial_norm_bound: u64,
    /// 0-mul Kronecker ternary projection $y_{\text{kron}} = \langle \bigotimes c_j, \mathbf{w} \rangle$.
    pub kronecker_projection: RingElem,
    /// $\log_2(\text{cols})$ split-and-fold cross-commitment rounds.
    pub rounds: Vec<AkitaFoldRound>,
    /// Final dimension-1 folded witness element $w_{\text{final}} \in R_{q_{\text{lat}}}$.
    pub final_witness: RingElem,
}

fn squeeze_kronecker_pairs(
    tr: &mut FenziTranscript<InstanceBound>,
    log_cols: usize,
) -> Vec<[TernaryTrit; 2]> {
    if log_cols == 0 {
        return Vec::new();
    }
    let raw = tr.squeeze_ternary_trits(2 * log_cols);
    let mut pairs = Vec::with_capacity(log_cols);
    for i in 0..log_cols {
        let mut t0 = TernaryTrit::from_i8(raw[2 * i]).unwrap();
        let t1 = TernaryTrit::from_i8(raw[2 * i + 1]).unwrap();
        // Ensure every pair is non-trivial so Kronecker projection never collapses to identically 0
        if t0 == TernaryTrit::Zero && t1 == TernaryTrit::Zero {
            t0 = TernaryTrit::PosOne;
        }
        pairs.push([t0, t1]);
    }
    pairs
}

fn absorb_akita_round(tr: &mut FenziTranscript<InstanceBound>, rnd: &AkitaFoldRound) {
    let mut buf = Vec::with_capacity((3 * rnd.t_ll.len() + 3) * RING_DEGREE * 8);
    for v in &rnd.t_ll {
        buf.extend_from_slice(&v.to_be_bytes());
    }
    for v in &rnd.t_mid {
        buf.extend_from_slice(&v.to_be_bytes());
    }
    for v in &rnd.t_rr {
        buf.extend_from_slice(&v.to_be_bytes());
    }
    buf.extend_from_slice(&rnd.k_ll.to_be_bytes());
    buf.extend_from_slice(&rnd.k_mid.to_be_bytes());
    buf.extend_from_slice(&rnd.k_rr.to_be_bytes());
    tr.absorb(AKITA_ROUND_LABEL, &buf);
}

/// Squeeze a $\ge 147$-bit canonical low-norm invertible ring challenge
/// $c \in \{-2, -1, 0, +1, +2\}^{64} \setminus \{0\}$ with positive first non-zero coefficient
/// and $\|c\|_1 \le \text{AKITA\_CHALLENGE\_MAX\_L1}$ (`96`).
///
/// By Lyubashevsky–Seiler (Eurocrypt 2018), because $Q_{\text{LAT}} \equiv 5 \pmod 8$ splits
/// $X^{64} + 1$ into two irreducible degree-32 factors and $\|c_1 \pm c_2\|_\infty \le 4 \ll \sqrt{Q_{\text{LAT}}/2}$,
/// **every** distinct pair $c_1 \ne c_2$ in this canonical half-space has BOTH $c_1 - c_2$ and $c_1 + c_2$
/// invertible in $R_{Q_{\text{LAT}}}$, giving single-round quadratic soundness $\le 4 / 2^{147.5} < 2^{-145} \ll 2^{-128}$!
pub fn squeeze_invertible_ring_challenge(tr: &mut FenziTranscript<InstanceBound>) -> RingElem {
    let seed = tr.squeeze_challenge_256();
    let mut xof = Cshake256Xof::new(AKITA_CHALLENGE_XOF_CUSTOMIZATION);
    xof.absorb(&seed);

    let mut byte = [0u8; 1];
    loop {
        let mut coeffs = [0i64; RING_DEGREE];
        let mut filled = 0usize;
        while filled < RING_DEGREE {
            xof.squeeze(&mut byte);
            let b = byte[0];
            // 2 * 5^3 = 250 < 256: extract up to 3 independent unbiased digits in {-2, -1, 0, +1, +2}
            if b < 250 {
                let mut v = b % 125;
                for _ in 0..3 {
                    if filled == RING_DEGREE {
                        break;
                    }
                    coeffs[filled] = (v % 5) as i64 - 2;
                    v /= 5;
                    filled += 1;
                }
            }
        }
        let Some(first_nz) = coeffs.iter().position(|&c| c != 0) else {
            continue;
        };
        if coeffs[first_nz] < 0 {
            for c in &mut coeffs {
                *c = -*c;
            }
        }
        let l1: u64 = coeffs.iter().map(|c| c.unsigned_abs()).sum();
        if l1 <= AKITA_CHALLENGE_MAX_L1 {
            return RingElem { coeffs };
        }
    }
}

/// Prove a short MSIS opening $A \mathbf{w} = \mathbf{t}$ with $\|\mathbf{w}\|_\infty \le \beta_0$
/// via 0-mul `PikkuFold` Kronecker ternary projection + $\log_2 n$ recursive `Akita` split-and-fold rounds!
pub fn akita_prove_open(
    params: &LatticeParams,
    witness: &[RingElem],
    initial_norm_bound: u64,
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<AkitaFoldProof, LatticeError> {
    if witness.len() != params.cols {
        return Err(LatticeError::WitnessLengthMismatch {
            expected: params.cols,
            actual: witness.len(),
        });
    }
    let actual_norm = max_witness_norm_inf(witness);
    if initial_norm_bound == 0 && actual_norm > 0 {
        return Err(LatticeError::ZeroNormBoundOnNonZeroCommitment);
    }
    if actual_norm > initial_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: actual_norm,
            bound: initial_norm_bound,
        });
    }
    let log_cols = params.cols.trailing_zeros() as usize;
    let mut worst_case_budget = initial_norm_bound;
    for _ in 0..log_cols {
        worst_case_budget = worst_case_budget.saturating_mul(1 + AKITA_CHALLENGE_MAX_L1);
        if worst_case_budget > MAX_SAFE_SIS_NORM {
            return Err(LatticeError::NormBudgetOverflow {
                next_bound: worst_case_budget,
                ceiling: MAX_SAFE_SIS_NORM,
            });
        }
    }

    // Bind `LatticeParams` digest into transcript before squeezing any challenge (`P0-04`)
    tr.absorb(AKITA_PARAMS_LABEL, &params.transcript_digest());
    tr.absorb(
        b"AKITA.INITIAL.NORM_BOUND",
        &initial_norm_bound.to_be_bytes(),
    );

    // Step 1: 0-multiplication PikkuFold Kronecker ternary projection
    let kron_pairs = squeeze_kronecker_pairs(tr, log_cols);
    let kronecker_projection = kronecker_ternary_fold_0mul(witness, &kron_pairs)?;
    tr.absorb(AKITA_KRON_LABEL, &kronecker_projection.to_be_bytes());

    let mut cur_cols = params.cols;
    let mut cur_mat = params.matrix.clone();
    let mut cur_w = witness.to_vec();
    let mut cur_kron: Vec<RingElem> = expand_kronecker_ternary(&kron_pairs)
        .into_iter()
        .map(|t| RingElem::constant(t as i64))
        .collect();

    let mut rounds = Vec::with_capacity(log_cols);

    while cur_cols > 1 {
        let half = cur_cols >> 1;
        let w_l = &cur_w[..half];
        let w_r = &cur_w[half..];

        let mut a_l = Vec::with_capacity(params.rows * half);
        let mut a_r = Vec::with_capacity(params.rows * half);
        for r in 0..params.rows {
            let off = r * cur_cols;
            a_l.extend_from_slice(&cur_mat[off..off + half]);
            a_r.extend_from_slice(&cur_mat[off + half..off + cur_cols]);
        }

        let t_ll = mat_vec_mul_submatrix(params.rows, half, &a_l, w_l);
        let t_rr = mat_vec_mul_submatrix(params.rows, half, &a_r, w_r);
        let a_l_wr = mat_vec_mul_submatrix(params.rows, half, &a_l, w_r);
        let a_r_wl = mat_vec_mul_submatrix(params.rows, half, &a_r, w_l);
        let t_mid: Vec<RingElem> = a_l_wr
            .iter()
            .zip(a_r_wl.iter())
            .map(|(x, y)| x.add(y))
            .collect();

        let k_l = &cur_kron[..half];
        let k_r = &cur_kron[half..];
        let k_ll = mat_vec_mul_submatrix(1, half, k_l, w_l)[0];
        let k_rr = mat_vec_mul_submatrix(1, half, k_r, w_r)[0];
        let k_mid = mat_vec_mul_submatrix(1, half, k_l, w_r)[0]
            .add(&mat_vec_mul_submatrix(1, half, k_r, w_l)[0]);

        let rnd = AkitaFoldRound {
            t_ll,
            t_mid,
            t_rr,
            k_ll,
            k_mid,
            k_rr,
        };
        absorb_akita_round(tr, &rnd);

        // >= 147-bit invertible low-norm ring challenge c in R_{q_lat} (`P0-04`)
        let c = squeeze_invertible_ring_challenge(tr);

        let mut next_w = Vec::with_capacity(half);
        let mut next_kron = Vec::with_capacity(half);
        for j in 0..half {
            next_w.push(w_l[j].add(&c.mul(&w_r[j])));
            next_kron.push(k_l[j].add(&c.mul(&k_r[j])));
        }

        let mut next_mat = Vec::with_capacity(params.rows * half);
        for r in 0..params.rows {
            let off_h = r * half;
            for j in 0..half {
                next_mat.push(a_l[off_h + j].add(&c.mul(&a_r[off_h + j])));
            }
        }

        rounds.push(rnd);
        cur_w = next_w;
        cur_kron = next_kron;
        cur_mat = next_mat;
        cur_cols = half;
    }

    let final_witness = cur_w[0];
    tr.absorb(AKITA_FINAL_LABEL, &final_witness.to_be_bytes());

    Ok(AkitaFoldProof {
        initial_norm_bound,
        kronecker_projection,
        rounds,
        final_witness,
    })
}

/// Verify a recursive `Akita` + `PikkuFold` MSIS opening proof against `comm`, enforcing
/// per-round commitment algebra, Kronecker projection consistency, non-degenerate zero-bound checks,
/// and tracked $\ell_\infty$ norm budget!
pub fn akita_verify_open(
    params: &LatticeParams,
    comm: &LatticeCommitment,
    max_initial_norm_bound: u64,
    proof: &AkitaFoldProof,
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<u64, LatticeError> {
    if comm.cols as usize != params.cols || comm.syndrome.len() != params.rows {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: comm.syndrome.len(),
            cols: comm.cols as usize,
        });
    }
    if proof.initial_norm_bound == 0 && !comm.syndrome.iter().all(RingElem::is_zero) {
        return Err(LatticeError::ZeroNormBoundOnNonZeroCommitment);
    }
    if proof.initial_norm_bound > max_initial_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: proof.initial_norm_bound,
            bound: max_initial_norm_bound,
        });
    }
    let log_cols = params.cols.trailing_zeros() as usize;
    if proof.rounds.len() != log_cols {
        return Err(LatticeError::AkitaRoundCountMismatch {
            expected: log_cols,
            actual: proof.rounds.len(),
        });
    }

    // Bind `LatticeParams` digest and `initial_norm_bound` symmetrically with `akita_prove_open`
    tr.absorb(AKITA_PARAMS_LABEL, &params.transcript_digest());
    tr.absorb(
        b"AKITA.INITIAL.NORM_BOUND",
        &proof.initial_norm_bound.to_be_bytes(),
    );

    let kron_pairs = squeeze_kronecker_pairs(tr, log_cols);
    let max_kron_norm = (params.cols as u64).saturating_mul(proof.initial_norm_bound);
    if proof.kronecker_projection.norm_inf() > max_kron_norm {
        return Err(LatticeError::WitnessNormExceeded {
            actual: proof.kronecker_projection.norm_inf(),
            bound: max_kron_norm,
        });
    }
    tr.absorb(AKITA_KRON_LABEL, &proof.kronecker_projection.to_be_bytes());

    let mut cur_cols = params.cols;
    let mut cur_mat = params.matrix.clone();
    let mut cur_syn = comm.syndrome.clone();
    let mut cur_kron: Vec<RingElem> = expand_kronecker_ternary(&kron_pairs)
        .into_iter()
        .map(|t| RingElem::constant(t as i64))
        .collect();
    let mut cur_k_val = proof.kronecker_projection;
    let mut tracked_norm_bound = proof.initial_norm_bound;

    for (round_idx, rnd) in proof.rounds.iter().enumerate() {
        if rnd.t_ll.len() != params.rows
            || rnd.t_mid.len() != params.rows
            || rnd.t_rr.len() != params.rows
        {
            return Err(LatticeError::AkitaCrossCommitmentSumMismatch { round: round_idx });
        }
        if tracked_norm_bound == 0
            && (!rnd.t_ll.iter().all(RingElem::is_zero)
                || !rnd.t_mid.iter().all(RingElem::is_zero)
                || !rnd.t_rr.iter().all(RingElem::is_zero)
                || !rnd.k_ll.is_zero()
                || !rnd.k_mid.is_zero()
                || !rnd.k_rr.is_zero())
        {
            return Err(LatticeError::ZeroNormBoundOnNonZeroCommitment);
        }
        // Check t_ll + t_rr == cur_syn AND k_ll + k_rr == cur_k_val
        for r in 0..params.rows {
            if rnd.t_ll[r].add(&rnd.t_rr[r]) != cur_syn[r] {
                return Err(LatticeError::AkitaCrossCommitmentSumMismatch { round: round_idx });
            }
        }
        if rnd.k_ll.add(&rnd.k_rr) != cur_k_val {
            return Err(LatticeError::AkitaKroneckerProjectionMismatch);
        }

        absorb_akita_round(tr, rnd);
        let c = squeeze_invertible_ring_challenge(tr);
        let c2 = c.mul(&c);
        let chal_l1 = c.norm_l1();

        tracked_norm_bound = tracked_norm_bound.saturating_mul(1 + chal_l1);
        if tracked_norm_bound > MAX_SAFE_SIS_NORM {
            return Err(LatticeError::NormBudgetOverflow {
                next_bound: tracked_norm_bound,
                ceiling: MAX_SAFE_SIS_NORM,
            });
        }

        let mut next_syn = Vec::with_capacity(params.rows);
        for r in 0..params.rows {
            let term_c = c.mul(&rnd.t_mid[r]);
            let term_c2 = c2.mul(&rnd.t_rr[r]);
            next_syn.push(rnd.t_ll[r].add(&term_c).add(&term_c2));
        }
        cur_k_val = rnd.k_ll.add(&c.mul(&rnd.k_mid)).add(&c2.mul(&rnd.k_rr));

        let half = cur_cols >> 1;
        let mut next_mat = Vec::with_capacity(params.rows * half);
        for r in 0..params.rows {
            let off = r * cur_cols;
            for j in 0..half {
                let al = &cur_mat[off + j];
                let ar = &cur_mat[off + half + j];
                next_mat.push(al.add(&c.mul(ar)));
            }
        }
        let mut next_kron = Vec::with_capacity(half);
        for j in 0..half {
            next_kron.push(cur_kron[j].add(&c.mul(&cur_kron[half + j])));
        }

        cur_syn = next_syn;
        cur_mat = next_mat;
        cur_kron = next_kron;
        cur_cols = half;
    }

    tr.absorb(AKITA_FINAL_LABEL, &proof.final_witness.to_be_bytes());

    // Final base check (cur_cols == 1): norm check + A_final * w_final == t_final + kron_final * w_final == k_final
    let final_norm = proof.final_witness.norm_inf();
    if final_norm > tracked_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: final_norm,
            bound: tracked_norm_bound,
        });
    }
    for r in 0..params.rows {
        if cur_mat[r].mul(&proof.final_witness) != cur_syn[r] {
            return Err(LatticeError::AkitaFinalCommitmentMismatch);
        }
    }
    if cur_kron[0].mul(&proof.final_witness) != cur_k_val {
        return Err(LatticeError::AkitaKroneckerProjectionMismatch);
    }

    Ok(tracked_norm_bound)
}

// ============================================================================
// 5. Constructive Discrepancy Witness Extractor (`SisBreak`, Closing `F1`/`F2`)
// ============================================================================

/// Concrete non-zero short Module-SIS kernel witness (`A * delta == 0 mod q_lat` with
/// `delta.len() == params.cols` and `0 < ||delta||_inf <= bound`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SisCollisionWitness {
    pub delta: Vec<RingElem>,
    pub norm_inf: u64,
    pub declared_bound: u64,
}

/// Constructively extract a fixed-length Module-SIS kernel collision $\boldsymbol{\delta} = \mathbf{w}_1 - \mathbf{w}_2$
/// from any two distinct short witnesses opening the same `LatticeCommitment` (`K6`, closing `F1`/`F2`!).
pub fn extract_sis_collision(
    params: &LatticeParams,
    w1: &[RingElem],
    w2: &[RingElem],
    per_witness_bound: u64,
) -> Result<SisCollisionWitness, LatticeError> {
    let c1 = commit_ring_witness(params, w1)?;
    let c2 = commit_ring_witness(params, w2)?;
    if c1 != c2 {
        return Err(LatticeError::CommitmentsDoNotMatch);
    }
    let n1 = max_witness_norm_inf(w1);
    let n2 = max_witness_norm_inf(w2);
    if n1 > per_witness_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: n1,
            bound: per_witness_bound,
        });
    }
    if n2 > per_witness_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: n2,
            bound: per_witness_bound,
        });
    }
    if w1 == w2 {
        return Err(LatticeError::NoCollisionWitnessIsIdentical);
    }

    let delta: Vec<RingElem> = w1.iter().zip(w2.iter()).map(|(a, b)| a.sub(b)).collect();
    let norm_inf = max_witness_norm_inf(&delta);
    let declared_bound = per_witness_bound.saturating_mul(2);

    let ker_check = commit_ring_witness(params, &delta)?;
    if !ker_check.syndrome.iter().all(RingElem::is_zero) {
        return Err(LatticeError::ExtractedVectorNotInKernel);
    }

    Ok(SisCollisionWitness {
        delta,
        norm_inf,
        declared_bound,
    })
}

// ============================================================================
// 6. Salted Zero-Knowledge `commit_private_order` + `SameOpening` Dark Bazaar (`K7`)
// ============================================================================

const BAZAAR_CANOPY_BIND_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.CANOPY_BIND/v1";
const BAZAAR_LAT_BLIND_EXT_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.LAT_BLIND_EXT/v1";
const BAZAAR_R1CS_CRS_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.R1CS_CRS/v1";
const BAZAAR_BDLOP_CRS_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.BDLOP_CRS/v1";
const BAZAAR_PROVER_MASK_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.ZK_MASK/v1";
const BAZAAR_GATE_LAMBDA_CUSTOMIZATION: &[u8] = b"OBEND.DARKBAZAAR.GATE_LAMBDA/v1";

const BAZAAR_COMMIT_PHASE_LABEL: &[u8] = b"DARKBAZAAR.R1CS.COMMIT";
const BAZAAR_ZK_ROUND_LABEL: &[u8] = b"DARKBAZAAR.ZK.ROUND";
const BAZAAR_AKITA_ROUND0_LABEL: &[u8] = b"DARKBAZAAR.AKITA.ROUND0";

/// Number of parallel/sequential Fiat–Shamir R1CS Sigma rounds (`(2/256)^19 = 2^-133 < 2^-128`).
pub const BAZAAR_ZK_ROUNDS: usize = 19;

/// Number of independent $\mathbb{F}_{q_{\text{lat}}}$ quadratic-gate batching streams (`q_lat^-3 < 2^-179`).
const BAZAAR_LAMBDA_STREAMS: usize = 3;

/// R1CS commitment width (`32 * 64 = 2048` slots: `0..944` witness, `944..960` zero,
/// `960..2048` = `1088` independent 16-bit blinding scalars giving `> 9700` bits of LHL surplus entropy).
const BAZAAR_R1CS_ROWS: usize = 2;
const BAZAAR_R1CS_COLS: usize = 32;
const BAZAAR_R1CS_MSG_SLOTS: usize = 15 * RING_DEGREE; // 960
const BAZAAR_R1CS_USED_SLOTS: usize = 944;
const BAZAAR_BATCH_USED_SLOTS: usize = 7 * 32; // 224 bits for 7 limb carries

/// BDLOP cross-term commitment dimensions (`rows = 3`: 2 MSIS binding rows + 1 message row;
/// `cols = 16`: `1024 * 16 = 16,384` bits of uniform blinding entropy over `11,520`-bit output).
const BAZAAR_BDLOP_ROWS: usize = 3;
const BAZAAR_BDLOP_COLS: usize = 16;

/// Lyubashevsky rejection-sampling bounds for R1CS / batch / BDLOP openings (`|e * w| < 2^24`).
const BAZAAR_MASK_HALF_WIDTH: i64 = 1i64 << 44;
const BAZAAR_Z_MAX: i64 = BAZAAR_MASK_HALF_WIDTH - (1i64 << 24);

/// Side of a Dark Bazaar limit order (`Obend.Judge.Side`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrderSide {
    Bid,
    Ask,
}

impl OrderSide {
    #[inline]
    pub const fn tag_u64(self) -> u64 {
        match self {
            Self::Bid => 0,
            Self::Ask => 1,
        }
    }

    #[inline]
    pub const fn flow_sign(self) -> i128 {
        match self {
            Self::Bid => 1,
            Self::Ask => -1,
        }
    }
}

/// Dual-track cryptographic hiding salt for `commit_private_order` (`K7`, defeating `F6`
/// $2^{16}$ dictionary & linear meet-in-the-middle attacks across BOTH tracks!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderSalt {
    /// 256-bit `Canopy` column salt derivation seed (Track H hiding).
    pub canopy_salt_seed: [u8; 32],
    /// Short BDLOP-style lattice blinding polynomial $\mathbf{r}_{\text{blind}} \in R_{q_{\text{lat}}}$
    /// with $\|\mathbf{r}_{\text{blind}}\|_\infty \le 65535$ placed in column 1 of $A = [A_{\text{msg}} \mid A_{\text{blind}}]$.
    pub lattice_blinding: RingElem,
}

impl OrderSalt {
    /// Deterministically derive a fresh `OrderSalt` from 32 bytes of OS/caller entropy.
    pub fn from_entropy(entropy: [u8; 32]) -> Self {
        let mut xof = Cshake256Xof::new(b"OBEND.DARKBAZAAR.ORDERSALT/v1");
        xof.absorb(&entropy);
        let mut canopy_salt_seed = [0u8; 32];
        xof.squeeze(&mut canopy_salt_seed);
        let mut raw_coeffs = [0i64; RING_DEGREE];
        let mut b2 = [0u8; 2];
        for c in &mut raw_coeffs {
            xof.squeeze(&mut b2);
            *c = u16::from_le_bytes(b2) as i64; // in [0, 65535], matching 16-bit gadget norm!
        }
        Self {
            canopy_salt_seed,
            lattice_blinding: RingElem { coeffs: raw_coeffs },
        }
    }
}

/// Private `BitZ` (`2026/2141`) bit-packed order witness + hiding `OrderSalt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateOrderWitness {
    pub qty_bits: Vec<bool>,
    pub total_bits: Vec<bool>,
    pub salt: OrderSalt,
}

/// Little-endian boolean bit-packing $\sum_i b_i 2^i$ (`Obend.Crypto.SameOpening.bitsToNat`).
pub fn bits_to_u64(bits: &[bool]) -> Result<u64, LatticeError> {
    if bits.len() > 63 {
        return Err(LatticeError::MaxBitsExceedsCanonical63(bits.len() as u32));
    }
    let mut acc = 0u64;
    for (i, &b) in bits.iter().enumerate() {
        if b {
            acc |= 1u64 << i;
        }
    }
    Ok(acc)
}

impl PrivateOrderWitness {
    pub fn qty(&self) -> Result<u64, LatticeError> {
        bits_to_u64(&self.qty_bits)
    }

    pub fn total(&self) -> Result<u64, LatticeError> {
        bits_to_u64(&self.total_bits)
    }
}

/// Public on-chain / query specification of a salted dual-committed Dark Bazaar private order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedPrivateOrder {
    pub account_id: u64,
    pub side: OrderSide,
    pub max_bits: u32,
    pub canopy_comm: CanopyCommitment,
    pub lattice_comm: LatticeCommitment,
}

impl CommittedPrivateOrder {
    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(128);
        out.extend_from_slice(&self.account_id.to_be_bytes());
        out.push(self.side.tag_u64() as u8);
        out.extend_from_slice(&self.max_bits.to_be_bytes());
        out.extend_from_slice(&self.canopy_comm.to_transcript_bytes());
        out.extend_from_slice(&self.lattice_comm.to_transcript_bytes());
        out
    }
}

fn derive_canopy_bind_limbs(
    account_id: u64,
    side: OrderSide,
    max_bits: u32,
    qty_val: u64,
    tot_val: u64,
    canopy_salt_seed: &[u8; 32],
) -> [Goldilocks; 2] {
    let mut xof = Cshake256Xof::new(BAZAAR_CANOPY_BIND_CUSTOMIZATION);
    xof.absorb(&account_id.to_be_bytes());
    xof.absorb(&[side.tag_u64() as u8]);
    xof.absorb(&max_bits.to_be_bytes());
    xof.absorb(&qty_val.to_be_bytes());
    xof.absorb(&tot_val.to_be_bytes());
    xof.absorb(canopy_salt_seed);
    let mut b0 = [0u8; 8];
    let mut b1 = [0u8; 8];
    xof.squeeze(&mut b0);
    xof.squeeze(&mut b1);
    // Mask to 63 bits (< GOLDILOCKS_PRIME) so canonicality holds unconditionally
    let lo = u64::from_le_bytes(b0) & ((1u64 << 63) - 1);
    let hi = u64::from_le_bytes(b1) & ((1u64 << 63) - 1);
    [
        Goldilocks::from_u64_reduced(lo),
        Goldilocks::from_u64_reduced(hi),
    ]
}

#[allow(clippy::type_complexity)]
fn build_order_ring_witness_and_canopy_table(
    lattice_params: &LatticeParams,
    account_id: u64,
    side: OrderSide,
    max_bits: u32,
    witness: &PrivateOrderWitness,
) -> Result<
    (
        [Goldilocks; 4],
        [Goldilocks; 2],
        Vec<RingElem>,
        LatticeCommitment,
    ),
    LatticeError,
> {
    // Strictly cap max_bits <= 63 so 2^max_bits <= 2^63 < GOLDILOCKS_PRIME (closing `0 vs p` alias!)
    if max_bits > 63 {
        return Err(LatticeError::MaxBitsExceedsCanonical63(max_bits));
    }
    if witness.qty_bits.len() > max_bits as usize {
        return Err(LatticeError::BitWitnessLengthExceeded {
            max_bits,
            actual_len: witness.qty_bits.len(),
        });
    }
    if witness.total_bits.len() > max_bits as usize {
        return Err(LatticeError::BitWitnessLengthExceeded {
            max_bits,
            actual_len: witness.total_bits.len(),
        });
    }
    let blind_norm = witness.salt.lattice_blinding.norm_inf();
    if blind_norm > GADGET_LIMB_MAX {
        return Err(LatticeError::BlindingNormExceeded {
            actual: blind_norm,
            max_allowed: GADGET_LIMB_MAX,
        });
    }
    let lattice_cols = lattice_params.cols;
    if lattice_cols < 4 || !lattice_cols.is_power_of_two() {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: lattice_params.rows,
            cols: lattice_cols,
        });
    }

    let acc_gl = CanonicalLift::try_new(account_id)?.into_field();
    let side_gl = Goldilocks::from_canonical(side.tag_u64())?;
    let qty_val = witness.qty()?;
    let tot_val = witness.total()?;
    let qty_gl = CanonicalLift::try_new(qty_val)?.into_field();
    let tot_gl = CanonicalLift::try_new(tot_val)?.into_field();
    let bind_limbs = derive_canopy_bind_limbs(
        account_id,
        side,
        max_bits,
        qty_val,
        tot_val,
        &witness.salt.canopy_salt_seed,
    );

    // Weld `bind_limbs[0..2]` into `ring_witness[0].coeffs[16..24]` so Track H (`canopy_comm`)
    // and Track L (`lattice_comm`) are cryptographically locked to the exact same `SameOpening`!
    let secret_msg = [
        acc_gl,
        side_gl,
        qty_gl,
        tot_gl,
        bind_limbs[0],
        bind_limbs[1],
    ];
    let mut ring_witness = pack_goldilocks_to_ring_witness(&secret_msg, lattice_cols)?;
    if lattice_cols > 2 {
        let mut ext_xof = Cshake256Xof::new(BAZAAR_LAT_BLIND_EXT_CUSTOMIZATION);
        ext_xof.absorb(&witness.salt.canopy_salt_seed);
        ext_xof.absorb(&witness.salt.lattice_blinding.to_be_bytes());
        let mut b2 = [0u8; 2];
        for elem in &mut ring_witness[1..lattice_cols] {
            for coeff in &mut elem.coeffs {
                ext_xof.squeeze(&mut b2);
                *coeff = u16::from_le_bytes(b2) as i64;
            }
        }
    }

    let lattice_comm = commit_ring_witness(lattice_params, &ring_witness)?;
    let canopy_table = [acc_gl, side_gl, bind_limbs[0], bind_limbs[1]];

    Ok((canopy_table, bind_limbs, ring_witness, lattice_comm))
}

/// Commit a private Dark Bazaar order under **salted** `Canopy` (Track H) + **salted** `PikkuFold`
/// $R_{q_{\text{lat}}}$ MSIS (Track L) (`K7`, defeating `F6` dictionary & MITM recovery without
/// putting cleartext `qty` or `total` into the Track H `Canopy` table!).
pub fn commit_private_order(
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    account_id: u64,
    side: OrderSide,
    max_bits: u32,
    witness: &PrivateOrderWitness,
) -> Result<CommittedPrivateOrder, LatticeError> {
    let (canopy_table, _bind_limbs, _ring_witness, lattice_comm) =
        build_order_ring_witness_and_canopy_table(
            lattice_params,
            account_id,
            side,
            max_bits,
            witness,
        )?;
    let canopy_state = canopy_commit(
        canopy_params,
        2,
        &canopy_table,
        Some(&witness.salt.canopy_salt_seed),
    )?;

    Ok(CommittedPrivateOrder {
        account_id,
        side,
        max_bits,
        canopy_comm: canopy_state.commitment,
        lattice_comm,
    })
}

/// Multi-release `Choe–Kang–Stehlé (2026/2546)` smudging + decryption margin configuration (`F7` fix).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SmudgeBudgetConfig {
    pub noise_bound: u64,
    pub smudge_bound: u128,
    pub sec_bits: u32,
    pub num_releases: u64,
}

impl SmudgeBudgetConfig {
    /// Enforce:
    /// 1. `noise_bound > 0` and `sec_bits >= 40`
    /// 2. `num_releases >= 1`
    /// 3. Hybrid multi-query drowning: `num_releases * RING_DEGREE * noise_bound * 2^sec_bits <= smudge_bound`
    /// 4. Correctness margin: `noise_bound + smudge_bound < 2^100` (smudge cannot wrap decryption!)
    pub fn validate(&self) -> Result<(), LatticeError> {
        if self.noise_bound == 0
            || self.sec_bits < 40
            || self.sec_bits >= 120
            || self.num_releases == 0
        {
            return Err(LatticeError::UnsmudgedOrInsufficientNoiseBudget);
        }
        let scale = 1u128 << self.sec_bits;
        let required = (self.num_releases as u128)
            .checked_mul(RING_DEGREE as u128)
            .and_then(|v| v.checked_mul(self.noise_bound as u128))
            .and_then(|v| v.checked_mul(scale))
            .ok_or(LatticeError::UnsmudgedOrInsufficientNoiseBudget)?;
        if required > self.smudge_bound {
            return Err(LatticeError::UnsmudgedOrInsufficientNoiseBudget);
        }
        let total_noise = (self.noise_bound as u128).saturating_add(self.smudge_bound);
        let max_decryption_margin: u128 = 1u128 << 100;
        if total_noise >= max_decryption_margin {
            return Err(LatticeError::DecryptionMarginWrapped);
        }
        Ok(())
    }
}

/// Dark Bazaar uniform-price batch clearing market (`Obend.Judge.Market`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DarkBazaarMarket {
    pub currency_asset: u32,
    pub goods_asset: u32,
}

/// Single Lyubashevsky rejection-sampled Sigma round for the Dark Bazaar R1CS + Dual-PCS relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DarkBazaarZkRound {
    pub t_ord: Vec<LatticeCommitment>,
    pub t_r1cs: Vec<LatticeCommitment>,
    pub t_batch: LatticeCommitment,
    pub c_tau0: LatticeCommitment,
    pub c_tau1: LatticeCommitment,
    /// Schnorr/Lyubashevsky HVZK linear mask syndromes `A_lin * y mod q_lat` (`38 * n + 8` entries).
    pub u_lin: Vec<i64>,
    pub z_ord: Vec<Vec<RingElem>>,
    pub z_r1cs: Vec<Vec<RingElem>>,
    pub z_batch: Vec<RingElem>,
    pub z_bdlop: Vec<RingElem>,
}

/// Zero-knowledge per-order Dual-Track (`Canopy` + `Akita` + R1CS) proof bundle inside
/// `DarkBazaarSameOpeningProof` (`0` cleartext witness bits or salts!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderDualOpeningProof {
    /// Salted PRF binding limbs `[bind_lo, bind_hi]` committed in Track H (`Canopy`).
    pub canopy_bind_limbs: [Goldilocks; 2],
    pub eval_point: [GoldilocksExt2; 2],
    pub claimed_mle_val: GoldilocksExt2,
    pub canopy_proof: CanopyBatchedProof,
    /// Statistically hiding commitment to the 944-slot bit/range/KKT R1CS witness.
    pub r1cs_comm: LatticeCommitment,
    /// `Akita` recursive split-and-fold opening of round 0's rejection-sampled masked order witness.
    pub akita_proof: AkitaFoldProof,
}

/// Zero-knowledge KKT primal-dual zero-gap clearing certificate + Dual-Track salted order proofs (`K7`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DarkBazaarSameOpeningProof {
    pub uniform_price: u64,
    /// Matched goods quantity $f_i \ge 0$ filled for each order $i$.
    pub order_fills: Vec<u64>,
    /// Dual capacity-slack variables $s_i \ge 0$ for each order $i$.
    pub dual_slacks: Vec<u64>,
    /// LP flow-conservation dual multiplier $\mu \in \{-1, 0, +1\}$.
    pub flow_dual_mu: i8,
    pub order_openings: Vec<OrderDualOpeningProof>,
    /// Statistically hiding commitment to the 7 batch zero-gap limb carries $\gamma_0..\gamma_6$.
    pub batch_carry_comm: LatticeCommitment,
    /// `BAZAAR_ZK_ROUNDS` (`19` rounds, $\ge 132$-bit sound) zero-knowledge R1CS proof rounds.
    pub zk_rounds: Vec<DarkBazaarZkRound>,
}

#[inline]
fn order_crosses_price(side: OrderSide, qty: u64, total: u64, price: u64) -> bool {
    if qty == 0 {
        return false;
    }
    match side {
        OrderSide::Bid => (total as u128) >= (qty as u128) * (price as u128),
        OrderSide::Ask => (total as u128) <= (qty as u128) * (price as u128),
    }
}

#[inline]
fn order_strictly_crosses_price(side: OrderSide, qty: u64, total: u64, price: u64) -> bool {
    if qty == 0 {
        return false;
    }
    match side {
        OrderSide::Bid => (total as u128) > (qty as u128) * (price as u128),
        OrderSide::Ask => (total as u128) < (qty as u128) * (price as u128),
    }
}

fn check_accounts_nodup(orders: &[CommittedPrivateOrder]) -> Result<(), LatticeError> {
    if orders.len() <= 1 {
        return Ok(());
    }
    let mut ids: Vec<u64> = orders.iter().map(|o| o.account_id).collect();
    ids.sort_unstable();
    for pair in ids.windows(2) {
        if pair[0] == pair[1] {
            return Err(LatticeError::DuplicateAccountOrder(pair[0]));
        }
    }
    Ok(())
}

fn derive_bazaar_r1cs_params(
    lattice_params: &LatticeParams,
) -> Result<LatticeParams, LatticeError> {
    let seed = cshake256_32(
        BAZAAR_R1CS_CRS_CUSTOMIZATION,
        &lattice_params.transcript_digest(),
    );
    LatticeParams::expand_from_seed(seed, BAZAAR_R1CS_ROWS, BAZAAR_R1CS_COLS)
}

fn derive_bazaar_bdlop_params(
    lattice_params: &LatticeParams,
) -> Result<LatticeParams, LatticeError> {
    let seed = cshake256_32(
        BAZAAR_BDLOP_CRS_CUSTOMIZATION,
        &lattice_params.transcript_digest(),
    );
    LatticeParams::expand_from_seed(seed, BAZAAR_BDLOP_ROWS, BAZAAR_BDLOP_COLS)
}

fn ord_mask_bounds(lattice_cols: usize) -> Result<(i64, i64), LatticeError> {
    if lattice_cols < 4 || !lattice_cols.is_power_of_two() {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: 1,
            cols: lattice_cols,
        });
    }
    let log_cols = lattice_cols.trailing_zeros();
    let fold_factor = 1u64 + AKITA_CHALLENGE_MAX_L1; // 97
    let fold_mult =
        fold_factor
            .checked_pow(log_cols)
            .ok_or(LatticeError::InvalidMatrixDimensions {
                rows: 1,
                cols: lattice_cols,
            })?;
    let max_m = (MAX_SAFE_SIS_NORM / fold_mult).min(1u64 << 42) as i64;
    let secret_shift = 1i64 << 24;
    if max_m <= (1i64 << 26) {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: 1,
            cols: lattice_cols,
        });
    }
    Ok((max_m, max_m - secret_shift))
}

fn bdlop_commit_triple(
    bdlop_params: &LatticeParams,
    msg: &[i64; BAZAAR_LAMBDA_STREAMS],
    rand: &[RingElem],
) -> Result<LatticeCommitment, LatticeError> {
    let mut comm = commit_ring_witness(bdlop_params, rand)?;
    let mut msg_elem = RingElem::zero();
    for (k, &m) in msg.iter().enumerate() {
        msg_elem.coeffs[k] = center_mod_q(m as i128);
    }
    comm.syndrome[BAZAAR_BDLOP_ROWS - 1] = comm.syndrome[BAZAAR_BDLOP_ROWS - 1].add(&msg_elem);
    Ok(comm)
}

fn combine_commitments(
    t_comm: &LatticeCommitment,
    chal_e: i64,
    c_comm: &LatticeCommitment,
) -> Result<LatticeCommitment, LatticeError> {
    if t_comm.cols != c_comm.cols || t_comm.syndrome.len() != c_comm.syndrome.len() {
        return Err(LatticeError::CommitmentsDoNotMatch);
    }
    let mut syndrome = Vec::with_capacity(t_comm.syndrome.len());
    for (t_r, c_r) in t_comm.syndrome.iter().zip(c_comm.syndrome.iter()) {
        syndrome.push(t_r.add(&c_r.scalar_mul(chal_e)));
    }
    Ok(LatticeCommitment {
        cols: t_comm.cols,
        syndrome,
    })
}

#[inline]
fn sample_uniform_sym(xof: &mut Cshake256Xof, half_width: i64) -> i64 {
    debug_assert!(half_width > 0);
    let span = (half_width as u64) * 2 + 1;
    let threshold = u64::MAX - (u64::MAX % span);
    let mut buf = [0u8; 8];
    loop {
        xof.squeeze(&mut buf);
        let raw = u64::from_le_bytes(buf);
        if raw < threshold {
            return ((raw % span) as i64) - half_width;
        }
    }
}

#[inline]
fn u64_to_limbs4(val: u64) -> [i64; 4] {
    [
        (val & 0xFFFF) as i64,
        ((val >> 16) & 0xFFFF) as i64,
        ((val >> 32) & 0xFFFF) as i64,
        ((val >> 48) & 0xFFFF) as i64,
    ]
}

#[inline]
fn u128_to_limbs8(val: u128) -> [i64; 8] {
    let mut out = [0i64; 8];
    for (u, slot) in out.iter_mut().enumerate() {
        *slot = ((val >> (16 * u)) & 0xFFFF) as i64;
    }
    out
}

#[inline]
fn goldilocks_limbs4(val: Goldilocks) -> [i64; 4] {
    u64_to_limbs4(val.to_canonical_u64())
}

#[inline]
fn get_flat_slot(rings: &[RingElem], slot: usize) -> i64 {
    rings[slot / RING_DEGREE].coeffs[slot % RING_DEGREE]
}

#[inline]
fn set_flat_slot(rings: &mut [RingElem], slot: usize, val: i64) {
    rings[slot / RING_DEGREE].coeffs[slot % RING_DEGREE] = val;
}

#[inline]
fn pack_bits_slot(rings: &[RingElem], base_slot: usize, bit_count: usize) -> i64 {
    let mut acc: i128 = 0;
    for j in 0..bit_count {
        acc += (get_flat_slot(rings, base_slot + j) as i128) << j;
    }
    mod_pos_q(acc)
}

#[inline]
fn sum_slots(rings: &[RingElem], base_slot: usize, count: usize) -> i64 {
    let mut acc: i128 = 0;
    for j in 0..count {
        acc += get_flat_slot(rings, base_slot + j) as i128;
    }
    mod_pos_q(acc)
}

// Per-order R1CS slot offsets (`0..944` inside `0..960`):
const OFF_Q_LIMBS: usize = 0; // 4
const OFF_T_LIMBS: usize = 4; // 4
const OFF_Q_BITS: usize = 8; // 64
const OFF_T_BITS: usize = 72; // 64
const OFF_M_BITS: usize = 136; // 128
const OFF_M_CARRY_BITS: usize = 264; // 126 (7 * 18)
const OFF_G_FLAG: usize = 390; // 1
const OFF_W_GA: usize = 391; // 8
const OFF_V_GB: usize = 399; // 8
const OFF_U_BITS: usize = 407; // 128
const OFF_CMP_CARRIES: usize = 535; // 7
const OFF_B_POS_QTY: usize = 542; // 1
const OFF_QTY_NZ_BITS: usize = 543; // 6
const OFF_U_POS: usize = 549; // 1
const OFF_U_NZ_BITS: usize = 550; // 7
const OFF_B_CROSS: usize = 557; // 1
const OFF_B_STRICT: usize = 558; // 1
const OFF_CAP_BITS: usize = 559; // 64
const OFF_REM_BITS: usize = 623; // 64
const OFF_REM_CARRIES: usize = 687; // 3
const OFF_D_BITS: usize = 690; // 128
const OFF_D_CARRY_BITS: usize = 818; // 126 (7 * 18), ends at 944

#[inline]
fn order_ab_limbs(rings: &[RingElem], side: OrderSide, u: usize) -> (i64, i64) {
    let t_u = if u < 4 {
        get_flat_slot(rings, OFF_T_LIMBS + u)
    } else {
        0
    };
    let m_u = pack_bits_slot(rings, OFF_M_BITS + 16 * u, 16);
    match side {
        OrderSide::Bid => (t_u, m_u),
        OrderSide::Ask => (m_u, t_u),
    }
}

fn populate_order_r1cs_witness(
    ord: &CommittedPrivateOrder,
    wit: &PrivateOrderWitness,
    price: u64,
    fill: u64,
    slack: u64,
    blinding_xof: &mut Cshake256Xof,
) -> Result<(Vec<RingElem>, u128), LatticeError> {
    let qty = wit.qty()?;
    let total = wit.total()?;
    let mut rings = vec![RingElem::zero(); BAZAAR_R1CS_COLS];

    let q_limbs = u64_to_limbs4(qty);
    let t_limbs = u64_to_limbs4(total);
    for l in 0..4 {
        set_flat_slot(&mut rings, OFF_Q_LIMBS + l, q_limbs[l]);
        set_flat_slot(&mut rings, OFF_T_LIMBS + l, t_limbs[l]);
    }
    for k in 0..64 {
        set_flat_slot(&mut rings, OFF_Q_BITS + k, i64::from((qty >> k) & 1 == 1));
        set_flat_slot(&mut rings, OFF_T_BITS + k, i64::from((total >> k) & 1 == 1));
    }

    // 128-bit product M = qty * price with 7 carries of 18 bits
    let p_limbs = u64_to_limbs4(price);
    let m_val: u128 = (qty as u128) * (price as u128);
    for k in 0..128 {
        set_flat_slot(
            &mut rings,
            OFF_M_BITS + k,
            i64::from(((m_val >> k) & 1) == 1),
        );
    }
    let mut carry_m: u128 = 0;
    for u in 0..7 {
        let mut conv: u128 = carry_m;
        for a in 0..4 {
            for b in 0..4 {
                if a + b == u {
                    conv += (p_limbs[a] as u128) * (q_limbs[b] as u128);
                }
            }
        }
        let m_u = (m_val >> (16 * u)) & 0xFFFF;
        carry_m = (conv - m_u) >> 16;
        for j in 0..18 {
            set_flat_slot(
                &mut rings,
                OFF_M_CARRY_BITS + 18 * u + j,
                i64::from(((carry_m >> j) & 1) == 1),
            );
        }
    }

    // Exact 128-bit comparison between A and B
    let (a_val, b_val) = match ord.side {
        OrderSide::Bid => (total as u128, m_val),
        OrderSide::Ask => (m_val, total as u128),
    };
    let g_bool = a_val >= b_val;
    let g_flag = i64::from(g_bool);
    set_flat_slot(&mut rings, OFF_G_FLAG, g_flag);

    let a_limbs = u128_to_limbs8(a_val);
    let b_limbs = u128_to_limbs8(b_val);
    for u in 0..8 {
        set_flat_slot(&mut rings, OFF_W_GA + u, g_flag * a_limbs[u]);
        set_flat_slot(&mut rings, OFF_V_GB + u, g_flag * b_limbs[u]);
    }
    let u_val: u128 = if g_bool {
        a_val - b_val
    } else {
        b_val - a_val - 1
    };
    for k in 0..128 {
        set_flat_slot(
            &mut rings,
            OFF_U_BITS + k,
            i64::from(((u_val >> k) & 1) == 1),
        );
    }
    let lo_limbs = if g_bool { b_limbs } else { a_limbs };
    let u_limbs = u128_to_limbs8(u_val);
    let mut cmp_carry: i64 = 0;
    for u in 0..7 {
        let add_one = if u == 0 { 1 - g_flag } else { 0 };
        let sum_u = cmp_carry + lo_limbs[u] + add_one + u_limbs[u];
        cmp_carry = sum_u >> 16;
        set_flat_slot(&mut rings, OFF_CMP_CARRIES + u, cmp_carry);
    }

    // Non-zero tests for qty and U
    let s_q: u64 = (0..64).map(|k| (qty >> k) & 1).sum();
    let b_pos_qty = i64::from(s_q > 0);
    set_flat_slot(&mut rings, OFF_B_POS_QTY, b_pos_qty);
    let sq_minus = if s_q > 0 { s_q - 1 } else { 0 };
    for j in 0..6 {
        set_flat_slot(
            &mut rings,
            OFF_QTY_NZ_BITS + j,
            i64::from(((sq_minus >> j) & 1) == 1),
        );
    }

    let s_u: u64 = (0..128).map(|k| ((u_val >> k) & 1) as u64).sum();
    let u_pos = i64::from(s_u > 0);
    set_flat_slot(&mut rings, OFF_U_POS, u_pos);
    let su_minus = if s_u > 0 { s_u - 1 } else { 0 };
    for j in 0..7 {
        set_flat_slot(
            &mut rings,
            OFF_U_NZ_BITS + j,
            i64::from(((su_minus >> j) & 1) == 1),
        );
    }

    let b_cross = b_pos_qty * g_flag;
    let b_strict = b_cross * u_pos;
    set_flat_slot(&mut rings, OFF_B_CROSS, b_cross);
    set_flat_slot(&mut rings, OFF_B_STRICT, b_strict);

    let cap = if b_cross == 1 { qty } else { 0 };
    for k in 0..64 {
        set_flat_slot(
            &mut rings,
            OFF_CAP_BITS + k,
            i64::from(((cap >> k) & 1) == 1),
        );
    }

    let rem = cap.wrapping_sub(fill);
    for k in 0..64 {
        set_flat_slot(
            &mut rings,
            OFF_REM_BITS + k,
            i64::from(((rem >> k) & 1) == 1),
        );
    }
    let f_limbs = u64_to_limbs4(fill);
    let r_limbs = u64_to_limbs4(rem);
    let mut rem_carry: i64 = 0;
    for l in 0..3 {
        let s_l = rem_carry + f_limbs[l] + r_limbs[l];
        rem_carry = s_l >> 16;
        set_flat_slot(&mut rings, OFF_REM_CARRIES + l, rem_carry);
    }

    // Dual objective D_i = cap * slack
    let cap_limbs = u64_to_limbs4(cap);
    let s_limbs = u64_to_limbs4(slack);
    let d_val: u128 = (cap as u128) * (slack as u128);
    for k in 0..128 {
        set_flat_slot(
            &mut rings,
            OFF_D_BITS + k,
            i64::from(((d_val >> k) & 1) == 1),
        );
    }
    let mut carry_d: u128 = 0;
    for u in 0..7 {
        let mut conv: u128 = carry_d;
        for a in 0..4 {
            for b in 0..4 {
                if a + b == u {
                    conv += (s_limbs[a] as u128) * (cap_limbs[b] as u128);
                }
            }
        }
        let d_u = (d_val >> (16 * u)) & 0xFFFF;
        carry_d = (conv - d_u) >> 16;
        for j in 0..18 {
            set_flat_slot(
                &mut rings,
                OFF_D_CARRY_BITS + 18 * u + j,
                i64::from(((carry_d >> j) & 1) == 1),
            );
        }
    }

    // Columns 15..32: uniform 16-bit blinding scalars
    let mut b2 = [0u8; 2];
    for elem in &mut rings[15..BAZAAR_R1CS_COLS] {
        for c in &mut elem.coeffs {
            blinding_xof.squeeze(&mut b2);
            *c = u16::from_le_bytes(b2) as i64;
        }
    }

    Ok((rings, d_val))
}

fn populate_batch_carry_witness(
    d_vals: &[u128],
    primal_sum: u128,
    blinding_xof: &mut Cshake256Xof,
) -> Vec<RingElem> {
    let mut rings = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
    let pi_limbs = u128_to_limbs8(primal_sum);
    let mut carry: i128 = 0;
    for u in 0..7 {
        let mut col_sum: i128 = carry;
        for &d_i in d_vals {
            col_sum += ((d_i >> (16 * u)) & 0xFFFF) as i128;
        }
        carry = (col_sum - (pi_limbs[u] as i128)).div_euclid(1 << 16);
        let c_u64 = carry.max(0) as u64;
        for j in 0..32 {
            set_flat_slot(&mut rings, 32 * u + j, i64::from(((c_u64 >> j) & 1) == 1));
        }
    }
    let mut b2 = [0u8; 2];
    for elem in &mut rings[15..BAZAAR_R1CS_COLS] {
        for c in &mut elem.coeffs {
            blinding_xof.squeeze(&mut b2);
            *c = u16::from_le_bytes(b2) as i64;
        }
    }
    rings
}

#[inline]
fn next_lambda_triple(xof: &mut Cshake256Xof) -> [i64; BAZAAR_LAMBDA_STREAMS] {
    let mut out = [0i64; BAZAAR_LAMBDA_STREAMS];
    let mut buf = [0u8; 8];
    for slot in &mut out {
        xof.squeeze(&mut buf);
        let raw = u64::from_le_bytes(buf) & ((1u64 << 62) - 1);
        *slot = mod_pos_q(raw as i128);
    }
    out
}

#[inline]
fn accum_quad_gate(
    acc: &mut [i128; BAZAAR_LAMBDA_STREAMS],
    xof: &mut Cshake256Xof,
    a_val: i64,
    b_val: i64,
    c_val: i64,
    chal_e: i64,
) {
    let a_m = mod_pos_q(a_val as i128) as i128;
    let b_m = mod_pos_q(b_val as i128) as i128;
    let c_m = mod_pos_q(c_val as i128) as i128;
    let e_m = mod_pos_q(chal_e as i128) as i128;
    let prod = mod_pos_q(a_m * b_m) as i128;
    let ec = mod_pos_q(e_m * c_m) as i128;
    let gate_res = mod_pos_q(prod - ec) as i128;
    let lambdas = next_lambda_triple(xof);
    for k in 0..BAZAAR_LAMBDA_STREAMS {
        acc[k] = mod_pos_q(acc[k] + (lambdas[k] as i128) * gate_res) as i128;
    }
}

#[inline]
fn accum_bool_range(
    acc: &mut [i128; BAZAAR_LAMBDA_STREAMS],
    xof: &mut Cshake256Xof,
    rings: &[RingElem],
    base_slot: usize,
    count: usize,
    chal_e: i64,
) {
    for j in 0..count {
        let v = get_flat_slot(rings, base_slot + j);
        accum_quad_gate(acc, xof, v, v, v, chal_e);
    }
}

fn eval_batch_quad_residual(
    lambda_seed: &[u8; 32],
    orders: &[CommittedPrivateOrder],
    z_r1cs_all: &[Vec<RingElem>],
    z_batch: &[RingElem],
    chal_e: i64,
) -> [i64; BAZAAR_LAMBDA_STREAMS] {
    let mut xof = Cshake256Xof::new(BAZAAR_GATE_LAMBDA_CUSTOMIZATION);
    xof.absorb(lambda_seed);
    let mut acc = [0i128; BAZAAR_LAMBDA_STREAMS];

    for (ord, rings) in orders.iter().zip(z_r1cs_all.iter()) {
        // Boolean bit gates (`v * v = v`)
        accum_bool_range(&mut acc, &mut xof, rings, OFF_Q_BITS, 64, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_T_BITS, 64, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_M_BITS, 128, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_M_CARRY_BITS, 126, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_G_FLAG, 1, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_U_BITS, 128, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_CMP_CARRIES, 7, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_B_POS_QTY, 1, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_QTY_NZ_BITS, 6, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_U_POS, 1, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_U_NZ_BITS, 7, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_REM_BITS, 64, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_REM_CARRIES, 3, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_D_BITS, 128, chal_e);
        accum_bool_range(&mut acc, &mut xof, rings, OFF_D_CARRY_BITS, 126, chal_e);

        // Selector products W_u = g_i * A_u and V_u = g_i * B_u
        let g_val = get_flat_slot(rings, OFF_G_FLAG);
        for u in 0..8 {
            let (a_u, b_u) = order_ab_limbs(rings, ord.side, u);
            let w_u = get_flat_slot(rings, OFF_W_GA + u);
            let v_u = get_flat_slot(rings, OFF_V_GB + u);
            accum_quad_gate(&mut acc, &mut xof, g_val, a_u, w_u, chal_e);
            accum_quad_gate(&mut acc, &mut xof, g_val, b_u, v_u, chal_e);
        }

        // Non-zero indicator gates: b_pos_qty * S_q = S_q and u_pos * S_u = S_u
        let s_q = sum_slots(rings, OFF_Q_BITS, 64);
        let b_pos_qty = get_flat_slot(rings, OFF_B_POS_QTY);
        accum_quad_gate(&mut acc, &mut xof, b_pos_qty, s_q, s_q, chal_e);

        let s_u = sum_slots(rings, OFF_U_BITS, 128);
        let u_pos = get_flat_slot(rings, OFF_U_POS);
        accum_quad_gate(&mut acc, &mut xof, u_pos, s_u, s_u, chal_e);

        // Crossing & strict-crossing flags: b_cross = b_pos_qty * g_i, b_strict = b_cross * u_pos
        let b_cross = get_flat_slot(rings, OFF_B_CROSS);
        let b_strict = get_flat_slot(rings, OFF_B_STRICT);
        accum_quad_gate(&mut acc, &mut xof, b_pos_qty, g_val, b_cross, chal_e);
        accum_quad_gate(&mut acc, &mut xof, b_cross, u_pos, b_strict, chal_e);

        // Capacity bits: cap_bits[k] = b_cross * q_bits[k]
        for k in 0..64 {
            let q_k = get_flat_slot(rings, OFF_Q_BITS + k);
            let cap_k = get_flat_slot(rings, OFF_CAP_BITS + k);
            accum_quad_gate(&mut acc, &mut xof, b_cross, q_k, cap_k, chal_e);
        }

        // Walrasian strict-preference full-clearing gate: b_strict * sum(rem_bits) = 0!
        let sum_rem = sum_slots(rings, OFF_REM_BITS, 64);
        accum_quad_gate(&mut acc, &mut xof, b_strict, sum_rem, 0, chal_e);
    }

    // Batch carry boolean bits (`7 * 32 = 224` bits)
    accum_bool_range(
        &mut acc,
        &mut xof,
        z_batch,
        0,
        BAZAAR_BATCH_USED_SLOTS,
        chal_e,
    );

    [acc[0] as i64, acc[1] as i64, acc[2] as i64]
}

const BAZAAR_ORDER_LINEAR_EQS: usize = 38;
const BAZAAR_BATCH_LINEAR_EQS: usize = 8;

fn eval_order_linear_residuals(
    ord: &CommittedPrivateOrder,
    z_r1cs: &[RingElem],
    price: u64,
    fill: u64,
    slack: u64,
    chal_e: i64,
) -> [i64; BAZAAR_ORDER_LINEAR_EQS] {
    let mut out = [0i64; BAZAAR_ORDER_LINEAR_EQS];
    let mut pos = 0usize;

    // 1. Limb-packing of `Q_0..Q_3`, `T_0..T_3` (`8` eqs: `0..8`)
    for l in 0..4 {
        let q_pack = pack_bits_slot(z_r1cs, OFF_Q_BITS + 16 * l, 16);
        let t_pack = pack_bits_slot(z_r1cs, OFF_T_BITS + 16 * l, 16);
        out[pos] = mod_pos_q(q_pack as i128 - get_flat_slot(z_r1cs, OFF_Q_LIMBS + l) as i128);
        out[pos + 1] = mod_pos_q(t_pack as i128 - get_flat_slot(z_r1cs, OFF_T_LIMBS + l) as i128);
        pos += 2;
    }

    // 2. 128-bit product M = qty * price (`8` eqs: `8..16`)
    let p_limbs = u64_to_limbs4(price);
    for u in 0..8 {
        let c_prev = if u == 0 {
            0i128
        } else {
            pack_bits_slot(z_r1cs, OFF_M_CARRY_BITS + 18 * (u - 1), 18) as i128
        };
        let c_cur = if u < 7 {
            pack_bits_slot(z_r1cs, OFF_M_CARRY_BITS + 18 * u, 18) as i128
        } else {
            0i128
        };
        let mut conv: i128 = c_prev;
        for a in 0..4 {
            for b in 0..4 {
                if a + b == u {
                    let q_b = get_flat_slot(z_r1cs, OFF_Q_LIMBS + b) as i128;
                    conv = mod_pos_q(conv + (p_limbs[a] as i128) * q_b) as i128;
                }
            }
        }
        let m_u = pack_bits_slot(z_r1cs, OFF_M_BITS + 16 * u, 16) as i128;
        let rhs = mod_pos_q(m_u + (c_cur << 16)) as i128;
        out[pos] = mod_pos_q(conv - rhs);
        pos += 1;
    }

    // 3. 128-bit exact comparison Lo + (1 - g_i) + U = Hi (`8` eqs: `16..24`)
    let g_val = get_flat_slot(z_r1cs, OFF_G_FLAG) as i128;
    for u in 0..8 {
        let (a_u, b_u) = order_ab_limbs(z_r1cs, ord.side, u);
        let w_u = get_flat_slot(z_r1cs, OFF_W_GA + u) as i128;
        let v_u = get_flat_slot(z_r1cs, OFF_V_GB + u) as i128;
        let lo_u = mod_pos_q((a_u as i128) - w_u + v_u) as i128;
        let hi_u = mod_pos_q((b_u as i128) + w_u - v_u) as i128;
        let k_prev = if u == 0 {
            0i128
        } else {
            get_flat_slot(z_r1cs, OFF_CMP_CARRIES + u - 1) as i128
        };
        let k_cur = if u < 7 {
            get_flat_slot(z_r1cs, OFF_CMP_CARRIES + u) as i128
        } else {
            0i128
        };
        let one_minus_g = if u == 0 {
            (chal_e as i128) - g_val
        } else {
            0i128
        };
        let u_limb = pack_bits_slot(z_r1cs, OFF_U_BITS + 16 * u, 16) as i128;
        let lhs = mod_pos_q(k_prev + lo_u + one_minus_g + u_limb) as i128;
        let rhs = mod_pos_q(hi_u + (k_cur << 16)) as i128;
        out[pos] = mod_pos_q(lhs - rhs);
        pos += 1;
    }

    // 4. Non-zero sum decompositions S_q - b_pos_qty and S_u - u_pos (`2` eqs: `24..26`)
    let s_q = sum_slots(z_r1cs, OFF_Q_BITS, 64) as i128;
    let b_pos_qty = get_flat_slot(z_r1cs, OFF_B_POS_QTY) as i128;
    let sq_nz = pack_bits_slot(z_r1cs, OFF_QTY_NZ_BITS, 6) as i128;
    out[pos] = mod_pos_q(s_q - b_pos_qty - sq_nz);
    pos += 1;

    let s_u = sum_slots(z_r1cs, OFF_U_BITS, 128) as i128;
    let u_pos = get_flat_slot(z_r1cs, OFF_U_POS) as i128;
    let su_nz = pack_bits_slot(z_r1cs, OFF_U_NZ_BITS, 7) as i128;
    out[pos] = mod_pos_q(s_u - u_pos - su_nz);
    pos += 1;

    // 5. Fill <= Cap (`F + R == Cap`) (`4` eqs: `26..30`)
    let f_limbs = u64_to_limbs4(fill);
    for l in 0..4 {
        let rho_prev = if l == 0 {
            0i128
        } else {
            get_flat_slot(z_r1cs, OFF_REM_CARRIES + l - 1) as i128
        };
        let rho_cur = if l < 3 {
            get_flat_slot(z_r1cs, OFF_REM_CARRIES + l) as i128
        } else {
            0i128
        };
        let r_l = pack_bits_slot(z_r1cs, OFF_REM_BITS + 16 * l, 16) as i128;
        let cap_l = pack_bits_slot(z_r1cs, OFF_CAP_BITS + 16 * l, 16) as i128;
        let lhs = mod_pos_q(rho_prev + (chal_e as i128) * (f_limbs[l] as i128) + r_l) as i128;
        let rhs = mod_pos_q(cap_l + (rho_cur << 16)) as i128;
        out[pos] = mod_pos_q(lhs - rhs);
        pos += 1;
    }

    // 6. 128-bit dual objective product D_i = cap_i * slack_i (`8` eqs: `30..38`)
    let s_limbs = u64_to_limbs4(slack);
    for u in 0..8 {
        let c_prev = if u == 0 {
            0i128
        } else {
            pack_bits_slot(z_r1cs, OFF_D_CARRY_BITS + 18 * (u - 1), 18) as i128
        };
        let c_cur = if u < 7 {
            pack_bits_slot(z_r1cs, OFF_D_CARRY_BITS + 18 * u, 18) as i128
        } else {
            0i128
        };
        let mut conv: i128 = c_prev;
        for a in 0..4 {
            for b in 0..4 {
                if a + b == u {
                    let cap_b = pack_bits_slot(z_r1cs, OFF_CAP_BITS + 16 * b, 16) as i128;
                    conv = mod_pos_q(conv + (s_limbs[a] as i128) * cap_b) as i128;
                }
            }
        }
        let d_u = pack_bits_slot(z_r1cs, OFF_D_BITS + 16 * u, 16) as i128;
        let rhs = mod_pos_q(d_u + (c_cur << 16)) as i128;
        out[pos] = mod_pos_q(conv - rhs);
        pos += 1;
    }

    debug_assert_eq!(pos, BAZAAR_ORDER_LINEAR_EQS);
    out
}

fn eval_batch_linear_residuals(
    z_r1cs_all: &[Vec<RingElem>],
    z_batch: &[RingElem],
    primal_objective: u128,
    chal_e: i64,
) -> [i64; BAZAAR_BATCH_LINEAR_EQS] {
    let mut out = [0i64; BAZAAR_BATCH_LINEAR_EQS];
    let pi_limbs = u128_to_limbs8(primal_objective);
    for u in 0..8 {
        let gamma_prev = if u == 0 {
            0i128
        } else {
            pack_bits_slot(z_batch, 32 * (u - 1), 32) as i128
        };
        let gamma_cur = if u < 7 {
            pack_bits_slot(z_batch, 32 * u, 32) as i128
        } else {
            0i128
        };
        let mut lhs = gamma_prev;
        for z_i in z_r1cs_all {
            let d_iu = pack_bits_slot(z_i, OFF_D_BITS + 16 * u, 16) as i128;
            lhs = mod_pos_q(lhs + d_iu) as i128;
        }
        let rhs = mod_pos_q((chal_e as i128) * (pi_limbs[u] as i128) + (gamma_cur << 16)) as i128;
        out[u] = mod_pos_q(lhs - rhs);
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn verify_order_linear_r1cs(
    idx: usize,
    ord: &CommittedPrivateOrder,
    canopy_bind_limbs: &[Goldilocks; 2],
    z_ord: &[RingElem],
    z_r1cs: &[RingElem],
    expected_u_ord: &[i64],
    price: u64,
    fill: u64,
    slack: u64,
    flow_dual_mu: i8,
    chal_e: i64,
    primal_objective: u128,
) -> Result<(), LatticeError> {
    let acc_gl = CanonicalLift::try_new(ord.account_id)?.into_field();
    let side_gl = Goldilocks::from_canonical(ord.side.tag_u64())?;
    let acc_limbs = goldilocks_limbs4(acc_gl);
    let side_limbs = goldilocks_limbs4(side_gl);
    let bind0_limbs = goldilocks_limbs4(canopy_bind_limbs[0]);
    let bind1_limbs = goldilocks_limbs4(canopy_bind_limbs[1]);

    // 1. Public & cross-track `SameOpening` weld slots (`0..8` & `16..24`) + zero-padding (`24..64`) of `z_ord`
    for l in 0..4 {
        if z_ord[0].coeffs[l] != chal_e * acc_limbs[l]
            || z_ord[0].coeffs[4 + l] != chal_e * side_limbs[l]
            || z_ord[0].coeffs[16 + l] != chal_e * bind0_limbs[l]
            || z_ord[0].coeffs[20 + l] != chal_e * bind1_limbs[l]
        {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
    }
    for slot in 24..RING_DEGREE {
        if z_ord[0].coeffs[slot] != 0 {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
    }

    // 2. Exact equality of secret `(Q_0..Q_3, T_0..T_3)` between `ord.lattice_comm` and `r1cs_comm`
    for l in 0..4 {
        if get_flat_slot(z_r1cs, OFF_Q_LIMBS + l) != z_ord[0].coeffs[8 + l]
            || get_flat_slot(z_r1cs, OFF_T_LIMBS + l) != z_ord[0].coeffs[12 + l]
        {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
    }

    // 3. Bit-range bound `max_bits` (`<= 63`)
    for k in (ord.max_bits as usize)..64 {
        if get_flat_slot(z_r1cs, OFF_Q_BITS + k) != 0 || get_flat_slot(z_r1cs, OFF_T_BITS + k) != 0
        {
            return Err(LatticeError::ZeroKnowledgeRelationFailedAtOrder(idx));
        }
    }

    // 4. LP dual feasibility: if `slack_i + sign_i * flow_dual_mu < 1`, order MUST NOT cross (`b_cross == 0`)!
    let eff_slack = (slack as i128) + ord.side.flow_sign() * (flow_dual_mu as i128);
    if eff_slack < 1 && get_flat_slot(z_r1cs, OFF_B_CROSS) != 0 {
        return Err(LatticeError::NonZeroPrimalDualKktGap {
            primal: primal_objective as i128,
            dual: 0,
        });
    }

    // 5. Unused trailing witness slots `944..960` must be `0`
    for slot in BAZAAR_R1CS_USED_SLOTS..BAZAAR_R1CS_MSG_SLOTS {
        if get_flat_slot(z_r1cs, slot) != 0 {
            return Err(LatticeError::ZeroKnowledgeRelationFailedAtOrder(idx));
        }
    }

    // 6. Schnorr/Lyubashevsky HVZK linear syndrome check `A_lin * z - e * b_pub == u_lin (mod q_lat)`
    let actual_u = eval_order_linear_residuals(ord, z_r1cs, price, fill, slack, chal_e);
    if actual_u[0..26] != expected_u_ord[0..26] {
        return Err(LatticeError::ZeroKnowledgeRelationFailedAtOrder(idx));
    }
    if actual_u[26..30] != expected_u_ord[26..30] {
        return Err(LatticeError::NegativeOrExcessFillAtOrder(idx));
    }
    if actual_u[30..38] != expected_u_ord[30..38] {
        return Err(LatticeError::NonZeroPrimalDualKktGap {
            primal: primal_objective as i128,
            dual: -1,
        });
    }

    Ok(())
}

fn verify_batch_zero_gap_linear(
    z_r1cs_all: &[Vec<RingElem>],
    z_batch: &[RingElem],
    expected_u_batch: &[i64],
    primal_objective: u128,
    chal_e: i64,
) -> Result<(), LatticeError> {
    for slot in BAZAAR_BATCH_USED_SLOTS..BAZAAR_R1CS_MSG_SLOTS {
        if get_flat_slot(z_batch, slot) != 0 {
            return Err(LatticeError::NonZeroPrimalDualKktGap {
                primal: primal_objective as i128,
                dual: -1,
            });
        }
    }
    let actual_u = eval_batch_linear_residuals(z_r1cs_all, z_batch, primal_objective, chal_e);
    if actual_u.as_slice() != expected_u_batch {
        return Err(LatticeError::NonZeroPrimalDualKktGap {
            primal: primal_objective as i128,
            dual: -1,
        });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn bind_bazaar_transcript(
    vk_digest: &[u8; 32],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    orders: &[CommittedPrivateOrder],
    uniform_price: u64,
    order_fills: &[u64],
    dual_slacks: &[u64],
    flow_dual_mu: i8,
) -> FenziTranscript<InstanceBound> {
    let mut circuit_desc = Vec::with_capacity(128);
    circuit_desc.extend_from_slice(&lattice_params.transcript_digest());
    circuit_desc.push(match canopy_params.domain_kind {
        crate::canopy::DomainKind::PrimeField => 0,
        crate::canopy::DomainKind::BinaryAdditive => 1,
    });
    circuit_desc.push(match canopy_params.regime {
        crate::canopy::ProximityRegime::UniqueDecodingRadius => 0,
        crate::canopy::ProximityRegime::JohnsonBound => 1,
        crate::canopy::ProximityRegime::CapacityBound => 2,
    });
    circuit_desc.extend_from_slice(&(canopy_params.blowup_factor as u64).to_be_bytes());
    circuit_desc.extend_from_slice(&(canopy_params.num_queries as u64).to_be_bytes());
    circuit_desc.extend_from_slice(&canopy_params.coset_shift.to_be_bytes());
    circuit_desc.extend_from_slice(&market.currency_asset.to_be_bytes());
    circuit_desc.extend_from_slice(&market.goods_asset.to_be_bytes());
    circuit_desc.extend_from_slice(&smudge.noise_bound.to_be_bytes());
    circuit_desc.extend_from_slice(&smudge.smudge_bound.to_be_bytes());
    circuit_desc.extend_from_slice(&smudge.sec_bits.to_be_bytes());
    circuit_desc.extend_from_slice(&smudge.num_releases.to_be_bytes());

    let mut comm_bytes = leb128(orders.len());
    for ord in orders {
        comm_bytes.extend_from_slice(&ord.to_transcript_bytes());
    }
    comm_bytes.extend_from_slice(&uniform_price.to_be_bytes());
    comm_bytes.push(flow_dual_mu as u8);
    comm_bytes.extend_from_slice(&leb128(order_fills.len()));
    for &f in order_fills {
        comm_bytes.extend_from_slice(&f.to_be_bytes());
    }
    comm_bytes.extend_from_slice(&leb128(dual_slacks.len()));
    for &s in dual_slacks {
        comm_bytes.extend_from_slice(&s.to_be_bytes());
    }

    let price_ext = GoldilocksExt2::from_base(Goldilocks::from_u64_reduced(uniform_price));
    FenziTranscript::new(b"OBEND.DARKBAZAAR.SEED")
        .bind_relation(DARK_BAZAAR_PROTO_ID, vk_digest, &circuit_desc)
        .bind_instance(&comm_bytes, price_ext, &[])
}

fn encode_zk_round_commitments(
    t_ord: &[LatticeCommitment],
    t_r1cs: &[LatticeCommitment],
    t_batch: &LatticeCommitment,
    c_tau0: &LatticeCommitment,
    c_tau1: &LatticeCommitment,
    u_lin: &[i64],
) -> Vec<u8> {
    let mut msg = Vec::new();
    msg.extend_from_slice(&leb128(t_ord.len()));
    for c in t_ord {
        let b = c.to_transcript_bytes();
        msg.extend_from_slice(&leb128(b.len()));
        msg.extend_from_slice(&b);
    }
    msg.extend_from_slice(&leb128(t_r1cs.len()));
    for c in t_r1cs {
        let b = c.to_transcript_bytes();
        msg.extend_from_slice(&leb128(b.len()));
        msg.extend_from_slice(&b);
    }
    for c in [t_batch, c_tau0, c_tau1] {
        let b = c.to_transcript_bytes();
        msg.extend_from_slice(&leb128(b.len()));
        msg.extend_from_slice(&b);
    }
    msg.extend_from_slice(&leb128(u_lin.len()));
    for &u in u_lin {
        msg.extend_from_slice(&u.to_be_bytes());
    }
    msg
}

fn bazaar_round_challenges(
    tr: &mut FenziTranscript<InstanceBound>,
    commitments: impl IntoIterator<Item = Vec<u8>>,
) -> [i64; BAZAAR_ZK_ROUNDS] {
    // No challenge is available until every first message has been absorbed.
    for msg in commitments {
        tr.absorb(BAZAAR_ZK_ROUND_LABEL, &msg);
    }
    core::array::from_fn(|_| i64::from(tr.squeeze_challenge_256()[0]) + 1)
}

#[allow(clippy::too_many_arguments)]
fn prove_dark_bazaar_zk_unchecked(
    vk_digest: &[u8; 32],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    committed_orders: &[CommittedPrivateOrder],
    witnesses: &[PrivateOrderWitness],
    uniform_price: u64,
    order_fills: Vec<u64>,
    dual_slacks: Vec<u64>,
    flow_dual_mu: i8,
) -> Result<DarkBazaarSameOpeningProof, LatticeError> {
    let n = committed_orders.len();
    let r1cs_params = derive_bazaar_r1cs_params(lattice_params)?;
    let bdlop_params = derive_bazaar_bdlop_params(lattice_params)?;
    let (m_ord_half, z_ord_max) = ord_mask_bounds(lattice_params.cols)?;

    let mut tr = bind_bazaar_transcript(
        vk_digest,
        canopy_params,
        lattice_params,
        market,
        smudge,
        committed_orders,
        uniform_price,
        &order_fills,
        &dual_slacks,
        flow_dual_mu,
    );

    let mut mask_xof = Cshake256Xof::new(BAZAAR_PROVER_MASK_CUSTOMIZATION);
    mask_xof.absorb(tr.state());
    for wit in witnesses {
        mask_xof.absorb(&wit.qty()?.to_be_bytes());
        mask_xof.absorb(&wit.total()?.to_be_bytes());
        mask_xof.absorb(&wit.salt.canopy_salt_seed);
        mask_xof.absorb(&wit.salt.lattice_blinding.to_be_bytes());
    }

    let mut canopy_tables = Vec::with_capacity(n);
    let mut bind_limbs_vec = Vec::with_capacity(n);
    let mut ord_ring_witnesses = Vec::with_capacity(n);
    let mut r1cs_witnesses = Vec::with_capacity(n);
    let mut r1cs_comms = Vec::with_capacity(n);
    let mut d_vals = Vec::with_capacity(n);

    for (idx, (ord, wit)) in committed_orders.iter().zip(witnesses.iter()).enumerate() {
        let (table, bind_limbs, ring_wit, expected_lat) =
            build_order_ring_witness_and_canopy_table(
                lattice_params,
                ord.account_id,
                ord.side,
                ord.max_bits,
                wit,
            )?;
        if expected_lat != ord.lattice_comm {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
        let (r1cs_wit, d_val) = populate_order_r1cs_witness(
            ord,
            wit,
            uniform_price,
            order_fills[idx],
            dual_slacks[idx],
            &mut mask_xof,
        )?;
        let r1cs_comm = commit_ring_witness(&r1cs_params, &r1cs_wit)?;
        canopy_tables.push(table);
        bind_limbs_vec.push(bind_limbs);
        ord_ring_witnesses.push(ring_wit);
        r1cs_witnesses.push(r1cs_wit);
        r1cs_comms.push(r1cs_comm);
        d_vals.push(d_val);
    }

    let primal_sum: u128 = order_fills.iter().map(|&f| f as u128).sum();
    let batch_carry_wit = populate_batch_carry_witness(&d_vals, primal_sum, &mut mask_xof);
    let batch_carry_comm = commit_ring_witness(&r1cs_params, &batch_carry_wit)?;

    // Phase 1: absorb per-order PRF binding limbs + R1CS commitments + batch carry commitment
    let mut phase1_bytes = leb128(n);
    for i in 0..n {
        phase1_bytes.extend_from_slice(&bind_limbs_vec[i][0].to_be_bytes());
        phase1_bytes.extend_from_slice(&bind_limbs_vec[i][1].to_be_bytes());
        let rb = r1cs_comms[i].to_transcript_bytes();
        phase1_bytes.extend_from_slice(&leb128(rb.len()));
        phase1_bytes.extend_from_slice(&rb);
    }
    let bb = batch_carry_comm.to_transcript_bytes();
    phase1_bytes.extend_from_slice(&leb128(bb.len()));
    phase1_bytes.extend_from_slice(&bb);
    tr.absorb(BAZAAR_COMMIT_PHASE_LABEL, &phase1_bytes);

    // Phase 2: salted Track H (`Canopy`) openings over `[acc_gl, side_gl, bind_lo, bind_hi]`
    let mut canopy_eval_points = Vec::with_capacity(n);
    let mut canopy_mle_vals = Vec::with_capacity(n);
    let mut canopy_proofs = Vec::with_capacity(n);
    for i in 0..n {
        let canopy_state = canopy_commit(
            canopy_params,
            2,
            &canopy_tables[i],
            Some(&witnesses[i].salt.canopy_salt_seed),
        )?;
        if canopy_state.commitment != committed_orders[i].canopy_comm {
            return Err(LatticeError::CommitmentMismatchAtOrder(i));
        }
        let r0 = tr.squeeze_ext2();
        let r1 = tr.squeeze_ext2();
        let eval_point = [r0, r1];
        let claimed_mle_val =
            mle_eval_base_at_ext2(&canopy_tables[i], &eval_point).map_err(CanopyError::from)?;
        let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
        let tr_l_idle = tr.fork(DUAL_TRACK2_LABEL);
        let c_prf = canopy_open(canopy_params, &canopy_state, &eval_point, &mut tr_h)?;
        tr.join(&tr_h, &tr_l_idle);
        canopy_eval_points.push(eval_point);
        canopy_mle_vals.push(claimed_mle_val);
        canopy_proofs.push(c_prf);
    }

    // Phase 3: squeeze 256-bit quadratic-gate batching seed (`3` streams over F_{q_lat})
    let lambda_seed = tr.squeeze_challenge_256();

    // Phase 4: `BAZAAR_ZK_ROUNDS` rejection-sampled Sigma openings + round-0 `Akita` fold
    let mut zk_rounds = Vec::with_capacity(BAZAAR_ZK_ROUNDS);
    let mut round0_akita_proofs: Option<Vec<AkitaFoldProof>> = None;

    'batch: loop {
        zk_rounds.clear();
        let mut cand_tr = tr.clone();
        let mut candidates = Vec::with_capacity(BAZAAR_ZK_ROUNDS);
        let mut commitments = Vec::with_capacity(BAZAAR_ZK_ROUNDS);
        for _ in 0..BAZAAR_ZK_ROUNDS {
            let mut y_ord = Vec::with_capacity(n);
            let mut y_r1cs = Vec::with_capacity(n);
            let mut t_ord = Vec::with_capacity(n);
            let mut t_r1cs = Vec::with_capacity(n);

            for i in 0..n {
                let mut yo = vec![RingElem::zero(); lattice_params.cols];
                // Mask secret limbs 8..16 of col 0 and all coeffs of cols 1..lattice_cols
                for slot in 8..16 {
                    yo[0].coeffs[slot] = sample_uniform_sym(&mut mask_xof, m_ord_half);
                }
                for col in &mut yo[1..lattice_params.cols] {
                    for c in &mut col.coeffs {
                        *c = sample_uniform_sym(&mut mask_xof, m_ord_half);
                    }
                }
                let mut yr = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                // Slots 0..8 share the exact mask of `yo[0].coeffs[8..16]` (`Q_0..Q_3, T_0..T_3`)
                for l in 0..8 {
                    set_flat_slot(&mut yr, l, yo[0].coeffs[8 + l]);
                }
                for slot in 8..BAZAAR_R1CS_USED_SLOTS {
                    if slot >= OFF_Q_BITS + (committed_orders[i].max_bits as usize)
                        && slot < OFF_Q_BITS + 64
                    {
                        continue;
                    }
                    if slot >= OFF_T_BITS + (committed_orders[i].max_bits as usize)
                        && slot < OFF_T_BITS + 64
                    {
                        continue;
                    }
                    let eff_slack = (dual_slacks[i] as i128)
                        + committed_orders[i].side.flow_sign() * (flow_dual_mu as i128);
                    if slot == OFF_B_CROSS && eff_slack < 1 {
                        continue;
                    }
                    set_flat_slot(
                        &mut yr,
                        slot,
                        sample_uniform_sym(&mut mask_xof, BAZAAR_MASK_HALF_WIDTH),
                    );
                }
                for col in &mut yr[15..BAZAAR_R1CS_COLS] {
                    for c in &mut col.coeffs {
                        *c = sample_uniform_sym(&mut mask_xof, BAZAAR_MASK_HALF_WIDTH);
                    }
                }
                t_ord.push(commit_ring_witness(lattice_params, &yo)?);
                t_r1cs.push(commit_ring_witness(&r1cs_params, &yr)?);
                y_ord.push(yo);
                y_r1cs.push(yr);
            }

            let mut y_batch = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
            for slot in 0..BAZAAR_BATCH_USED_SLOTS {
                set_flat_slot(
                    &mut y_batch,
                    slot,
                    sample_uniform_sym(&mut mask_xof, BAZAAR_MASK_HALF_WIDTH),
                );
            }
            for col in &mut y_batch[15..BAZAAR_R1CS_COLS] {
                for c in &mut col.coeffs {
                    *c = sample_uniform_sym(&mut mask_xof, BAZAAR_MASK_HALF_WIDTH);
                }
            }
            let t_batch = commit_ring_witness(&r1cs_params, &y_batch)?;

            // Compute quadratic cross-terms tau_0 = P(0), tau_1 = P(1) - P(0) mod Q_LAT
            let tau0 =
                eval_batch_quad_residual(&lambda_seed, committed_orders, &y_r1cs, &y_batch, 0);
            let mut y_plus_w_r1cs = Vec::with_capacity(n);
            for i in 0..n {
                let sum_i: Vec<RingElem> = y_r1cs[i]
                    .iter()
                    .zip(r1cs_witnesses[i].iter())
                    .map(|(a, b)| a.add(b))
                    .collect();
                y_plus_w_r1cs.push(sum_i);
            }
            let y_plus_w_batch: Vec<RingElem> = y_batch
                .iter()
                .zip(batch_carry_wit.iter())
                .map(|(a, b)| a.add(b))
                .collect();
            let p1 = eval_batch_quad_residual(
                &lambda_seed,
                committed_orders,
                &y_plus_w_r1cs,
                &y_plus_w_batch,
                1,
            );
            let tau1 = [
                mod_pos_q((p1[0] as i128) - (tau0[0] as i128)),
                mod_pos_q((p1[1] as i128) - (tau0[1] as i128)),
                mod_pos_q((p1[2] as i128) - (tau0[2] as i128)),
            ];

            let mut y_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
            let mut r1_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
            let mut b2 = [0u8; 2];
            for col in 0..BAZAAR_BDLOP_COLS {
                for c_idx in 0..RING_DEGREE {
                    y_bdlop[col].coeffs[c_idx] =
                        sample_uniform_sym(&mut mask_xof, BAZAAR_MASK_HALF_WIDTH);
                    mask_xof.squeeze(&mut b2);
                    r1_bdlop[col].coeffs[c_idx] = u16::from_le_bytes(b2) as i64;
                }
            }
            let c_tau0 = bdlop_commit_triple(&bdlop_params, &tau0, &y_bdlop)?;
            let c_tau1 = bdlop_commit_triple(&bdlop_params, &tau1, &r1_bdlop)?;

            let mut u_lin =
                Vec::with_capacity(n * BAZAAR_ORDER_LINEAR_EQS + BAZAAR_BATCH_LINEAR_EQS);
            for i in 0..n {
                let u_ord = eval_order_linear_residuals(
                    &committed_orders[i],
                    &y_r1cs[i],
                    uniform_price,
                    order_fills[i],
                    dual_slacks[i],
                    0,
                );
                u_lin.extend_from_slice(&u_ord);
            }
            let u_batch = eval_batch_linear_residuals(&y_r1cs, &y_batch, primal_sum, 0);
            u_lin.extend_from_slice(&u_batch);

            commitments.push(encode_zk_round_commitments(
                &t_ord, &t_r1cs, &t_batch, &c_tau0, &c_tau1, &u_lin,
            ));

            candidates.push((
                y_ord, y_r1cs, y_batch, y_bdlop, r1_bdlop, t_ord, t_r1cs, t_batch, c_tau0, c_tau1,
                u_lin,
            ));
        }
        let challenges = bazaar_round_challenges(&mut cand_tr, commitments);
        let mut response_tr = cand_tr;
        for (
            round_idx,
            (
                (
                    y_ord,
                    y_r1cs,
                    y_batch,
                    y_bdlop,
                    r1_bdlop,
                    t_ord,
                    t_r1cs,
                    t_batch,
                    c_tau0,
                    c_tau1,
                    u_lin,
                ),
                chal_e,
            ),
        ) in candidates.into_iter().zip(challenges).enumerate()
        {
            // Lyubashevsky rejection check across all masked vectors
            let mut rejected = false;
            let mut z_ord = Vec::with_capacity(n);
            let mut z_r1cs = Vec::with_capacity(n);
            for i in 0..n {
                let mut zo = vec![RingElem::zero(); lattice_params.cols];
                for col in 0..lattice_params.cols {
                    for c_idx in 0..RING_DEGREE {
                        let val = y_ord[i][col].coeffs[c_idx]
                            + chal_e * ord_ring_witnesses[i][col].coeffs[c_idx];
                        if val.unsigned_abs() > (z_ord_max as u64) {
                            rejected = true;
                            break;
                        }
                        zo[col].coeffs[c_idx] = val;
                    }
                    if rejected {
                        break;
                    }
                }
                if rejected {
                    break;
                }
                let mut zr = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                for col in 0..BAZAAR_R1CS_COLS {
                    for c_idx in 0..RING_DEGREE {
                        let val = y_r1cs[i][col].coeffs[c_idx]
                            + chal_e * r1cs_witnesses[i][col].coeffs[c_idx];
                        if val.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                            rejected = true;
                            break;
                        }
                        zr[col].coeffs[c_idx] = val;
                    }
                    if rejected {
                        break;
                    }
                }
                if rejected {
                    break;
                }
                z_ord.push(zo);
                z_r1cs.push(zr);
            }
            if rejected {
                continue 'batch;
            }

            let mut z_batch = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
            for col in 0..BAZAAR_R1CS_COLS {
                for c_idx in 0..RING_DEGREE {
                    let val =
                        y_batch[col].coeffs[c_idx] + chal_e * batch_carry_wit[col].coeffs[c_idx];
                    if val.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                        rejected = true;
                        break;
                    }
                    z_batch[col].coeffs[c_idx] = val;
                }
                if rejected {
                    break;
                }
            }
            if rejected {
                continue 'batch;
            }

            let mut z_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
            for col in 0..BAZAAR_BDLOP_COLS {
                for c_idx in 0..RING_DEGREE {
                    let val = y_bdlop[col].coeffs[c_idx] + chal_e * r1_bdlop[col].coeffs[c_idx];
                    if val.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                        rejected = true;
                        break;
                    }
                    z_bdlop[col].coeffs[c_idx] = val;
                }
                if rejected {
                    break;
                }
            }
            if rejected {
                continue 'batch;
            }

            if round_idx == 0 {
                let mut akita_vec = Vec::with_capacity(n);
                for z_o_i in &z_ord {
                    let mut tr_akita = response_tr.fork(BAZAAR_AKITA_ROUND0_LABEL);
                    let tr_idle = response_tr.fork(DUAL_TRACK2_LABEL);
                    let ak_prf =
                        akita_prove_open(lattice_params, z_o_i, z_ord_max as u64, &mut tr_akita)?;
                    response_tr.join(&tr_akita, &tr_idle);
                    akita_vec.push(ak_prf);
                }
                round0_akita_proofs = Some(akita_vec);
            }

            zk_rounds.push(DarkBazaarZkRound {
                t_ord,
                t_r1cs,
                t_batch,
                c_tau0,
                c_tau1,
                u_lin,
                z_ord,
                z_r1cs,
                z_batch,
                z_bdlop,
            });
        }
        break;
    }

    let mut akita_iter = round0_akita_proofs.unwrap_or_default().into_iter();
    let mut order_openings = Vec::with_capacity(n);
    for ((bind_limbs, (eval_point, claimed_mle_val)), (canopy_proof, r1cs_comm)) in bind_limbs_vec
        .into_iter()
        .zip(canopy_eval_points.into_iter().zip(canopy_mle_vals))
        .zip(canopy_proofs.into_iter().zip(r1cs_comms))
    {
        let akita_proof = akita_iter
            .next()
            .ok_or(LatticeError::AkitaRoundCountMismatch {
                expected: n,
                actual: 0,
            })?;
        order_openings.push(OrderDualOpeningProof {
            canopy_bind_limbs: bind_limbs,
            eval_point,
            claimed_mle_val,
            canopy_proof,
            r1cs_comm,
            akita_proof,
        });
    }

    Ok(DarkBazaarSameOpeningProof {
        uniform_price,
        order_fills,
        dual_slacks,
        flow_dual_mu,
        order_openings,
        batch_carry_comm,
        zk_rounds,
    })
}

/// Generate a complete salted zero-knowledge `SameOpening` Dark Bazaar Dual-Track (`Canopy` + `Akita`) proof (`K7`).
#[allow(clippy::too_many_arguments)]
pub fn prove_dark_bazaar_same_opening(
    vk_digest: &[u8; 32],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    committed_orders: &[CommittedPrivateOrder],
    witnesses: &[PrivateOrderWitness],
    uniform_price: u64,
    order_fills: Vec<u64>,
    dual_slacks: Vec<u64>,
) -> Result<DarkBazaarSameOpeningProof, LatticeError> {
    ord_mask_bounds(lattice_params.cols)?;
    smudge.validate()?;
    if market.currency_asset == market.goods_asset {
        return Err(LatticeError::DuplicateOrIdenticalMarketAssets);
    }
    let n = committed_orders.len();
    if n != witnesses.len() || order_fills.len() != n || dual_slacks.len() != n {
        return Err(LatticeError::OrderWitnessCountMismatch {
            expected: n,
            actual: witnesses.len(),
        });
    }
    check_accounts_nodup(committed_orders)?;

    if n == 0 {
        let r1cs_params = derive_bazaar_r1cs_params(lattice_params)?;
        let zero_comm =
            commit_ring_witness(&r1cs_params, &vec![RingElem::zero(); BAZAAR_R1CS_COLS])?;
        let proof = DarkBazaarSameOpeningProof {
            uniform_price,
            order_fills,
            dual_slacks,
            flow_dual_mu: 0,
            order_openings: Vec::new(),
            batch_carry_comm: zero_comm,
            zk_rounds: Vec::new(),
        };
        verify_dark_bazaar_same_opening(
            vk_digest,
            canopy_params,
            lattice_params,
            market,
            smudge,
            committed_orders,
            &proof,
        )?;
        return Ok(proof);
    }

    let mut net_flow: i128 = 0;
    let mut primal_objective: i128 = 0;
    let mut dual_objective: i128 = 0;
    let mut crossing_flags = Vec::with_capacity(n);

    for (idx, (ord, wit)) in committed_orders.iter().zip(witnesses.iter()).enumerate() {
        let qty = wit.qty()?;
        let total = wit.total()?;
        let crosses = order_crosses_price(ord.side, qty, total, uniform_price);
        let strictly_crosses = order_strictly_crosses_price(ord.side, qty, total, uniform_price);
        let cap = if crosses { qty } else { 0 };
        let fill = order_fills[idx];
        let slack = dual_slacks[idx];
        if fill > cap {
            return Err(LatticeError::NegativeOrExcessFillAtOrder(idx));
        }
        if strictly_crosses && fill != cap {
            return Err(LatticeError::NonZeroPrimalDualKktGap {
                primal: fill as i128,
                dual: cap as i128,
            });
        }
        crossing_flags.push(crosses);
        net_flow += ord.side.flow_sign() * (fill as i128);
        primal_objective += fill as i128;
        dual_objective += (cap as i128) * (slack as i128);
    }

    if net_flow != 0 {
        return Err(LatticeError::FlowConservationFailed);
    }
    if primal_objective != dual_objective {
        return Err(LatticeError::NonZeroPrimalDualKktGap {
            primal: primal_objective,
            dual: dual_objective,
        });
    }

    let mut chosen_mu: Option<i8> = None;
    for cand_mu in [0i8, 1, -1] {
        let ok = committed_orders
            .iter()
            .zip(crossing_flags.iter())
            .zip(dual_slacks.iter())
            .all(|((ord, &crosses), &slack)| {
                !crosses || (slack as i128) + ord.side.flow_sign() * (cand_mu as i128) >= 1
            });
        if ok {
            chosen_mu = Some(cand_mu);
            break;
        }
    }
    let flow_dual_mu = chosen_mu.ok_or(LatticeError::NonZeroPrimalDualKktGap {
        primal: primal_objective,
        dual: dual_objective,
    })?;

    let proof = prove_dark_bazaar_zk_unchecked(
        vk_digest,
        canopy_params,
        lattice_params,
        market,
        smudge,
        committed_orders,
        witnesses,
        uniform_price,
        order_fills,
        dual_slacks,
        flow_dual_mu,
    )?;

    verify_dark_bazaar_same_opening(
        vk_digest,
        canopy_params,
        lattice_params,
        market,
        smudge,
        committed_orders,
        &proof,
    )?;
    Ok(proof)
}

/// Verify a salted zero-knowledge `SameOpening` Dark Bazaar clearing proof:
/// 1. `SmudgeBudgetConfig` (`2026/2546` drowning + decryption margin),
/// 2. Distinct market assets & $O(N \log N)$ unique account IDs (`accountsNodup`),
/// 3. Zero-knowledge `BitZ` $2^B$ range bounds & `CanonicalLift` (`< p`),
/// 4. Salted `Canopy` (Track H) + `Akita` (Track L) Dual-PCS openings bound to `FenziTranscript<InstanceBound>`,
/// 5. Exact flow conservation, Walrasian strict-crossing full clearing, LP dual feasibility, and KKT zero gap!
pub fn verify_dark_bazaar_same_opening(
    vk_digest: &[u8; 32],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    committed_orders: &[CommittedPrivateOrder],
    proof: &DarkBazaarSameOpeningProof,
) -> Result<(), LatticeError> {
    ord_mask_bounds(lattice_params.cols)?;
    smudge.validate()?;
    if market.currency_asset == market.goods_asset {
        return Err(LatticeError::DuplicateOrIdenticalMarketAssets);
    }
    let n = committed_orders.len();
    if proof.order_openings.len() != n
        || proof.order_fills.len() != n
        || proof.dual_slacks.len() != n
    {
        return Err(LatticeError::OrderWitnessCountMismatch {
            expected: n,
            actual: proof.order_openings.len(),
        });
    }
    if !(-1..=1).contains(&proof.flow_dual_mu) {
        return Err(LatticeError::NonZeroPrimalDualKktGap {
            primal: 0,
            dual: proof.flow_dual_mu as i128,
        });
    }

    // O(N log N) account uniqueness check (`accountsNodup`)
    check_accounts_nodup(committed_orders)?;

    let r1cs_params = derive_bazaar_r1cs_params(lattice_params)?;
    let bdlop_params = derive_bazaar_bdlop_params(lattice_params)?;
    let (_m_ord_half, z_ord_max) = ord_mask_bounds(lattice_params.cols)?;

    if n == 0 {
        let zero_comm =
            commit_ring_witness(&r1cs_params, &vec![RingElem::zero(); BAZAAR_R1CS_COLS])?;
        if proof.flow_dual_mu != 0
            || !proof.zk_rounds.is_empty()
            || proof.batch_carry_comm != zero_comm
        {
            return Err(LatticeError::OrderWitnessCountMismatch {
                expected: 0,
                actual: proof.zk_rounds.len(),
            });
        }
        return Ok(());
    }

    if proof.zk_rounds.len() != BAZAAR_ZK_ROUNDS {
        return Err(LatticeError::OrderWitnessCountMismatch {
            expected: BAZAAR_ZK_ROUNDS,
            actual: proof.zk_rounds.len(),
        });
    }

    let mut net_flow: i128 = 0;
    let mut primal_objective: u128 = 0;
    for (idx, ord) in committed_orders.iter().enumerate() {
        if ord.max_bits > 63 {
            return Err(LatticeError::MaxBitsExceedsCanonical63(ord.max_bits));
        }
        if !ord.canopy_comm.salted {
            return Err(CanopyError::MissingOrUnexpectedColumnSalt.into());
        }
        let fill = proof.order_fills[idx];
        net_flow = net_flow
            .checked_add(ord.side.flow_sign() * (fill as i128))
            .ok_or(LatticeError::FlowConservationFailed)?;
        primal_objective = primal_objective
            .checked_add(fill as u128)
            .ok_or(LatticeError::FlowConservationFailed)?;
    }
    if net_flow != 0 {
        return Err(LatticeError::FlowConservationFailed);
    }

    let mut tr = bind_bazaar_transcript(
        vk_digest,
        canopy_params,
        lattice_params,
        market,
        smudge,
        committed_orders,
        proof.uniform_price,
        &proof.order_fills,
        &proof.dual_slacks,
        proof.flow_dual_mu,
    );

    // Phase 1: absorb PRF binding limbs + R1CS commitments + batch carry commitment
    let mut phase1_bytes = leb128(n);
    for open in &proof.order_openings {
        phase1_bytes.extend_from_slice(&open.canopy_bind_limbs[0].to_be_bytes());
        phase1_bytes.extend_from_slice(&open.canopy_bind_limbs[1].to_be_bytes());
        let rb = open.r1cs_comm.to_transcript_bytes();
        phase1_bytes.extend_from_slice(&leb128(rb.len()));
        phase1_bytes.extend_from_slice(&rb);
    }
    let bb = proof.batch_carry_comm.to_transcript_bytes();
    phase1_bytes.extend_from_slice(&leb128(bb.len()));
    phase1_bytes.extend_from_slice(&bb);
    tr.absorb(BAZAAR_COMMIT_PHASE_LABEL, &phase1_bytes);

    // Phase 2: verify salted Track H (`Canopy`) openings over `[acc_gl, side_gl, bind_lo, bind_hi]`
    for (idx, (ord, open)) in committed_orders
        .iter()
        .zip(proof.order_openings.iter())
        .enumerate()
    {
        let acc_gl = CanonicalLift::try_new(ord.account_id)?.into_field();
        let side_gl = Goldilocks::from_canonical(ord.side.tag_u64())?;
        let table = [
            acc_gl,
            side_gl,
            open.canopy_bind_limbs[0],
            open.canopy_bind_limbs[1],
        ];
        let r0 = tr.squeeze_ext2();
        let r1 = tr.squeeze_ext2();
        if open.eval_point != [r0, r1] {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
        let actual_mle =
            mle_eval_base_at_ext2(&table, &open.eval_point).map_err(CanopyError::from)?;
        if actual_mle != open.claimed_mle_val {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }
        let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
        let tr_l_idle = tr.fork(DUAL_TRACK2_LABEL);
        canopy_verify(
            canopy_params,
            &ord.canopy_comm,
            &open.eval_point,
            open.claimed_mle_val,
            &open.canopy_proof,
            &mut tr_h,
        )?;
        tr.join(&tr_h, &tr_l_idle);
    }

    // Phase 3: squeeze quadratic-gate batching seed
    let lambda_seed = tr.squeeze_challenge_256();

    // Phase 4: verify all `BAZAAR_ZK_ROUNDS` Sigma openings + round-0 `Akita` fold
    let expected_u_lin_len = n * BAZAAR_ORDER_LINEAR_EQS + BAZAAR_BATCH_LINEAR_EQS;
    let challenges = bazaar_round_challenges(
        &mut tr,
        proof.zk_rounds.iter().map(|rnd| {
            encode_zk_round_commitments(
                &rnd.t_ord,
                &rnd.t_r1cs,
                &rnd.t_batch,
                &rnd.c_tau0,
                &rnd.c_tau1,
                &rnd.u_lin,
            )
        }),
    );
    for (round_idx, rnd) in proof.zk_rounds.iter().enumerate() {
        if rnd.t_ord.len() != n
            || rnd.t_r1cs.len() != n
            || rnd.u_lin.len() != expected_u_lin_len
            || rnd.z_ord.len() != n
            || rnd.z_r1cs.len() != n
            || rnd.z_batch.len() != BAZAAR_R1CS_COLS
            || rnd.z_bdlop.len() != BAZAAR_BDLOP_COLS
        {
            return Err(LatticeError::OrderWitnessCountMismatch {
                expected: n,
                actual: rnd.z_ord.len(),
            });
        }
        for &u_val in &rnd.u_lin {
            if !(0..Q_LAT).contains(&u_val) {
                return Err(LatticeError::ZeroKnowledgeRelationFailedAtOrder(0));
            }
        }

        let chal_e = challenges[round_idx];

        let mut combined_ord_comms = Vec::with_capacity(n);
        for idx in 0..n {
            let zo = &rnd.z_ord[idx];
            let zr = &rnd.z_r1cs[idx];
            if zo.len() != lattice_params.cols || zr.len() != BAZAAR_R1CS_COLS {
                return Err(LatticeError::WitnessLengthMismatch {
                    expected: BAZAAR_R1CS_COLS,
                    actual: zr.len(),
                });
            }
            let n_ord = max_witness_norm_inf(zo);
            if n_ord > (z_ord_max as u64) {
                return Err(LatticeError::WitnessNormExceeded {
                    actual: n_ord,
                    bound: z_ord_max as u64,
                });
            }
            let n_r1cs = max_witness_norm_inf(zr);
            if n_r1cs > (BAZAAR_Z_MAX as u64) {
                return Err(LatticeError::WitnessNormExceeded {
                    actual: n_r1cs,
                    bound: BAZAAR_Z_MAX as u64,
                });
            }

            let expected_ord =
                combine_commitments(&rnd.t_ord[idx], chal_e, &committed_orders[idx].lattice_comm)?;
            let actual_ord = commit_ring_witness(lattice_params, zo)?;
            if expected_ord != actual_ord {
                return Err(LatticeError::CommitmentMismatchAtOrder(idx));
            }

            let expected_r1cs = combine_commitments(
                &rnd.t_r1cs[idx],
                chal_e,
                &proof.order_openings[idx].r1cs_comm,
            )?;
            let actual_r1cs = commit_ring_witness(&r1cs_params, zr)?;
            if expected_r1cs != actual_r1cs {
                return Err(LatticeError::CommitmentMismatchAtOrder(idx));
            }

            let u_ord_start = idx * BAZAAR_ORDER_LINEAR_EQS;
            let u_ord_end = u_ord_start + BAZAAR_ORDER_LINEAR_EQS;
            verify_order_linear_r1cs(
                idx,
                &committed_orders[idx],
                &proof.order_openings[idx].canopy_bind_limbs,
                zo,
                zr,
                &rnd.u_lin[u_ord_start..u_ord_end],
                proof.uniform_price,
                proof.order_fills[idx],
                proof.dual_slacks[idx],
                proof.flow_dual_mu,
                chal_e,
                primal_objective,
            )?;

            combined_ord_comms.push(expected_ord);
        }

        if round_idx == 0 {
            for (idx, comb_comm) in combined_ord_comms.iter().enumerate() {
                let mut tr_akita = tr.fork(BAZAAR_AKITA_ROUND0_LABEL);
                let tr_idle = tr.fork(DUAL_TRACK2_LABEL);
                akita_verify_open(
                    lattice_params,
                    comb_comm,
                    z_ord_max as u64,
                    &proof.order_openings[idx].akita_proof,
                    &mut tr_akita,
                )?;
                tr.join(&tr_akita, &tr_idle);
            }
        }

        let n_batch = max_witness_norm_inf(&rnd.z_batch);
        if n_batch > (BAZAAR_Z_MAX as u64) {
            return Err(LatticeError::WitnessNormExceeded {
                actual: n_batch,
                bound: BAZAAR_Z_MAX as u64,
            });
        }
        let expected_batch = combine_commitments(&rnd.t_batch, chal_e, &proof.batch_carry_comm)?;
        let actual_batch = commit_ring_witness(&r1cs_params, &rnd.z_batch)?;
        if expected_batch != actual_batch {
            return Err(LatticeError::NonZeroPrimalDualKktGap {
                primal: primal_objective as i128,
                dual: -1,
            });
        }

        let u_batch_start = n * BAZAAR_ORDER_LINEAR_EQS;
        verify_batch_zero_gap_linear(
            &rnd.z_r1cs,
            &rnd.z_batch,
            &rnd.u_lin[u_batch_start..],
            primal_objective,
            chal_e,
        )?;

        let n_bdlop = max_witness_norm_inf(&rnd.z_bdlop);
        if n_bdlop > (BAZAAR_Z_MAX as u64) {
            return Err(LatticeError::WitnessNormExceeded {
                actual: n_bdlop,
                bound: BAZAAR_Z_MAX as u64,
            });
        }
        let tau_eval = eval_batch_quad_residual(
            &lambda_seed,
            committed_orders,
            &rnd.z_r1cs,
            &rnd.z_batch,
            chal_e,
        );
        let expected_bdlop = combine_commitments(&rnd.c_tau0, chal_e, &rnd.c_tau1)?;
        let actual_bdlop = bdlop_commit_triple(&bdlop_params, &tau_eval, &rnd.z_bdlop)?;
        if expected_bdlop != actual_bdlop {
            return Err(LatticeError::ZeroKnowledgeRelationFailedAtOrder(0));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canopy::{DomainKind, ProximityRegime};

    fn is_prime_u64(n: u64) -> bool {
        if n < 2 || n.is_multiple_of(2) {
            return n == 2;
        }
        let mut d = n - 1;
        let mut s = 0u32;
        while d.is_multiple_of(2) {
            d /= 2;
            s += 1;
        }
        let mod_mul = |a: u64, b: u64| -> u64 { ((a as u128 * b as u128) % (n as u128)) as u64 };
        let mod_pow = |mut base: u64, mut exp: u64| -> u64 {
            let mut res = 1u64;
            base %= n;
            while exp > 0 {
                if exp & 1 == 1 {
                    res = mod_mul(res, base);
                }
                base = mod_mul(base, base);
                exp >>= 1;
            }
            res
        };
        for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
            if a >= n {
                continue;
            }
            let mut x = mod_pow(a, d);
            if x == 1 || x == n - 1 {
                continue;
            }
            let mut composite = true;
            for _ in 0..(s - 1) {
                x = mod_mul(x, x);
                if x == n - 1 {
                    composite = false;
                    break;
                }
            }
            if composite {
                return false;
            }
        }
        true
    }

    fn to_bits_le(val: u64, len: usize) -> Vec<bool> {
        (0..len).map(|i| ((val >> i) & 1) == 1).collect()
    }

    #[test]
    fn test_cyclotomic_ring_primality_partial_splitting_and_short_invertibility() {
        assert!(is_prime_u64(Q_LAT as u64), "Q_LAT must be prime");
        assert_eq!(
            Q_LAT % 8,
            5,
            "Q_LAT == 5 mod 8 ensures exact 2-factor splitting"
        );
        assert_eq!(
            mod_pos_q((Q_LAT_ZETA as i128) * (Q_LAT_ZETA as i128)),
            Q_LAT - 1,
            "ZETA^2 == -1 mod Q_LAT"
        );

        // X^64 = -1 in R_{q_lat}
        let x1 = RingElem::one().mul_signed_monomial(1, 1);
        let x63 = RingElem::one().mul_signed_monomial(1, 63);
        assert_eq!(x1.mul(&x63), RingElem::one().neg());

        // Short challenge differences (ternary / signed monomials) are ALWAYS invertible in R_{q_lat}!
        let c1 = RingElem::one().mul_signed_monomial(1, 7);
        let c2 = RingElem::one().mul_signed_monomial(-1, 23);
        let diff = c1.sub(&c2);
        let diff_inv = diff
            .inv()
            .expect("short non-zero element must be invertible in R_{q_lat}");
        assert_eq!(diff.mul(&diff_inv), RingElem::one());

        // Arbitrary dense ternary element of norm 1 is invertible
        let mut trits = [0i64; RING_DEGREE];
        for (i, slot) in trits.iter_mut().enumerate() {
            *slot = match i % 3 {
                0 => 1,
                1 => -1,
                _ => 0,
            };
        }
        let tern = RingElem::from_coeffs(trits);
        let tern_inv = tern
            .inv()
            .expect("non-zero ternary ring element is invertible");
        assert_eq!(tern.mul(&tern_inv), RingElem::one());
    }

    #[test]
    fn test_akita_recursive_split_and_fold_and_0mul_kronecker() {
        let params = LatticeParams::expand_from_seed([0x77u8; 32], 4, 8).unwrap();
        let scalars: Vec<Goldilocks> = (0..128u64)
            .map(|i| Goldilocks::from_u64_reduced(i * 1009 + 3))
            .collect();
        let witness = pack_goldilocks_to_ring_witness(&scalars, params.cols).unwrap();
        let unpacked = unpack_ring_witness_to_goldilocks(&witness, scalars.len()).unwrap();
        assert_eq!(unpacked, scalars);

        let comm = commit_ring_witness(&params, &witness).unwrap();
        let vk = [0x33u8; 32];
        let base_tr = bind_akita_relation(
            FenziTranscript::new(b"akita-test"),
            "OBEND.AKITA.PCS/v1",
            &vk,
            &params,
            b"rows=4,cols=8",
        )
        .bind_instance(&comm.to_transcript_bytes(), GoldilocksExt2::ZERO, &[]);

        let mut p_tr = base_tr.clone();
        let proof = akita_prove_open(&params, &witness, GADGET_LIMB_MAX, &mut p_tr).unwrap();
        assert_eq!(proof.rounds.len(), 3); // log2(8) == 3

        let mut v_tr = base_tr;
        let final_budget =
            akita_verify_open(&params, &comm, GADGET_LIMB_MAX, &proof, &mut v_tr).unwrap();
        assert!(final_budget > GADGET_LIMB_MAX && final_budget <= MAX_SAFE_SIS_NORM);
        assert_eq!(p_tr.state(), v_tr.state());

        // Verify sparse one-hot agrees with dense commitment
        let mut one_hot_w = vec![RingElem::zero(); params.cols];
        one_hot_w[3] = RingElem::one().mul_signed_monomial(1, 19);
        assert_eq!(
            commit_one_hot_ring(&params, 3, 19).unwrap(),
            commit_ring_witness(&params, &one_hot_w).unwrap()
        );
    }

    #[test]
    fn test_p0_04_akita_monomial_forgery_and_zero_norm_bound_defeated() {
        let params = LatticeParams::expand_from_seed([0x51u8; 32], 2, 4).unwrap();
        let alt_params = LatticeParams::expand_from_seed([0x52u8; 32], 2, 4).unwrap();
        let target_comm = LatticeCommitment {
            cols: 4,
            syndrome: vec![
                RingElem::constant(123_456_789),
                RingElem::constant(77).mul_signed_monomial(1, 13),
            ],
        };
        let one_plus_x = RingElem::one().add(&RingElem::one().mul_signed_monomial(1, 1));
        let inv_one_plus_x = one_plus_x
            .inv()
            .expect("(1 + X) must be invertible in R_{q_lat}");
        let t_rr: Vec<RingElem> = target_comm
            .syndrome
            .iter()
            .map(|s| s.mul(&inv_one_plus_x))
            .collect();
        let t_mid: Vec<RingElem> = target_comm.syndrome.iter().map(RingElem::neg).collect();
        let t_ll: Vec<RingElem> = target_comm
            .syndrome
            .iter()
            .zip(t_rr.iter())
            .map(|(s, r)| s.sub(r))
            .collect();

        // 1. Degenerate `initial_norm_bound == 0` on non-zero commitment MUST be rejected immediately
        let zero_bound_forgery = AkitaFoldProof {
            initial_norm_bound: 0,
            kronecker_projection: RingElem::zero(),
            rounds: vec![
                AkitaFoldRound {
                    t_ll: t_ll.clone(),
                    t_mid: t_mid.clone(),
                    t_rr: t_rr.clone(),
                    k_ll: RingElem::zero(),
                    k_mid: RingElem::zero(),
                    k_rr: RingElem::zero(),
                },
                AkitaFoldRound {
                    t_ll: vec![RingElem::zero(); 2],
                    t_mid: vec![RingElem::zero(); 2],
                    t_rr: vec![RingElem::zero(); 2],
                    k_ll: RingElem::zero(),
                    k_mid: RingElem::zero(),
                    k_rr: RingElem::zero(),
                },
            ],
            final_witness: RingElem::zero(),
        };
        let mut tr0 = bind_akita_relation(
            FenziTranscript::new(b"p0-04-zero-norm"),
            "OBEND.AKITA.PCS/v1",
            &[0x11u8; 32],
            &params,
            b"",
        )
        .bind_instance(
            &target_comm.to_transcript_bytes(),
            GoldilocksExt2::ZERO,
            &[],
        );
        assert_eq!(
            akita_verify_open(
                &params,
                &target_comm,
                GADGET_LIMB_MAX,
                &zero_bound_forgery,
                &mut tr0
            ),
            Err(LatticeError::ZeroNormBoundOnNonZeroCommitment)
        );

        // 2. Classic `(t_rr = S*(1+X)^{-1}, t_mid = -S, t_ll = S - t_rr)` monomial grinding attack
        // with non-zero `initial_norm_bound = 1` across 256 distinct transcripts MUST fail 256/256 times!
        let mut grind_forgery = zero_bound_forgery;
        grind_forgery.initial_norm_bound = 1;
        for attempt in 0u32..256 {
            let mut seed_label = Vec::from(&b"p0-04-grind-"[..]);
            seed_label.extend_from_slice(&attempt.to_be_bytes());
            let mut tr = bind_akita_relation(
                FenziTranscript::new(&seed_label),
                "OBEND.AKITA.PCS/v1",
                &[0x22u8; 32],
                &params,
                b"grind",
            )
            .bind_instance(
                &target_comm.to_transcript_bytes(),
                GoldilocksExt2::ZERO,
                &[],
            );
            assert!(
                akita_verify_open(
                    &params,
                    &target_comm,
                    GADGET_LIMB_MAX,
                    &grind_forgery,
                    &mut tr
                )
                .is_err(),
                "monomial forgery succeeded on attempt {attempt}"
            );
        }

        // 3. Cross-CRS substitution (`alt_params` vs `params`) MUST fail because `LatticeParams` is bound!
        let honest_w = vec![RingElem::constant(5); 4];
        let honest_comm = commit_ring_witness(&params, &honest_w).unwrap();
        let mut p_tr = bind_akita_relation(
            FenziTranscript::new(b"crs-bind"),
            "OBEND.AKITA.PCS/v1",
            &[0x44u8; 32],
            &params,
            b"",
        )
        .bind_instance(
            &honest_comm.to_transcript_bytes(),
            GoldilocksExt2::ZERO,
            &[],
        );
        let honest_prf = akita_prove_open(&params, &honest_w, GADGET_LIMB_MAX, &mut p_tr).unwrap();
        let mut wrong_crs_tr = bind_akita_relation(
            FenziTranscript::new(b"crs-bind"),
            "OBEND.AKITA.PCS/v1",
            &[0x44u8; 32],
            &params,
            b"",
        )
        .bind_instance(
            &honest_comm.to_transcript_bytes(),
            GoldilocksExt2::ZERO,
            &[],
        );
        assert!(
            akita_verify_open(
                &alt_params,
                &honest_comm,
                GADGET_LIMB_MAX,
                &honest_prf,
                &mut wrong_crs_tr
            )
            .is_err()
        );
    }

    #[test]
    fn test_p0_05_and_p3_02_dark_bazaar_crossing_zero_fill_rejected_zk_privacy_and_nlogn_nodup() {
        let cp = CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            8,
        )
        .unwrap();
        let lp = LatticeParams::expand_from_seed([0x99u8; 32], 2, 4).unwrap();
        let market = DarkBazaarMarket {
            currency_asset: 10,
            goods_asset: 20,
        };
        let smudge = SmudgeBudgetConfig {
            noise_bound: 8,
            smudge_bound: 8u128 * 64 * 4 * (1u128 << 40),
            sec_bits: 40,
            num_releases: 4,
        };
        let vk = [0xABu8; 32];

        // Strictly crossing order book: Bid qty=12 @ limit 55 (total=660), Ask qty=12 @ limit 42 (total=504)
        let bid_wit = PrivateOrderWitness {
            qty_bits: to_bits_le(12, 16),
            total_bits: to_bits_le(660, 16),
            salt: OrderSalt::from_entropy([0x11u8; 32]),
        };
        let ask_wit = PrivateOrderWitness {
            qty_bits: to_bits_le(12, 16),
            total_bits: to_bits_le(504, 16),
            salt: OrderSalt::from_entropy([0x22u8; 32]),
        };
        let ord_bid = commit_private_order(&cp, &lp, 1001, OrderSide::Bid, 16, &bid_wit).unwrap();
        let ord_ask = commit_private_order(&cp, &lp, 1002, OrderSide::Ask, 16, &ask_wit).unwrap();
        let orders = vec![ord_bid, ord_ask];
        let witnesses = vec![bid_wit, ask_wit];

        // 1. All-zero `fills = [0, 0], slacks = [0, 0]` MUST be rejected both by `prove` AND by `verify`
        // even if a dishonest prover bypasses `prove_dark_bazaar_same_opening` pre-checks!
        assert!(matches!(
            prove_dark_bazaar_same_opening(
                &vk,
                &cp,
                &lp,
                &market,
                &smudge,
                &orders,
                &witnesses,
                48,
                vec![0, 0],
                vec![0, 0],
            ),
            Err(LatticeError::NonZeroPrimalDualKktGap { .. })
        ));

        for bad_price in [1u64, 48, 55, 1_000] {
            for bad_mu in [-1i8, 0, 1] {
                let forged_zero = prove_dark_bazaar_zk_unchecked(
                    &vk,
                    &cp,
                    &lp,
                    &market,
                    &smudge,
                    &orders,
                    &witnesses,
                    bad_price,
                    vec![0, 0],
                    vec![0, 0],
                    bad_mu,
                )
                .unwrap();
                assert!(
                    verify_dark_bazaar_same_opening(
                        &vk,
                        &cp,
                        &lp,
                        &market,
                        &smudge,
                        &orders,
                        &forged_zero
                    )
                    .is_err(),
                    "dishonest zero-fill proof passed at price={bad_price}, mu={bad_mu}"
                );
            }
        }

        // 2. Honest full clearing `fills = [12, 12], slacks = [1, 1]` at `price = 48` succeeds,
        // and `OrderDualOpeningProof` contains ZERO cleartext witness fields or Canopy table leaks!
        let valid_prf = prove_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &orders,
            &witnesses,
            48,
            vec![12, 12],
            vec![1, 1],
        )
        .unwrap();
        let mut min_mu = valid_prf.clone();
        min_mu.flow_dual_mu = i8::MIN;
        assert!(matches!(
            verify_dark_bazaar_same_opening(&vk, &cp, &lp, &market, &smudge, &orders, &min_mu),
            Err(LatticeError::NonZeroPrimalDualKktGap { .. })
        ));
        let other_market = DarkBazaarMarket {
            currency_asset: 30,
            goods_asset: 40,
        };
        let other = prove_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &other_market,
            &smudge,
            &orders,
            &witnesses,
            48,
            vec![12, 12],
            vec![1, 1],
        )
        .unwrap();
        for (left, right) in valid_prf.zk_rounds.iter().zip(&other.zk_rounds) {
            assert_ne!(left.t_ord, right.t_ord);
            assert_ne!(left.z_ord, right.z_ord);
            // Reused masks would make all blind-coordinate differences proportional to the witness.
            let (_, _, w, _) = build_order_ring_witness_and_canopy_table(
                &lp,
                1001,
                OrderSide::Bid,
                16,
                &witnesses[0],
            )
            .unwrap();
            let d0 = (left.z_ord[0][1].coeffs[0] - right.z_ord[0][1].coeffs[0]) as i128;
            assert!((1..RING_DEGREE).any(|k| {
                let dk = (left.z_ord[0][1].coeffs[k] - right.z_ord[0][1].coeffs[k]) as i128;
                d0 * (w[1].coeffs[k] as i128) != dk * (w[1].coeffs[0] as i128)
            }));
        }
        let narrow = LatticeParams::expand_from_seed([0x99; 32], 2, 2).unwrap();
        assert!(
            commit_private_order(&cp, &narrow, 1001, OrderSide::Bid, 16, &witnesses[0]).is_err()
        );
        assert!(
            prove_dark_bazaar_same_opening(
                &vk,
                &cp,
                &narrow,
                &market,
                &smudge,
                &orders,
                &witnesses,
                48,
                vec![12, 12],
                vec![1, 1]
            )
            .is_err()
        );
        assert!(
            verify_dark_bazaar_same_opening(
                &vk, &cp, &narrow, &market, &smudge, &orders, &valid_prf
            )
            .is_err()
        );
        let (_, _, wide_witness, _) =
            build_order_ring_witness_and_canopy_table(&lp, 1001, OrderSide::Bid, 16, &witnesses[0])
                .unwrap();
        for column in &wide_witness[1..] {
            assert!(column.coeffs.iter().all(|c| (0..=65535).contains(c)));
            assert!(column.coeffs.iter().any(|c| *c != 0));
        }
        // A change in the final first-message commitment changes the first challenge too.
        let round_challenges = |rounds: &[DarkBazaarZkRound]| {
            let mut transcript = bind_bazaar_transcript(
                &vk,
                &cp,
                &lp,
                &market,
                &smudge,
                &orders,
                48,
                &[12, 12],
                &[1, 1],
                0,
            );
            bazaar_round_challenges(
                &mut transcript,
                rounds.iter().map(|r| {
                    encode_zk_round_commitments(
                        &r.t_ord, &r.t_r1cs, &r.t_batch, &r.c_tau0, &r.c_tau1, &r.u_lin,
                    )
                }),
            )
        };
        let original_challenges = round_challenges(&valid_prf.zk_rounds);
        assert!(original_challenges.iter().all(|e| (1..=256).contains(e)));
        let mut changed = valid_prf.zk_rounds.clone();
        let mut changed_first = false;
        for value in 1..=16 {
            changed[BAZAAR_ZK_ROUNDS - 1].u_lin[0] = value;
            changed_first |= round_challenges(&changed)[0] != original_challenges[0];
        }
        assert!(
            changed_first,
            "later commitments must bind the first challenge"
        );

        verify_dark_bazaar_same_opening(&vk, &cp, &lp, &market, &smudge, &orders, &valid_prf)
            .unwrap();
        assert_ne!(
            valid_prf.order_openings[0].canopy_bind_limbs[0].to_canonical_u64(),
            12
        );
        assert_ne!(
            valid_prf.order_openings[0].canopy_bind_limbs[1].to_canonical_u64(),
            660
        );

        // 3. Cross-track `SameOpening` splicing (`canopy_comm` from Order A + `lattice_comm` from Order B
        // for the same `(account_id, side)`) MUST be rejected because `canopy_bind_limbs` is welded into `z_ord[0].coeffs[16..24]`!
        let alt_bid_wit = PrivateOrderWitness {
            qty_bits: to_bits_le(100, 16),
            total_bits: to_bits_le(5500, 16),
            salt: OrderSalt::from_entropy([0x33u8; 32]),
        };
        let ord_bid_alt =
            commit_private_order(&cp, &lp, 1001, OrderSide::Bid, 16, &alt_bid_wit).unwrap();
        let spliced_bid = CommittedPrivateOrder {
            account_id: 1001,
            side: OrderSide::Bid,
            max_bits: 16,
            canopy_comm: ord_bid_alt.canopy_comm,
            lattice_comm: orders[0].lattice_comm.clone(),
        };
        let spliced_orders = vec![spliced_bid, orders[1].clone()];
        assert_eq!(
            prove_dark_bazaar_same_opening(
                &vk,
                &cp,
                &lp,
                &market,
                &smudge,
                &spliced_orders,
                &witnesses,
                48,
                vec![12, 12],
                vec![1, 1],
            ),
            Err(LatticeError::CommitmentMismatchAtOrder(0))
        );

        // Even if a malicious prover bypasses honest-prover checks and constructs a 100% Fiat-Shamir-consistent
        // proof opening Track H (`Canopy`) to Order A (`alt_bid_wit`) and Track L (`Lattice` + R1CS) to Order B (`witnesses[0]`),
        // `verify_order_linear_r1cs` rejects `z_ord[0].coeffs[16..24] != chal_e * alt_bind_limbs`!
        let (alt_table, alt_bind_limbs, _, _) =
            build_order_ring_witness_and_canopy_table(&lp, 1001, OrderSide::Bid, 16, &alt_bid_wit)
                .unwrap();
        let (ord1_table, ord1_bind_limbs, ord1_ring_wit, _) =
            build_order_ring_witness_and_canopy_table(&lp, 1002, OrderSide::Ask, 16, &witnesses[1])
                .unwrap();
        let (_, _, ord0_ring_wit, _) =
            build_order_ring_witness_and_canopy_table(&lp, 1001, OrderSide::Bid, 16, &witnesses[0])
                .unwrap();
        let r1cs_params = derive_bazaar_r1cs_params(&lp).unwrap();
        let bdlop_params = derive_bazaar_bdlop_params(&lp).unwrap();
        let (m_ord_half, z_ord_max) = ord_mask_bounds(lp.cols).unwrap();
        let mut adv_xof = Cshake256Xof::new(b"ADV.SPLICE.MASK");
        let (r1cs_w0, d0) =
            populate_order_r1cs_witness(&spliced_orders[0], &witnesses[0], 48, 12, 1, &mut adv_xof)
                .unwrap();
        let (r1cs_w1, d1) =
            populate_order_r1cs_witness(&spliced_orders[1], &witnesses[1], 48, 12, 1, &mut adv_xof)
                .unwrap();
        let r1cs_c0 = commit_ring_witness(&r1cs_params, &r1cs_w0).unwrap();
        let r1cs_c1 = commit_ring_witness(&r1cs_params, &r1cs_w1).unwrap();
        let batch_w = populate_batch_carry_witness(&[d0, d1], 24, &mut adv_xof);
        let batch_c = commit_ring_witness(&r1cs_params, &batch_w).unwrap();

        let mut splice_tr = bind_bazaar_transcript(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &spliced_orders,
            48,
            &[12, 12],
            &[1, 1],
            0,
        );
        let splice_binds = [alt_bind_limbs, ord1_bind_limbs];
        let splice_r1cs_comms = [r1cs_c0.clone(), r1cs_c1.clone()];
        let mut p1 = leb128(2);
        for i in 0..2 {
            p1.extend_from_slice(&splice_binds[i][0].to_be_bytes());
            p1.extend_from_slice(&splice_binds[i][1].to_be_bytes());
            let rb = splice_r1cs_comms[i].to_transcript_bytes();
            p1.extend_from_slice(&leb128(rb.len()));
            p1.extend_from_slice(&rb);
        }
        let bb = batch_c.to_transcript_bytes();
        p1.extend_from_slice(&leb128(bb.len()));
        p1.extend_from_slice(&bb);
        splice_tr.absorb(BAZAAR_COMMIT_PHASE_LABEL, &p1);

        let splice_tables = [alt_table, ord1_table];
        let splice_salts = [
            alt_bid_wit.salt.canopy_salt_seed,
            witnesses[1].salt.canopy_salt_seed,
        ];
        let mut adv_eval_pts = Vec::new();
        let mut adv_mles = Vec::new();
        let mut adv_c_prfs = Vec::new();
        for i in 0..2 {
            let st = canopy_commit(&cp, 2, &splice_tables[i], Some(&splice_salts[i])).unwrap();
            let r0 = splice_tr.squeeze_ext2();
            let r1 = splice_tr.squeeze_ext2();
            let pt = [r0, r1];
            let mle = mle_eval_base_at_ext2(&splice_tables[i], &pt).unwrap();
            let mut tr_h = splice_tr.fork(DUAL_TRACK1_LABEL);
            let tr_l = splice_tr.fork(DUAL_TRACK2_LABEL);
            let c_prf = canopy_open(&cp, &st, &pt, &mut tr_h).unwrap();
            splice_tr.join(&tr_h, &tr_l);
            adv_eval_pts.push(pt);
            adv_mles.push(mle);
            adv_c_prfs.push(c_prf);
        }
        let lambda_seed = splice_tr.squeeze_challenge_256();
        let adv_ord_wits = [ord0_ring_wit, ord1_ring_wit];
        let adv_r1cs_wits = [r1cs_w0, r1cs_w1];
        let mut adv_rounds = Vec::new();
        let mut adv_akitas: Option<Vec<AkitaFoldProof>> = None;
        'batch: loop {
            adv_rounds.clear();
            let mut cand_tr = splice_tr.clone();
            let mut candidates = Vec::with_capacity(BAZAAR_ZK_ROUNDS);
            let mut commitments = Vec::with_capacity(BAZAAR_ZK_ROUNDS);
            for _ in 0..BAZAAR_ZK_ROUNDS {
                let mut y_ord = Vec::new();
                let mut y_r1cs = Vec::new();
                let mut t_ord = Vec::new();
                let mut t_r1cs = Vec::new();
                for _ in 0..2 {
                    let mut yo = vec![RingElem::zero(); lp.cols];
                    for slot in 8..16 {
                        yo[0].coeffs[slot] = sample_uniform_sym(&mut adv_xof, m_ord_half);
                    }
                    for col in &mut yo[1..lp.cols] {
                        for c in &mut col.coeffs {
                            *c = sample_uniform_sym(&mut adv_xof, m_ord_half);
                        }
                    }
                    let mut yr = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                    for l in 0..8 {
                        set_flat_slot(&mut yr, l, yo[0].coeffs[8 + l]);
                    }
                    for slot in 8..BAZAAR_R1CS_USED_SLOTS {
                        if (OFF_Q_BITS + 16..OFF_Q_BITS + 64).contains(&slot)
                            || (OFF_T_BITS + 16..OFF_T_BITS + 64).contains(&slot)
                        {
                            continue;
                        }
                        set_flat_slot(
                            &mut yr,
                            slot,
                            sample_uniform_sym(&mut adv_xof, BAZAAR_MASK_HALF_WIDTH),
                        );
                    }
                    for col in &mut yr[15..BAZAAR_R1CS_COLS] {
                        for c in &mut col.coeffs {
                            *c = sample_uniform_sym(&mut adv_xof, BAZAAR_MASK_HALF_WIDTH);
                        }
                    }
                    t_ord.push(commit_ring_witness(&lp, &yo).unwrap());
                    t_r1cs.push(commit_ring_witness(&r1cs_params, &yr).unwrap());
                    y_ord.push(yo);
                    y_r1cs.push(yr);
                }
                let mut y_batch = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                for slot in 0..BAZAAR_BATCH_USED_SLOTS {
                    set_flat_slot(
                        &mut y_batch,
                        slot,
                        sample_uniform_sym(&mut adv_xof, BAZAAR_MASK_HALF_WIDTH),
                    );
                }
                for col in &mut y_batch[15..BAZAAR_R1CS_COLS] {
                    for c in &mut col.coeffs {
                        *c = sample_uniform_sym(&mut adv_xof, BAZAAR_MASK_HALF_WIDTH);
                    }
                }
                let t_batch = commit_ring_witness(&r1cs_params, &y_batch).unwrap();
                let tau0 =
                    eval_batch_quad_residual(&lambda_seed, &spliced_orders, &y_r1cs, &y_batch, 0);
                let ypw_r1cs: Vec<Vec<RingElem>> = (0..2)
                    .map(|i| {
                        y_r1cs[i]
                            .iter()
                            .zip(adv_r1cs_wits[i].iter())
                            .map(|(a, b)| a.add(b))
                            .collect()
                    })
                    .collect();
                let ypw_batch: Vec<RingElem> = y_batch
                    .iter()
                    .zip(batch_w.iter())
                    .map(|(a, b)| a.add(b))
                    .collect();
                let p1_q = eval_batch_quad_residual(
                    &lambda_seed,
                    &spliced_orders,
                    &ypw_r1cs,
                    &ypw_batch,
                    1,
                );
                let tau1 = [
                    mod_pos_q((p1_q[0] as i128) - (tau0[0] as i128)),
                    mod_pos_q((p1_q[1] as i128) - (tau0[1] as i128)),
                    mod_pos_q((p1_q[2] as i128) - (tau0[2] as i128)),
                ];
                let mut y_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
                let mut r1_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
                let mut b2 = [0u8; 2];
                for col in 0..BAZAAR_BDLOP_COLS {
                    for c_idx in 0..RING_DEGREE {
                        y_bdlop[col].coeffs[c_idx] =
                            sample_uniform_sym(&mut adv_xof, BAZAAR_MASK_HALF_WIDTH);
                        adv_xof.squeeze(&mut b2);
                        r1_bdlop[col].coeffs[c_idx] = u16::from_le_bytes(b2) as i64;
                    }
                }
                let c_tau0 = bdlop_commit_triple(&bdlop_params, &tau0, &y_bdlop).unwrap();
                let c_tau1 = bdlop_commit_triple(&bdlop_params, &tau1, &r1_bdlop).unwrap();
                let mut u_lin = Vec::new();
                for i in 0..2 {
                    u_lin.extend_from_slice(&eval_order_linear_residuals(
                        &spliced_orders[i],
                        &y_r1cs[i],
                        48,
                        12,
                        1,
                        0,
                    ));
                }
                u_lin.extend_from_slice(&eval_batch_linear_residuals(&y_r1cs, &y_batch, 24, 0));
                commitments.push(encode_zk_round_commitments(
                    &t_ord, &t_r1cs, &t_batch, &c_tau0, &c_tau1, &u_lin,
                ));

                candidates.push((
                    y_ord, y_r1cs, y_batch, y_bdlop, r1_bdlop, t_ord, t_r1cs, t_batch, c_tau0,
                    c_tau1, u_lin,
                ));
            }
            let challenges = bazaar_round_challenges(&mut cand_tr, commitments);
            let mut response_tr = cand_tr;
            for (
                round_idx,
                (
                    (
                        y_ord,
                        y_r1cs,
                        y_batch,
                        y_bdlop,
                        r1_bdlop,
                        t_ord,
                        t_r1cs,
                        t_batch,
                        c_tau0,
                        c_tau1,
                        u_lin,
                    ),
                    chal_e,
                ),
            ) in candidates.into_iter().zip(challenges).enumerate()
            {
                let mut z_ord = Vec::new();
                let mut z_r1cs = Vec::new();
                let mut rej = false;
                for i in 0..2 {
                    let mut zo = vec![RingElem::zero(); lp.cols];
                    for col in 0..lp.cols {
                        for c_idx in 0..RING_DEGREE {
                            let v = y_ord[i][col].coeffs[c_idx]
                                + chal_e * adv_ord_wits[i][col].coeffs[c_idx];
                            if v.unsigned_abs() > (z_ord_max as u64) {
                                rej = true;
                            }
                            zo[col].coeffs[c_idx] = v;
                        }
                    }
                    let mut zr = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                    for col in 0..BAZAAR_R1CS_COLS {
                        for c_idx in 0..RING_DEGREE {
                            let v = y_r1cs[i][col].coeffs[c_idx]
                                + chal_e * adv_r1cs_wits[i][col].coeffs[c_idx];
                            if v.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                                rej = true;
                            }
                            zr[col].coeffs[c_idx] = v;
                        }
                    }
                    z_ord.push(zo);
                    z_r1cs.push(zr);
                }
                let mut z_batch = vec![RingElem::zero(); BAZAAR_R1CS_COLS];
                for col in 0..BAZAAR_R1CS_COLS {
                    for c_idx in 0..RING_DEGREE {
                        let v = y_batch[col].coeffs[c_idx] + chal_e * batch_w[col].coeffs[c_idx];
                        if v.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                            rej = true;
                        }
                        z_batch[col].coeffs[c_idx] = v;
                    }
                }
                let mut z_bdlop = vec![RingElem::zero(); BAZAAR_BDLOP_COLS];
                for col in 0..BAZAAR_BDLOP_COLS {
                    for c_idx in 0..RING_DEGREE {
                        let v = y_bdlop[col].coeffs[c_idx] + chal_e * r1_bdlop[col].coeffs[c_idx];
                        if v.unsigned_abs() > (BAZAAR_Z_MAX as u64) {
                            rej = true;
                        }
                        z_bdlop[col].coeffs[c_idx] = v;
                    }
                }
                if rej {
                    continue 'batch;
                }
                if round_idx == 0 {
                    let mut aks = Vec::new();
                    for zo in &z_ord {
                        let mut tr_ak = response_tr.fork(BAZAAR_AKITA_ROUND0_LABEL);
                        let tr_id = response_tr.fork(DUAL_TRACK2_LABEL);
                        aks.push(akita_prove_open(&lp, zo, z_ord_max as u64, &mut tr_ak).unwrap());
                        response_tr.join(&tr_ak, &tr_id);
                    }
                    adv_akitas = Some(aks);
                }
                adv_rounds.push(DarkBazaarZkRound {
                    t_ord,
                    t_r1cs,
                    t_batch,
                    c_tau0,
                    c_tau1,
                    u_lin,
                    z_ord,
                    z_r1cs,
                    z_batch,
                    z_bdlop,
                });
            }
            break;
        }

        let mut ak_it = adv_akitas.unwrap().into_iter();
        let forged_splice_a = DarkBazaarSameOpeningProof {
            uniform_price: 48,
            order_fills: vec![12, 12],
            dual_slacks: vec![1, 1],
            flow_dual_mu: 0,
            order_openings: (0..2)
                .map(|i| OrderDualOpeningProof {
                    canopy_bind_limbs: splice_binds[i],
                    eval_point: adv_eval_pts[i],
                    claimed_mle_val: adv_mles[i],
                    canopy_proof: adv_c_prfs[i].clone(),
                    r1cs_comm: splice_r1cs_comms[i].clone(),
                    akita_proof: ak_it.next().unwrap(),
                })
                .collect(),
            batch_carry_comm: batch_c,
            zk_rounds: adv_rounds,
        };
        assert_eq!(
            verify_dark_bazaar_same_opening(
                &vk,
                &cp,
                &lp,
                &market,
                &smudge,
                &spliced_orders,
                &forged_splice_a
            ),
            Err(LatticeError::CommitmentMismatchAtOrder(0)),
            "cross-track splicing with Order A Canopy + Order B Lattice must be rejected at the SameOpening weld!"
        );

        // 4. P3-02: O(N log N) `check_accounts_nodup` over 4,096 orders completes instantaneously and catches duplicates
        let mut many_orders: Vec<CommittedPrivateOrder> = (0..4096u64)
            .map(|i| CommittedPrivateOrder {
                account_id: i.wrapping_mul(2_654_435_761),
                side: OrderSide::Bid,
                max_bits: 16,
                canopy_comm: orders[0].canopy_comm,
                lattice_comm: orders[0].lattice_comm.clone(),
            })
            .collect();
        check_accounts_nodup(&many_orders).unwrap();
        let dup_id = many_orders[17].account_id;
        many_orders[3999].account_id = dup_id;
        assert_eq!(
            check_accounts_nodup(&many_orders),
            Err(LatticeError::DuplicateAccountOrder(dup_id))
        );
    }
}
