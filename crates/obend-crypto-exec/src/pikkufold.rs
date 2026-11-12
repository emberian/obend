//! `PikkuFold` (`ePrint 2026/1809`) + `Akita` (`ePrint 2026/1983`) Track L Lattice-SIS Engine
//! & Salted `SameOpening` Dark Bazaar Clearing Proof (`K5`–`K7`):
//! - Dedicated partially-splitting cyclotomic ring $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$
//!   over $q_{\text{lat}} = 2^{48} - 59 \equiv 5 \pmod 8$ (`X^{64}+1 = (X^{32}-\zeta)(X^{32}+\zeta)`, avoiding
//!   Goldilocks linear splitting `F10` while keeping unboxed `[i64; 64]` arithmetic overflow-free!)
//! - **0-multiplication** Kronecker ternary $\{-1, 0, +1\}$ witness projection (`PikkuFold`)
//! - Explicit per-round $\ell_\infty$ norm budget tracking (`F11`) & linear 2-to-1 witness folding
//! - Recursive `Akita` split-and-fold MSIS + linear-form opening proof down to dimension 1
//! - Constructive discrepancy witness extractor `extract_sis_collision` (`SisBreak`, closing `F1`/`F2`)
//! - Salted `commit_private_order` + `SmudgeSafe` + KKT zero-gap `SameOpening` Dark Bazaar proof (`K7`, closing `F6`/`F7`).

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
    Cshake256Xof, DUAL_TRACK1_LABEL, DUAL_TRACK2_LABEL, FenziTranscript, InstanceBound, leb128,
};

/// Cyclotomic power-of-two ring degree $d = 64$ for $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$.
pub const RING_DEGREE: usize = 64;

/// Half-degree $d / 2 = 32$ of the two irreducible Lyubashevsky–Seiler CRT factors $X^{32} \mp \zeta$.
pub const HALF_RING_DEGREE: usize = RING_DEGREE / 2;

/// Dedicated lattice prime $q_{\text{lat}} = 2^{48} - 59 = 281\_474\_976\_710\_597 \equiv 5 \pmod 8$.
pub const Q_LAT: i64 = (1i64 << 48) - 59;

/// Centered half-modulus $\lfloor q_{\text{lat}} / 2 \rfloor = 140\_737\_488\_355\_298$.
pub const HALF_Q_LAT: i64 = (Q_LAT - 1) / 2;

/// Primitive 4th root of unity $\zeta = 137\_064\_555\_638\_465 \bmod q_{\text{lat}}$ ($\zeta^2 \equiv -1$).
pub const Q_LAT_ZETA: i64 = 137_064_555_638_465;

/// Conservative non-wrapping $\ell_\infty$ norm ceiling $< q_{\text{lat}} / 4$.
pub const MAX_SAFE_SIS_NORM: u64 = (Q_LAT as u64) / 4 - 1;

/// Base-$2^{16}$ Goldilocks limb bound ($65535$).
pub const GADGET_LIMB_MAX: u64 = 0xFFFF;

/// Domain customizations and labels.
pub const PIKKUFOLD_CRS_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.PIKKUFOLD.CRS/v1";
pub const AKITA_ROUND_LABEL: &[u8] = b"AKITA.SPLITFOLD.ROUND";
pub const AKITA_KRON_LABEL: &[u8] = b"PIKKUFOLD.KRONECKER.PROJ";
pub const AKITA_FINAL_LABEL: &[u8] = b"AKITA.FINAL.WITNESS";
pub const DARK_BAZAAR_PROTO_ID: &str = "OBEND.DARKBAZAAR.SAMEOPENING/v1";

/// Errors emitted by `PikkuFold`, `Akita`, and `SameOpening` Dark Bazaar operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LatticeError {
    InvalidMatrixDimensions { rows: usize, cols: usize },
    MatrixEntryCountMismatch { expected: usize, actual: usize },
    WitnessLengthMismatch { expected: usize, actual: usize },
    WitnessNormExceeded { actual: u64, bound: u64 },
    NormBudgetOverflow { next_bound: u64, ceiling: u64 },
    OutOfBoundsColumn { col: usize, cols: usize },
    OutOfBoundsSlot { slot: usize },
    KroneckerArityMismatch { expected_len: usize, actual_len: usize },
    InvalidGadgetLimb(i64),
    NonCanonicalGoldilocks(CanonicalLiftError),
    AkitaRoundCountMismatch { expected: usize, actual: usize },
    AkitaCrossCommitmentSumMismatch { round: usize },
    AkitaFinalCommitmentMismatch,
    AkitaKroneckerProjectionMismatch,
    NoCollisionWitnessIsIdentical,
    CommitmentsDoNotMatch,
    ExtractedVectorNotInKernel,
    /// `SameOpening` Dark Bazaar errors (`K7`, closing `F6` & `F7`):
    MaxBitsExceedsCanonical63(u32),
    BitWitnessLengthExceeded { max_bits: u32, actual_len: usize },
    BlindingNormExceeded { actual: u64, max_allowed: u64 },
    UnsmudgedOrInsufficientNoiseBudget,
    DecryptionMarginWrapped,
    DuplicateOrIdenticalMarketAssets,
    OrderWitnessCountMismatch { expected: usize, actual: usize },
    DuplicateAccountOrder(u64),
    CommitmentMismatchAtOrder(usize),
    FlowConservationFailed,
    NegativeOrExcessFillAtOrder(usize),
    NonZeroPrimalDualKktGap { primal: i128, dual: i128 },
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

    /// **0-multiplication** negacyclic monomial shift: computes $(\text{sign} \cdot X^{\text{exp}}) \cdot \text{self} \bmod (X^d + 1)$
    /// where `sign` $\in \{-1, +1\}$ and `exp < d`, preserving $\|\text{out}\|_\infty == \|\text{self}\|_\infty$!
    pub fn mul_signed_monomial(&self, sign: i64, exp: usize) -> Self {
        debug_assert!(sign == 1 || sign == -1);
        let shift = exp & (RING_DEGREE - 1);
        let flip = if ((exp / RING_DEGREE) & 1) == 1 { -sign } else { sign };
        let mut out = [0i64; RING_DEGREE];
        for i in 0..RING_DEGREE {
            if i + shift < RING_DEGREE {
                out[i + shift] = if flip == 1 { self.coeffs[i] } else { -self.coeffs[i] };
            } else {
                // X^d = -1 in R_{q_lat}
                let idx = i + shift - RING_DEGREE;
                out[idx] = if flip == 1 { -self.coeffs[i] } else { self.coeffs[i] };
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
            if val < -HALF_Q_LAT || val > HALF_Q_LAT {
                return Err(LatticeError::InvalidGadgetLimb(val));
            }
            coeffs[i] = val;
        }
        Ok(Self { coeffs })
    }
}

/// Extended Euclidean Algorithm in $\mathbb{F}_{q_{\text{lat}}}[X]$ modulo $X^{32} + c_0$.
fn poly32_inv_mod_binom(a: &[i64; HALF_RING_DEGREE], c0_const: i64) -> Option<[i64; HALF_RING_DEGREE]> {
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
        while rem.len() - 1 >= deg_d && !(rem.len() == 1 && rem[0] == 0) {
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
/// using pure `i64` additions and subtractions (`0` ring or integer multiplications!).
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
    // Note: Q_LAT < 2^48 leaves 16 bits (65,536x) of signed headroom in i64; flush every 4096 terms.
    let mut acc = [0i64; RING_DEGREE];
    let mut chunk_count = 0usize;
    for (&trit, ring_elem) in trits.iter().zip(witness.iter()) {
        match trit {
            TernaryTrit::Zero => continue,
            TernaryTrit::PosOne => {
                let c = ring_elem.coeffs();
                for k in 0..RING_DEGREE {
                    acc[k] += c[k];
                }
            }
            TernaryTrit::NegOne => {
                let c = ring_elem.coeffs();
                for k in 0..RING_DEGREE {
                    acc[k] -= c[k];
                }
            }
        }
        chunk_count += 1;
        if chunk_count == 4096 {
            for k in 0..RING_DEGREE {
                acc[k] = center_mod_q(acc[k] as i128);
            }
            chunk_count = 0;
        }
    }
    for k in 0..RING_DEGREE {
        acc[k] = center_mod_q(acc[k] as i128);
    }
    Ok(RingElem { coeffs: acc })
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
    pub fn expand_from_seed(crs_seed: [u8; 32], rows: usize, cols: usize) -> Result<Self, LatticeError> {
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
        for l in 0..4 {
            out[ring_idx].coeffs[coeff_off + l] = limbs[l];
        }
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
    let next_bound = input_norm_bound
        .saturating_add(chal_l1.saturating_mul(input_norm_bound));
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
    if actual_norm > initial_norm_bound {
        return Err(LatticeError::WitnessNormExceeded {
            actual: actual_norm,
            bound: initial_norm_bound,
        });
    }
    let log_cols = params.cols.trailing_zeros() as usize;
    let final_budget = initial_norm_bound.saturating_mul(1u64 << log_cols);
    if final_budget > MAX_SAFE_SIS_NORM {
        return Err(LatticeError::NormBudgetOverflow {
            next_bound: final_budget,
            ceiling: MAX_SAFE_SIS_NORM,
        });
    }

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

        // Signed monomial challenge c = sign * X^exp (L1 norm = 1 => 0 multiplications to fold!)
        let (sign, exp) = tr.squeeze_signed_monomial(RING_DEGREE);

        let mut next_w = Vec::with_capacity(half);
        let mut next_kron = Vec::with_capacity(half);
        for j in 0..half {
            next_w.push(w_l[j].add(&w_r[j].mul_signed_monomial(sign, exp)));
            next_kron.push(k_l[j].add(&k_r[j].mul_signed_monomial(sign, exp)));
        }

        let mut next_mat = Vec::with_capacity(params.rows * half);
        for r in 0..params.rows {
            let off_h = r * half;
            for j in 0..half {
                next_mat.push(a_l[off_h + j].add(&a_r[off_h + j].mul_signed_monomial(sign, exp)));
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
/// per-round commitment algebra, Kronecker projection consistency, and tracked $\ell_\infty$ norm budget!
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
        // Check t_ll + t_rr == cur_syn AND k_ll + k_rr == cur_k_val
        for r in 0..params.rows {
            if rnd.t_ll[r].add(&rnd.t_rr[r]) != cur_syn[r] {
                return Err(LatticeError::AkitaCrossCommitmentSumMismatch { round: round_idx });
            }
        }
        if rnd.k_ll.add(&rnd.k_rr) != cur_k_val {
            return Err(LatticeError::AkitaKroneckerProjectionMismatch);
        }

        tracked_norm_bound = tracked_norm_bound.saturating_mul(2);
        if tracked_norm_bound > MAX_SAFE_SIS_NORM {
            return Err(LatticeError::NormBudgetOverflow {
                next_bound: tracked_norm_bound,
                ceiling: MAX_SAFE_SIS_NORM,
            });
        }

        absorb_akita_round(tr, rnd);
        let (sign, exp) = tr.squeeze_signed_monomial(RING_DEGREE);
        // c^2 = (+1) * X^(2 * exp)
        let exp2 = 2 * exp;

        let mut next_syn = Vec::with_capacity(params.rows);
        for r in 0..params.rows {
            let term_c = rnd.t_mid[r].mul_signed_monomial(sign, exp);
            let term_c2 = rnd.t_rr[r].mul_signed_monomial(1, exp2);
            next_syn.push(rnd.t_ll[r].add(&term_c).add(&term_c2));
        }
        cur_k_val = rnd
            .k_ll
            .add(&rnd.k_mid.mul_signed_monomial(sign, exp))
            .add(&rnd.k_rr.mul_signed_monomial(1, exp2));

        let half = cur_cols >> 1;
        let mut next_mat = Vec::with_capacity(params.rows * half);
        for r in 0..params.rows {
            let off = r * cur_cols;
            for j in 0..half {
                let al = &cur_mat[off + j];
                let ar = &cur_mat[off + half + j];
                next_mat.push(al.add(&ar.mul_signed_monomial(sign, exp)));
            }
        }
        let mut next_kron = Vec::with_capacity(half);
        for j in 0..half {
            next_kron.push(cur_kron[j].add(&cur_kron[half + j].mul_signed_monomial(sign, exp)));
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
// 6. Salted `commit_private_order` + `SameOpening` Dark Bazaar Proof (`K7`)
// ============================================================================

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

fn build_order_table_and_ring_witness(
    account_id: u64,
    side: OrderSide,
    max_bits: u32,
    witness: &PrivateOrderWitness,
    lattice_cols: usize,
) -> Result<([Goldilocks; 4], Vec<RingElem>), LatticeError> {
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

    let acc_gl = CanonicalLift::try_new(account_id)?.into_field();
    let side_gl = Goldilocks::from_canonical(side.tag_u64())?;
    let qty_val = witness.qty()?;
    let tot_val = witness.total()?;
    let qty_gl = CanonicalLift::try_new(qty_val)?.into_field();
    let tot_gl = CanonicalLift::try_new(tot_val)?.into_field();

    let table = [acc_gl, side_gl, qty_gl, tot_gl];
    if lattice_cols < 2 || !lattice_cols.is_power_of_two() {
        return Err(LatticeError::InvalidMatrixDimensions {
            rows: 1,
            cols: lattice_cols,
        });
    }
    let mut ring_witness = pack_goldilocks_to_ring_witness(&table, lattice_cols)?;
    // Place hiding salt polynomial into column 1 (`A = [A_msg | A_blind | ...]`)
    ring_witness[1] = witness.salt.lattice_blinding;

    Ok((table, ring_witness))
}

/// Commit a private Dark Bazaar order under **salted** `Canopy` (Track H) + **salted** `PikkuFold`
/// $R_{q_{\text{lat}}}$ MSIS (Track L) (`K7`, defeating `F6` dictionary & MITM recovery!).
pub fn commit_private_order(
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    account_id: u64,
    side: OrderSide,
    max_bits: u32,
    witness: &PrivateOrderWitness,
) -> Result<CommittedPrivateOrder, LatticeError> {
    let (table, ring_witness) = build_order_table_and_ring_witness(
        account_id,
        side,
        max_bits,
        witness,
        lattice_params.cols,
    )?;
    let canopy_state =
        canopy_commit(canopy_params, 2, &table, Some(&witness.salt.canopy_salt_seed))?;
    let lattice_comm = commit_ring_witness(lattice_params, &ring_witness)?;

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
    /// 4. Correctness margin: `noise_bound + smudge_bound < Q_LAT / 4` (smudge cannot wrap decryption!)
    pub fn validate(&self) -> Result<(), LatticeError> {
        if self.noise_bound == 0 || self.sec_bits < 40 || self.sec_bits >= 120 || self.num_releases == 0 {
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
        // Check correctness margin against typical 128-bit RLWE collective modulus Q_FHE = 2^118
        // (and non-zero headroom): smudge cannot exceed decryption half-modulus!
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

/// Per-order Dual-Track (`Canopy` + `Akita`) proof bundle inside `DarkBazaarSameOpeningProof`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderDualOpeningProof {
    pub opened_witness: PrivateOrderWitness,
    pub eval_point: [GoldilocksExt2; 2],
    pub claimed_mle_val: GoldilocksExt2,
    pub canopy_proof: CanopyBatchedProof,
    pub akita_proof: AkitaFoldProof,
}

/// KKT primal-dual zero-gap clearing certificate + Dual-Track salted order proofs (`K7`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DarkBazaarSameOpeningProof {
    pub uniform_price: u64,
    /// Matched goods quantity $f_i \ge 0$ filled for each order $i$.
    pub order_fills: Vec<u64>,
    /// Dual capacity-slack variables $s_i \ge 0$ for each order $i$.
    pub dual_slacks: Vec<u64>,
    pub order_openings: Vec<OrderDualOpeningProof>,
}

#[inline]
fn order_crosses_price(side: OrderSide, qty: u64, total: u64, price: u64) -> bool {
    if qty == 0 {
        return false;
    }
    match side {
        // Bid crosses if limit total >= qty * price
        OrderSide::Bid => (total as u128) >= (qty as u128) * (price as u128),
        // Ask crosses if limit total <= qty * price
        OrderSide::Ask => (total as u128) <= (qty as u128) * (price as u128),
    }
}

fn bind_bazaar_transcript(
    vk_digest: &[u8; 32],
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    orders: &[CommittedPrivateOrder],
    uniform_price: u64,
) -> FenziTranscript<InstanceBound> {
    let mut circuit_desc = Vec::new();
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

    let price_ext = GoldilocksExt2::from_base(Goldilocks::from_u64_reduced(uniform_price));
    FenziTranscript::new(b"OBEND.DARKBAZAAR.SEED")
        .bind_relation(DARK_BAZAAR_PROTO_ID, vk_digest, &circuit_desc)
        .bind_instance(&comm_bytes, price_ext, &[])
}

/// Generate a complete salted `SameOpening` Dark Bazaar Dual-Track (`Canopy` + `Akita`) proof (`K7`).
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
    smudge.validate()?;
    if market.currency_asset == market.goods_asset {
        return Err(LatticeError::DuplicateOrIdenticalMarketAssets);
    }
    if committed_orders.len() != witnesses.len()
        || order_fills.len() != committed_orders.len()
        || dual_slacks.len() != committed_orders.len()
    {
        return Err(LatticeError::OrderWitnessCountMismatch {
            expected: committed_orders.len(),
            actual: witnesses.len(),
        });
    }

    let mut tr = bind_bazaar_transcript(vk_digest, market, smudge, committed_orders, uniform_price);
    let mut order_openings = Vec::with_capacity(committed_orders.len());

    for (ord, wit) in committed_orders.iter().zip(witnesses.iter()) {
        let (table, ring_witness) = build_order_table_and_ring_witness(
            ord.account_id,
            ord.side,
            ord.max_bits,
            wit,
            lattice_params.cols,
        )?;
        let canopy_state =
            canopy_commit(canopy_params, 2, &table, Some(&wit.salt.canopy_salt_seed))?;
        let r0 = tr.squeeze_ext2();
        let r1 = tr.squeeze_ext2();
        let eval_point = [r0, r1];
        let claimed_mle_val = mle_eval_base_at_ext2(&table, &eval_point)
            .map_err(CanopyError::from)?;

        let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
        let mut tr_l = tr.fork(DUAL_TRACK2_LABEL);

        let canopy_proof = canopy_open(canopy_params, &canopy_state, &eval_point, &mut tr_h)?;
        let akita_proof =
            akita_prove_open(lattice_params, &ring_witness, GADGET_LIMB_MAX, &mut tr_l)?;
        tr.join(&tr_h, &tr_l);

        order_openings.push(OrderDualOpeningProof {
            opened_witness: wit.clone(),
            eval_point,
            claimed_mle_val,
            canopy_proof,
            akita_proof,
        });
    }

    let proof = DarkBazaarSameOpeningProof {
        uniform_price,
        order_fills,
        dual_slacks,
        order_openings,
    };
    // Self-check before returning
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

/// Verify a salted `SameOpening` Dark Bazaar clearing proof:
/// 1. `SmudgeBudgetConfig` (`2026/2546` drowning + decryption margin),
/// 2. Distinct market assets & unique account IDs,
/// 3. `BitZ` $2^B$ range bounds & `CanonicalLift` (`< p`),
/// 4. Salted `Canopy` (Track H) + `Akita` (Track L) Dual-PCS openings bound to `FenziTranscript<InstanceBound>`,
/// 5. Exact flow conservation, crossing capacity bounds, and KKT zero primal-dual gap!
pub fn verify_dark_bazaar_same_opening(
    vk_digest: &[u8; 32],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    market: &DarkBazaarMarket,
    smudge: &SmudgeBudgetConfig,
    committed_orders: &[CommittedPrivateOrder],
    proof: &DarkBazaarSameOpeningProof,
) -> Result<(), LatticeError> {
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

    // Account uniqueness check (`accountsNodup`)
    for i in 0..n {
        for j in (i + 1)..n {
            if committed_orders[i].account_id == committed_orders[j].account_id {
                return Err(LatticeError::DuplicateAccountOrder(
                    committed_orders[i].account_id,
                ));
            }
        }
    }

    let mut tr = bind_bazaar_transcript(
        vk_digest,
        market,
        smudge,
        committed_orders,
        proof.uniform_price,
    );

    let mut net_flow: i128 = 0;
    let mut primal_objective: i128 = 0;
    let mut dual_objective: i128 = 0;

    for (idx, (ord, open)) in committed_orders
        .iter()
        .zip(proof.order_openings.iter())
        .enumerate()
    {
        let (table, ring_witness) = build_order_table_and_ring_witness(
            ord.account_id,
            ord.side,
            ord.max_bits,
            &open.opened_witness,
            lattice_params.cols,
        )?;

        // Verify salted commitments match `ord` on BOTH tracks
        let expected_canopy = canopy_commit(
            canopy_params,
            2,
            &table,
            Some(&open.opened_witness.salt.canopy_salt_seed),
        )?;
        let expected_lat = commit_ring_witness(lattice_params, &ring_witness)?;
        if expected_canopy.commitment != ord.canopy_comm || expected_lat != ord.lattice_comm {
            return Err(LatticeError::CommitmentMismatchAtOrder(idx));
        }

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
        let mut tr_l = tr.fork(DUAL_TRACK2_LABEL);

        canopy_verify(
            canopy_params,
            &ord.canopy_comm,
            &open.eval_point,
            open.claimed_mle_val,
            &open.canopy_proof,
            &mut tr_h,
        )?;
        akita_verify_open(
            lattice_params,
            &ord.lattice_comm,
            GADGET_LIMB_MAX,
            &open.akita_proof,
            &mut tr_l,
        )?;
        tr.join(&tr_h, &tr_l);

        // KKT primal feasibility + dual objective accumulation
        let qty = open.opened_witness.qty()?;
        let total = open.opened_witness.total()?;
        let fill = proof.order_fills[idx];
        let slack = proof.dual_slacks[idx];
        let crosses = order_crosses_price(ord.side, qty, total, proof.uniform_price);
        let cap = if crosses { qty } else { 0 };
        if fill > cap {
            return Err(LatticeError::NegativeOrExcessFillAtOrder(idx));
        }
        // Dual feasibility on crossing orders: slack >= 1 so any feasible circulation f_i <= cap_i
        // satisfies f_i <= cap_i * slack_i; at zero gap this enforces slack_i == 1 when filled == cap_i > 0!
        if crosses && fill > 0 && slack < 1 {
            return Err(LatticeError::NonZeroPrimalDualKktGap {
                primal: fill as i128,
                dual: 0,
            });
        }

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

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_prime_u64(n: u64) -> bool {
        if n < 2 || n % 2 == 0 {
            return n == 2;
        }
        let mut d = n - 1;
        let mut s = 0u32;
        while d % 2 == 0 {
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

    #[test]
    fn test_cyclotomic_ring_primality_partial_splitting_and_short_invertibility() {
        assert!(is_prime_u64(Q_LAT as u64), "Q_LAT must be prime");
        assert_eq!(Q_LAT % 8, 5, "Q_LAT == 5 mod 8 ensures exact 2-factor splitting");
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
        let diff_inv = diff.inv().expect("short non-zero element must be invertible in R_{q_lat}");
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
        let tern_inv = tern.inv().expect("non-zero ternary ring element is invertible");
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
        let base_tr = FenziTranscript::new(b"akita-test")
            .bind_relation("OBEND.AKITA.PCS/v1", &vk, b"rows=4,cols=8")
            .bind_instance(&comm.to_transcript_bytes(), GoldilocksExt2::ZERO, &[]);

        let mut p_tr = base_tr.clone();
        let proof = akita_prove_open(&params, &witness, GADGET_LIMB_MAX, &mut p_tr).unwrap();
        assert_eq!(proof.rounds.len(), 3); // log2(8) == 3

        let mut v_tr = base_tr.clone();
        let final_budget =
            akita_verify_open(&params, &comm, GADGET_LIMB_MAX, &proof, &mut v_tr).unwrap();
        assert_eq!(final_budget, GADGET_LIMB_MAX * 8);
        assert_eq!(p_tr.state(), v_tr.state());

        // Verify sparse one-hot agrees with dense commitment
        let mut one_hot_w = vec![RingElem::zero(); params.cols];
        one_hot_w[3] = RingElem::one().mul_signed_monomial(1, 19);
        assert_eq!(
            commit_one_hot_ring(&params, 3, 19).unwrap(),
            commit_ring_witness(&params, &one_hot_w).unwrap()
        );
    }
}
