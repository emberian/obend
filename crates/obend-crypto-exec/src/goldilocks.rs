//! Canonical 64-bit Goldilocks field ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$),
//! 128-bit quadratic challenge extension `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$),
//! `CanonicalLift` non-aliasing guard, in-place radix-2 NTT / iNTT, and linear-time
//! multilinear hypercube `eq_poly` & sumcheck prover/verifier.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::transcript::{FenziTranscript, InstanceBound};

/// The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = \text{0xFFFF\_FFFF\_0000\_0001}$.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

/// Reduction constant $\epsilon = 2^{32} - 1 = 2^{64} - p$.
pub const GOLDILOCKS_EPSILON: u64 = 0xFFFF_FFFF;

/// Multiplicative generator $g = 7$ of $\mathbb{F}_p^\times$ (also quadratic non-residue for $\mathbb{F}_{p^2}$).
pub const GOLDILOCKS_GENERATOR: u64 = 7;

/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const GOLDILOCKS_ROOT_2_32: u64 = 1_753_635_133_440_165_772;

/// Maximum 2-adicity of the Goldilocks multiplicative group ($2^{32} \mid p - 1$).
pub const GOLDILOCKS_TWO_ADICITY: u32 = 32;

/// Error returned when a 64-bit word lies in the non-canonical alias range $[p, 2^{64})$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanonicalLiftError {
    pub raw_value: u64,
}

impl fmt::Display for CanonicalLiftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "non-canonical Goldilocks encoding 0x{:016x} >= p (0x{:016x})",
            self.raw_value, GOLDILOCKS_PRIME
        )
    }
}

/// Error for NTT / sumcheck operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GoldilocksExecError {
    InvalidPowerOfTwoLength(usize),
    LogLengthExceedsTwoAdicity(u32),
    ZeroBlowupFactor,
    RoundCountMismatch { expected: usize, actual: usize },
    DegreeBoundExceeded { max_deg: usize, actual_coeffs: usize },
    RoundSumCheckFailed { round: usize },
    FinalEqEvaluationMismatch,
    EmptyEvaluationTable,
}

impl fmt::Display for GoldilocksExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPowerOfTwoLength(n) => write!(f, "length {n} is not a non-zero power of two"),
            Self::LogLengthExceedsTwoAdicity(k) => write!(f, "log2(N)={k} exceeds Goldilocks 2-adicity 32"),
            Self::ZeroBlowupFactor => write!(f, "LDE blowup factor must be a power of two >= 1"),
            Self::RoundCountMismatch { expected, actual } => {
                write!(f, "sumcheck round count mismatch: expected {expected}, got {actual}")
            }
            Self::DegreeBoundExceeded { max_deg, actual_coeffs } => {
                write!(f, "round polynomial has {actual_coeffs} coeffs, exceeding max_deg {max_deg}")
            }
            Self::RoundSumCheckFailed { round } => {
                write!(f, "sumcheck round {round} failed p(0) + p(1) == claimed_sum")
            }
            Self::FinalEqEvaluationMismatch => {
                write!(f, "weighted sumcheck final evaluation disagrees with eq_poly factor")
            }
            Self::EmptyEvaluationTable => write!(f, "multilinear table must be non-empty"),
        }
    }
}

/// Canonical element of the Goldilocks prime field $\mathbb{F}_p$.
///
/// Invariant: `self.0 < GOLDILOCKS_PRIME` at all times.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Goldilocks(u64);

impl fmt::Debug for Goldilocks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Goldilocks({})", self.0)
    }
}

/// Explicit witness-carrying canonical integer lift $< p$ (`K5` / closing `F4` & `0 vs p` alias).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalLift(Goldilocks);

impl CanonicalLift {
    /// Strictly validate `raw < GOLDILOCKS_PRIME`, rejecting all $2^{32}-1$ aliases in $[p, 2^{64})$.
    #[inline]
    pub const fn try_new(raw: u64) -> Result<Self, CanonicalLiftError> {
        if raw < GOLDILOCKS_PRIME {
            Ok(Self(Goldilocks(raw)))
        } else {
            Err(CanonicalLiftError { raw_value: raw })
        }
    }

    #[inline]
    pub const fn into_field(self) -> Goldilocks {
        self.0
    }

    #[inline]
    pub const fn value(self) -> u64 {
        self.0.0
    }
}

impl Goldilocks {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);
    pub const NON_RESIDUE: Self = Self(7);
    pub const NEG_ONE: Self = Self(GOLDILOCKS_PRIME - 1);

    /// Strict canonical lift: rejects every integer in $[p, 2^{64})$.
    #[inline]
    pub const fn from_canonical(raw: u64) -> Result<Self, CanonicalLiftError> {
        match CanonicalLift::try_new(raw) {
            Ok(lift) => Ok(lift.0),
            Err(err) => Err(err),
        }
    }

    /// Branch-clean canonicalization of an arbitrary `u64` modulo $p$ (`x < p ? x : x - p`).
    /// Named `_reduced` so callers never confuse modular reduction with `CanonicalLift`.
    #[inline]
    pub const fn from_u64_reduced(x: u64) -> Self {
        let (diff, borrow) = x.overflowing_sub(GOLDILOCKS_PRIME);
        let mask = (borrow as u64).wrapping_neg();
        Self((x & mask) | (diff & !mask))
    }

    /// Hardware-exact 128-to-64 branch-clean Goldilocks modular reduction matching
    /// `Obend.Apps.ZkNtt.goldilocksReduce128Spec`.
    #[inline]
    pub const fn reduce128(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let hi_lo = hi & GOLDILOCKS_EPSILON;
        let hi_hi = hi >> 32;
        let mid = (hi_lo << 32).wrapping_sub(hi_lo);
        let lo_c = Self::from_u64_reduced(lo);
        lo_c.const_add(Self(mid)).const_sub(Self(hi_hi))
    }

    /// Reduce an arbitrary 128-bit integer modulo $p$ (used for 128-bit challenge sampling).
    #[inline]
    pub const fn from_u128_reduced(x: u128) -> Self {
        Self::reduce128(x)
    }

    /// Return the guaranteed-canonical representative in $[0, p - 1]$.
    #[inline]
    pub const fn to_canonical_u64(self) -> u64 {
        self.0
    }

    /// Encode as 8 big-endian bytes (matching `Obend.Crypto.encodeGoldilocksBytes`).
    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 8] {
        self.0.to_be_bytes()
    }

    /// Encode as 8 little-endian bytes.
    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    /// Decode 8 big-endian bytes, strictly rejecting non-canonical values in $[p, 2^{64})$.
    #[inline]
    pub const fn from_be_bytes_canonical(bytes: [u8; 8]) -> Result<Self, CanonicalLiftError> {
        Self::from_canonical(u64::from_be_bytes(bytes))
    }

    /// Decode 8 little-endian bytes, strictly rejecting non-canonical values in $[p, 2^{64})$.
    #[inline]
    pub const fn from_le_bytes_canonical(bytes: [u8; 8]) -> Result<Self, CanonicalLiftError> {
        Self::from_canonical(u64::from_le_bytes(bytes))
    }

    /// Branch-clean modular addition matching `glAdd` in `Obend/Apps/ZkNtt.lean`.
    #[inline]
    pub const fn const_add(self, rhs: Self) -> Self {
        let rem_p = GOLDILOCKS_PRIME - rhs.0;
        let (diff, borrow) = self.0.overflowing_sub(rem_p);
        let plain_sum = self.0.wrapping_add(rhs.0);
        let mask = (borrow as u64).wrapping_neg();
        Self((plain_sum & mask) | (diff & !mask))
    }

    /// Branch-clean modular subtraction matching `glSub` in `Obend/Apps/ZkNtt.lean`.
    #[inline]
    pub const fn const_sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.0.overflowing_sub(rhs.0);
        let adj = (borrow as u64).wrapping_neg() & GOLDILOCKS_PRIME;
        Self(diff.wrapping_add(adj))
    }

    /// Branch-clean negation (`0 - self mod p`).
    #[inline]
    pub const fn const_neg(self) -> Self {
        Self::ZERO.const_sub(self)
    }

    /// Branch-clean modular multiplication via 128-to-64 shift/mask reduction.
    #[inline]
    pub const fn const_mul(self, rhs: Self) -> Self {
        Self::reduce128((self.0 as u128) * (rhs.0 as u128))
    }

    #[inline]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    /// Constant-stride binary exponentiation for public exponents.
    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Multiplicative inverse $a^{p - 2} \bmod p$ via fixed addition chain (`None` iff `self == 0`).
    #[inline]
    pub const fn inv(self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        // p - 2 = 0xFFFF_FFFE_FFFF_FFFF = (2^32 - 2) * 2^32 + (2^32 - 1)
        let t2 = self.square().const_mul(self); // a^(2^2 - 1)
        let t3 = t2.square().const_mul(self); // a^(2^3 - 1)
        let t6 = exp_pow2(t3, 3).const_mul(t3); // a^(2^6 - 1)
        let t12 = exp_pow2(t6, 6).const_mul(t6); // a^(2^12 - 1)
        let t24 = exp_pow2(t12, 12).const_mul(t12); // a^(2^24 - 1)
        let t30 = exp_pow2(t24, 6).const_mul(t6); // a^(2^30 - 1)
        let t31 = t30.square().const_mul(self); // a^(2^31 - 1)
        let t32 = t31.square().const_mul(self); // a^(2^32 - 1)
        // a^((2^31 - 1) * 2^33 + (2^32 - 1)) = a^(2^64 - 2^33 + 2^32 - 1) = a^(p - 2)
        let hi = exp_pow2(t31, 33);
        Some(hi.const_mul(t32))
    }

    /// Return the canonical $2^k$-th primitive root of unity in $\mathbb{F}_p$ ($0 \le k \le 32$).
    #[inline]
    pub const fn primitive_root_of_unity(log_n: u32) -> Result<Self, GoldilocksExecError> {
        if log_n > GOLDILOCKS_TWO_ADICITY {
            return Err(GoldilocksExecError::LogLengthExceedsTwoAdicity(log_n));
        }
        let root = exp_pow2(Self(GOLDILOCKS_ROOT_2_32), GOLDILOCKS_TWO_ADICITY - log_n);
        Ok(root)
    }
}

#[inline]
const fn exp_pow2(mut x: Goldilocks, mut k: u32) -> Goldilocks {
    while k > 0 {
        x = x.square();
        k -= 1;
    }
    x
}

impl Add for Goldilocks {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for Goldilocks {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for Goldilocks {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for Goldilocks {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

/// Quadratic extension $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$ providing full ~128-bit
/// Fiat–Shamir & sumcheck soundness (`K5`/`K7`, closing `F4`).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GoldilocksExt2 {
    pub c0: Goldilocks,
    pub c1: Goldilocks,
}

impl fmt::Debug for GoldilocksExt2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ext2({} + {}·u)", self.c0.to_canonical_u64(), self.c1.to_canonical_u64())
    }
}

impl GoldilocksExt2 {
    pub const ZERO: Self = Self { c0: Goldilocks::ZERO, c1: Goldilocks::ZERO };
    pub const ONE: Self = Self { c0: Goldilocks::ONE, c1: Goldilocks::ZERO };
    pub const U_BASIS: Self = Self { c0: Goldilocks::ZERO, c1: Goldilocks::ONE };

    #[inline]
    pub const fn new(c0: Goldilocks, c1: Goldilocks) -> Self {
        Self { c0, c1 }
    }

    #[inline]
    pub const fn from_base(c0: Goldilocks) -> Self {
        Self { c0, c1: Goldilocks::ZERO }
    }

    #[inline]
    pub const fn from_canonical_u64_pair(c0: u64, c1: u64) -> Result<Self, CanonicalLiftError> {
        let a0 = match Goldilocks::from_canonical(c0) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let a1 = match Goldilocks::from_canonical(c1) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        Ok(Self { c0: a0, c1: a1 })
    }

    /// Encode as 16 big-endian bytes (`be8(c0) || be8(c1)`), matching `encodeGoldilocksExt2Bytes`.
    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 16] {
        let b0 = self.c0.to_be_bytes();
        let b1 = self.c1.to_be_bytes();
        [
            b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7],
            b1[0], b1[1], b1[2], b1[3], b1[4], b1[5], b1[6], b1[7],
        ]
    }

    /// Decode 16 big-endian bytes with strict `CanonicalLift` validation on both coordinates.
    #[inline]
    pub const fn from_be_bytes_canonical(bytes: [u8; 16]) -> Result<Self, CanonicalLiftError> {
        let b0 = [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]];
        let b1 = [bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15]];
        let c0 = match Goldilocks::from_be_bytes_canonical(b0) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let c1 = match Goldilocks::from_be_bytes_canonical(b1) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        Ok(Self { c0, c1 })
    }

    #[inline]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_add(rhs.c0),
            c1: self.c1.const_add(rhs.c1),
        }
    }

    #[inline]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_sub(rhs.c0),
            c1: self.c1.const_sub(rhs.c1),
        }
    }

    #[inline]
    pub const fn const_neg(self) -> Self {
        Self {
            c0: self.c0.const_neg(),
            c1: self.c1.const_neg(),
        }
    }

    /// $(a_0 + a_1 u)(b_0 + b_1 u) = (a_0 b_0 + 7 a_1 b_1) + (a_0 b_1 + a_1 b_0) u$.
    #[inline]
    pub const fn const_mul(self, rhs: Self) -> Self {
        let a0b0 = self.c0.const_mul(rhs.c0);
        let a1b1 = self.c1.const_mul(rhs.c1);
        // Karatsuba: (a0 + a1)(b0 + b1) - a0*b0 - a1*b1 = a0*b1 + a1*b0
        let sum_a = self.c0.const_add(self.c1);
        let sum_b = rhs.c0.const_add(rhs.c1);
        let c1 = sum_a.const_mul(sum_b).const_sub(a0b0).const_sub(a1b1);
        // 7 * a1b1 = (8 - 1) * a1b1
        let two = a1b1.const_add(a1b1);
        let four = two.const_add(two);
        let seven_a1b1 = four.const_add(two).const_add(a1b1);
        let c0 = a0b0.const_add(seven_a1b1);
        Self { c0, c1 }
    }

    /// Multiply an extension element by a base-field scalar in 2 base multiplications.
    #[inline]
    pub const fn mul_base(self, scalar: Goldilocks) -> Self {
        Self {
            c0: self.c0.const_mul(scalar),
            c1: self.c1.const_mul(scalar),
        }
    }

    #[inline]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    /// Frobenius conjugate $\overline{a_0 + a_1 u} = a_0 - a_1 u$.
    #[inline]
    pub const fn conj(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.const_neg(),
        }
    }

    /// Norm $N(a_0 + a_1 u) = a_0^2 - 7 a_1^2 \in \mathbb{F}_p$.
    #[inline]
    pub const fn norm(self) -> Goldilocks {
        let a0_sq = self.c0.square();
        let a1_sq = self.c1.square();
        let seven_a1_sq = Goldilocks::NON_RESIDUE.const_mul(a1_sq);
        a0_sq.const_sub(seven_a1_sq)
    }

    /// Exact inverse in $\mathbb{F}_{p^2}$ (`None` iff `self == ZERO`, since $7$ is a non-residue).
    #[inline]
    pub const fn inv(self) -> Option<Self> {
        if self.c0.to_canonical_u64() == 0 && self.c1.to_canonical_u64() == 0 {
            return None;
        }
        match self.norm().inv() {
            Some(norm_inv) => Some(self.conj().mul_base(norm_inv)),
            None => None,
        }
    }

    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }
}

impl Add for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for GoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for GoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for GoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

/// Polymorphic field trait shared by `Goldilocks` and `GoldilocksExt2`.
pub trait FieldElem:
    Copy
    + Clone
    + Default
    + PartialEq
    + Eq
    + fmt::Debug
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Neg<Output = Self>
    + Mul<Output = Self>
    + MulAssign
{
    const ZERO: Self;
    const ONE: Self;
    /// Effective floor($\log_2 |\mathbb{F}|$) challenge security bits (`63` for base, `127` for `Ext2`).
    const CHALLENGE_SECURITY_BITS: u32;

    fn from_base_goldilocks(x: Goldilocks) -> Self;
}

impl FieldElem for Goldilocks {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;
    const CHALLENGE_SECURITY_BITS: u32 = 63;

    #[inline]
    fn from_base_goldilocks(x: Goldilocks) -> Self {
        x
    }
}

impl FieldElem for GoldilocksExt2 {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;
    const CHALLENGE_SECURITY_BITS: u32 = 127;

    #[inline]
    fn from_base_goldilocks(x: Goldilocks) -> Self {
        Self::from_base(x)
    }
}

/// Marker trait restricting Fiat–Shamir / sumcheck challenges to $\ge 120$-bit extension fields
/// (`GoldilocksExt2` only — `Goldilocks` intentionally does NOT implement this trait, closing `F4`!).
pub trait SoundChallengeField: FieldElem {}

impl SoundChallengeField for GoldilocksExt2 {}

// ============================================================================
// Radix-2 In-Place NTT, Inverse NTT & Reed–Solomon Coset Low-Degree Extension
// ============================================================================

#[inline]
fn bit_reverse_permute<T>(slice: &mut [T]) {
    let n = slice.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();
    let shift = usize::BITS - log_n;
    for i in 0..n {
        let rev = i.reverse_bits() >> shift;
        if i < rev {
            slice.swap(i, rev);
        }
    }
}

/// In-place iterative Cooley–Tukey radix-2 forward NTT over `Goldilocks` ($N = 2^k \le 2^{32}$).
pub fn ntt_in_place(values: &mut [Goldilocks]) -> Result<(), GoldilocksExecError> {
    let n = values.len();
    if n == 0 || !n.is_power_of_two() {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(n));
    }
    let log_n = n.trailing_zeros();
    if log_n > GOLDILOCKS_TWO_ADICITY {
        return Err(GoldilocksExecError::LogLengthExceedsTwoAdicity(log_n));
    }
    if n == 1 {
        return Ok(());
    }

    bit_reverse_permute(values);

    let mut stage_log = 1u32;
    let mut len = 2usize;
    while len <= n {
        let half = len >> 1;
        let step_root = Goldilocks::primitive_root_of_unity(stage_log)?;
        let mut start = 0usize;
        while start < n {
            let mut w = Goldilocks::ONE;
            for j in 0..half {
                let u = values[start + j];
                let v = values[start + j + half] * w;
                values[start + j] = u + v;
                values[start + j + half] = u - v;
                w *= step_root;
            }
            start += len;
        }
        len <<= 1;
        stage_log += 1;
    }
    Ok(())
}

/// In-place iterative radix-2 inverse NTT over `Goldilocks` ($N = 2^k \le 2^{32}$).
pub fn intt_in_place(values: &mut [Goldilocks]) -> Result<(), GoldilocksExecError> {
    let n = values.len();
    if n == 0 || !n.is_power_of_two() {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(n));
    }
    let log_n = n.trailing_zeros();
    if log_n > GOLDILOCKS_TWO_ADICITY {
        return Err(GoldilocksExecError::LogLengthExceedsTwoAdicity(log_n));
    }
    if n == 1 {
        return Ok(());
    }

    bit_reverse_permute(values);

    let mut stage_log = 1u32;
    let mut len = 2usize;
    while len <= n {
        let half = len >> 1;
        let step_root = Goldilocks::primitive_root_of_unity(stage_log)?;
        let step_root_inv = step_root.inv().expect("primitive root is non-zero");
        let mut start = 0usize;
        while start < n {
            let mut w = Goldilocks::ONE;
            for j in 0..half {
                let u = values[start + j];
                let v = values[start + j + half] * w;
                values[start + j] = u + v;
                values[start + j + half] = u - v;
                w *= step_root_inv;
            }
            start += len;
        }
        len <<= 1;
        stage_log += 1;
    }

    let n_inv = Goldilocks::from_u64_reduced(n as u64)
        .inv()
        .expect("power of two <= 2^32 is non-zero mod Goldilocks");
    for v in values.iter_mut() {
        *v *= n_inv;
    }
    Ok(())
}

/// Reed–Solomon coset low-degree extension: interpolates `evals` on $H_C$ and evaluates the
/// degree-$< C$ polynomial on $\text{shift} \cdot H_{C \cdot \text{blowup}}$.
pub fn coset_lde(
    evals: &[Goldilocks],
    shift: Goldilocks,
    blowup: usize,
) -> Result<Vec<Goldilocks>, GoldilocksExecError> {
    if blowup == 0 || !blowup.is_power_of_two() {
        return Err(GoldilocksExecError::ZeroBlowupFactor);
    }
    let c = evals.len();
    if c == 0 || !c.is_power_of_two() {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(c));
    }
    let extended_len = c.checked_mul(blowup).ok_or(GoldilocksExecError::LogLengthExceedsTwoAdicity(33))?;
    let mut coeffs = evals.to_vec();
    intt_in_place(&mut coeffs)?;

    let mut out = vec![Goldilocks::ZERO; extended_len];
    let mut shift_pow = Goldilocks::ONE;
    for (i, coeff) in coeffs.into_iter().enumerate() {
        out[i] = coeff * shift_pow;
        shift_pow *= shift;
    }
    ntt_in_place(&mut out)?;
    Ok(out)
}

/// $\mathbb{F}_p$-linear lift of `coset_lde` to `GoldilocksExt2` vectors: since $H_L \subset \mathbb{F}_p$
/// and `shift` $\in \mathbb{F}_p$, encoding `c0` and `c1` independently commutes with any
/// $\mathbb{F}_{p^2}$-linear row combination $q^\top M$.
pub fn coset_lde_ext2(
    evals: &[GoldilocksExt2],
    shift: Goldilocks,
    blowup: usize,
) -> Result<Vec<GoldilocksExt2>, GoldilocksExecError> {
    let mut c0_vec = Vec::with_capacity(evals.len());
    let mut c1_vec = Vec::with_capacity(evals.len());
    for z in evals {
        c0_vec.push(z.c0);
        c1_vec.push(z.c1);
    }
    let ext_c0 = coset_lde(&c0_vec, shift, blowup)?;
    let ext_c1 = coset_lde(&c1_vec, shift, blowup)?;
    Ok(ext_c0
        .into_iter()
        .zip(ext_c1)
        .map(|(c0, c1)| GoldilocksExt2::new(c0, c1))
        .collect())
}

// ============================================================================
// Multilinear Hypercube `eq_poly`, Evaluation & Linear-Time O(2^v) Sumcheck
// ============================================================================

/// Evaluate $\widetilde{\text{eq}}(\mathbf{z}, \mathbf{r}) = \prod_{i=0}^{v-1} ((1 - z_i)(1 - r_i) + z_i r_i)$
/// at two points in $O(v)$ field operations.
pub fn eq_poly_at<F: FieldElem>(z: &[F], r: &[F]) -> F {
    assert_eq!(z.len(), r.len(), "eq_poly_at requires equal-dimension points");
    let mut acc = F::ONE;
    for (&zi, &ri) in z.iter().zip(r.iter()) {
        // (1 - zi)(1 - ri) + zi*ri = 1 - zi - ri + 2*zi*ri
        let prod = zi * ri;
        let term = F::ONE - zi - ri + prod + prod;
        acc *= term;
    }
    acc
}

/// Materialize the $2^v$-entry hypercube Lagrange basis table $\widetilde{\text{eq}}(\mathbf{z}, \mathbf{b})$
/// in $O(2^v)$ field multiplications, matching `Obend.Crypto.Multilinear.hypercube` little-endian
/// layout (`idx` bit `i` = `(idx >> i) & 1`, so coordinate `0` alternates at stride `1`).
pub fn eq_poly_table<F: FieldElem>(point: &[F]) -> Vec<F> {
    let v = point.len();
    let total = 1usize << v;
    let mut table = vec![F::ZERO; total];
    table[0] = F::ONE;
    // Build from MSB down to LSB so coordinate 0 ends up at stride 1:
    // After processing `point[v - 1 .. k]`, `cur_len = 2^(v - k)`.
    // Splitting each entry `w` into `[(1 - r_k) * w, r_k * w]` doubles length with `r_k` at bit 0!
    let mut cur_len = 1usize;
    for &rk in point.iter().rev() {
        let one_minus_rk = F::ONE - rk;
        for idx in (0..cur_len).rev() {
            let w = table[idx];
            table[2 * idx] = one_minus_rk * w;
            table[2 * idx + 1] = rk * w;
        }
        cur_len <<= 1;
    }
    table
}

/// Evaluate multilinear table `tbl` ($|\text{tbl}| = 2^v$) at `point` in $O(2^v)$ operations.
pub fn mle_eval<F: FieldElem>(tbl: &[F], point: &[F]) -> Result<F, GoldilocksExecError> {
    let expected = 1usize << point.len();
    if tbl.len() != expected {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(tbl.len()));
    }
    let eq_tbl = eq_poly_table(point);
    let mut acc = F::ZERO;
    for (&val, &w) in tbl.iter().zip(eq_tbl.iter()) {
        acc += val * w;
    }
    Ok(acc)
}

/// Evaluate a base-field `Goldilocks` multilinear table at an extension-field `GoldilocksExt2` point
/// in $O(2^v)$ base-times-extension scalar multiplications.
pub fn mle_eval_base_at_ext2(
    tbl: &[Goldilocks],
    point: &[GoldilocksExt2],
) -> Result<GoldilocksExt2, GoldilocksExecError> {
    let expected = 1usize << point.len();
    if tbl.len() != expected {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(tbl.len()));
    }
    let eq_tbl = eq_poly_table(point);
    let mut acc = GoldilocksExt2::ZERO;
    for (&val, &w) in tbl.iter().zip(eq_tbl.iter()) {
        acc += w.mul_base(val);
    }
    Ok(acc)
}

/// In-place stride-2 butterfly fold of coordinate `0` at challenge `r0`:
/// replaces `(lo, hi)` pairs with `lo + r0 * (hi - lo)`, halving the active slice length.
/// Matches `Obend.Crypto.Multilinear.foldFirstVar`.
pub fn fold_first_var_in_place<F: FieldElem>(tbl: &mut Vec<F>, r0: F) {
    let half = tbl.len().div_ceil(2);
    for j in 0..half {
        let lo = tbl[2 * j];
        let hi = if 2 * j + 1 < tbl.len() { tbl[2 * j + 1] } else { F::ZERO };
        tbl[j] = lo + r0 * (hi - lo);
    }
    tbl.truncate(half);
}

/// Univariate round polynomial in monomial basis `coeffs = [c_0, c_1, ..., c_d]` over `GoldilocksExt2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckRoundPolyExt2 {
    pub coeffs: Vec<GoldilocksExt2>,
}

impl SumcheckRoundPolyExt2 {
    /// Horner evaluation $c_0 + x (c_1 + x (\cdots))$.
    #[inline]
    pub fn eval(&self, x: GoldilocksExt2) -> GoldilocksExt2 {
        let mut acc = GoldilocksExt2::ZERO;
        for &c in self.coeffs.iter().rev() {
            acc = c + x * acc;
        }
        acc
    }

    #[inline]
    pub fn deg_le(&self, max_deg: usize) -> bool {
        self.coeffs.len() <= max_deg + 1
    }

    /// Canonical byte serialization matching `Obend.Crypto.Sumcheck.encodeRoundPoly`.
    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = crate::transcript::leb128(self.coeffs.len());
        for c in &self.coeffs {
            let enc = c.to_be_bytes();
            out.extend_from_slice(&crate::transcript::leb128(enc.len()));
            out.extend_from_slice(&enc);
        }
        out
    }
}

/// Reduced evaluation claim emitted by the Fiat–Shamir sumcheck verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckEvalClaimExt2 {
    pub point: Vec<GoldilocksExt2>,
    pub expected_val: GoldilocksExt2,
}

/// Domain label `"SUMCHECK.ROUND"` matching `Obend/Crypto/Sumcheck.lean`.
pub const SUMCHECK_ROUND_LABEL: &[u8] = b"SUMCHECK.ROUND";

/// Linear-time $O(2^v)$ multilinear sumcheck prover over `GoldilocksExt2` challenges
/// bound to `FenziTranscript<InstanceBound>` (`\sum_{x \in \{0,1\}^v} f(x) = S`).
///
/// Round 0 accumulates directly over `Goldilocks` and lifts to `GoldilocksExt2` on the first fold,
/// halving memory immediately.
pub fn prove_multilinear_sumcheck_ext2(
    base_tbl: &[Goldilocks],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<(Vec<SumcheckRoundPolyExt2>, SumcheckEvalClaimExt2), GoldilocksExecError> {
    let n = base_tbl.len();
    if n == 0 || !n.is_power_of_two() {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(n));
    }
    let num_vars = n.trailing_zeros() as usize;
    if num_vars == 0 {
        return Ok((
            Vec::new(),
            SumcheckEvalClaimExt2 {
                point: Vec::new(),
                expected_val: GoldilocksExt2::from_base(base_tbl[0]),
            },
        ));
    }

    let mut rounds = Vec::with_capacity(num_vars);
    let mut point = Vec::with_capacity(num_vars);

    // Round 0: base-field pair scan + lift to Ext2 of half size 2^(v-1)
    let half0 = n >> 1;
    let mut s0_base = Goldilocks::ZERO;
    let mut s1_base = Goldilocks::ZERO;
    for j in 0..half0 {
        s0_base += base_tbl[2 * j];
        s1_base += base_tbl[2 * j + 1];
    }
    let s0 = GoldilocksExt2::from_base(s0_base);
    let s1 = GoldilocksExt2::from_base(s1_base);
    let p0 = SumcheckRoundPolyExt2 {
        coeffs: vec![s0, s1 - s0],
    };
    tr.absorb(SUMCHECK_ROUND_LABEL, &p0.to_transcript_bytes());
    let r0 = tr.squeeze_ext2();
    rounds.push(p0);
    point.push(r0);

    let mut ext_tbl = Vec::with_capacity(half0);
    for j in 0..half0 {
        let lo = base_tbl[2 * j];
        let hi = base_tbl[2 * j + 1];
        ext_tbl.push(GoldilocksExt2::from_base(lo) + r0.mul_base(hi - lo));
    }

    // Rounds 1 .. num_vars - 1: in-place O(2^(v - round)) fold
    for _round in 1..num_vars {
        let half = ext_tbl.len() >> 1;
        let mut sum0 = GoldilocksExt2::ZERO;
        let mut sum1 = GoldilocksExt2::ZERO;
        for j in 0..half {
            sum0 += ext_tbl[2 * j];
            sum1 += ext_tbl[2 * j + 1];
        }
        let poly = SumcheckRoundPolyExt2 {
            coeffs: vec![sum0, sum1 - sum0],
        };
        tr.absorb(SUMCHECK_ROUND_LABEL, &poly.to_transcript_bytes());
        let r = tr.squeeze_ext2();
        fold_first_var_in_place(&mut ext_tbl, r);
        rounds.push(poly);
        point.push(r);
    }

    Ok((
        rounds,
        SumcheckEvalClaimExt2 {
            point,
            expected_val: ext_tbl[0],
        },
    ))
}

/// Linear-time $O(2^v)$ `eq_poly`-weighted sumcheck prover reducing an evaluation claim
/// $\tilde{f}(\mathbf{z}) = \sum_{\mathbf{x} \in \{0,1\}^v} f(\mathbf{x}) \cdot \widetilde{\text{eq}}(\mathbf{z}, \mathbf{x}) = y$
/// to a single random-point evaluation claim $\tilde{f}(\mathbf{r}) = y_{\text{final}}$.
pub fn prove_eq_weighted_sumcheck_ext2(
    base_tbl: &[Goldilocks],
    eval_point: &[GoldilocksExt2],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<(Vec<SumcheckRoundPolyExt2>, SumcheckEvalClaimExt2), GoldilocksExecError> {
    let num_vars = eval_point.len();
    let expected_len = 1usize << num_vars;
    if base_tbl.len() != expected_len {
        return Err(GoldilocksExecError::InvalidPowerOfTwoLength(base_tbl.len()));
    }
    if num_vars == 0 {
        return Ok((
            Vec::new(),
            SumcheckEvalClaimExt2 {
                point: Vec::new(),
                expected_val: GoldilocksExt2::from_base(base_tbl[0]),
            },
        ));
    }

    let mut f_tbl: Vec<GoldilocksExt2> = base_tbl
        .iter()
        .map(|&x| GoldilocksExt2::from_base(x))
        .collect();
    let mut eq_tbl = eq_poly_table(eval_point);
    let mut rounds = Vec::with_capacity(num_vars);
    let mut challenge_point = Vec::with_capacity(num_vars);

    for _round in 0..num_vars {
        let half = f_tbl.len() >> 1;
        // Degree-2 polynomial g(X) = sum_j (f0 + X*(f1 - f0)) * (e0 + X*(e1 - e0))
        // c0 = sum f0*e0, c2 = sum df*de, g(1) = sum f1*e1 => c1 = g(1) - c0 - c2
        let mut c0 = GoldilocksExt2::ZERO;
        let mut g1 = GoldilocksExt2::ZERO;
        let mut c2 = GoldilocksExt2::ZERO;
        for j in 0..half {
            let f0 = f_tbl[2 * j];
            let f1 = f_tbl[2 * j + 1];
            let e0 = eq_tbl[2 * j];
            let e1 = eq_tbl[2 * j + 1];
            c0 += f0 * e0;
            g1 += f1 * e1;
            c2 += (f1 - f0) * (e1 - e0);
        }
        let c1 = g1 - c0 - c2;
        let poly = SumcheckRoundPolyExt2 {
            coeffs: vec![c0, c1, c2],
        };
        tr.absorb(SUMCHECK_ROUND_LABEL, &poly.to_transcript_bytes());
        let r = tr.squeeze_ext2();
        fold_first_var_in_place(&mut f_tbl, r);
        fold_first_var_in_place(&mut eq_tbl, r);
        rounds.push(poly);
        challenge_point.push(r);
    }

    Ok((
        rounds,
        SumcheckEvalClaimExt2 {
            point: challenge_point,
            expected_val: f_tbl[0],
        },
    ))
}

/// Polymorphic Fiat–Shamir sumcheck verifier over `FenziTranscript<InstanceBound>`.
/// Checks degree bound `max_deg` and round consistency $p_i(0) + p_i(1) = S_i$ for all $v$ rounds.
pub fn verify_sumcheck_ext2(
    max_deg: usize,
    num_vars: usize,
    mut claimed_sum: GoldilocksExt2,
    rounds: &[SumcheckRoundPolyExt2],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<SumcheckEvalClaimExt2, GoldilocksExecError> {
    if rounds.len() != num_vars {
        return Err(GoldilocksExecError::RoundCountMismatch {
            expected: num_vars,
            actual: rounds.len(),
        });
    }
    let mut point = Vec::with_capacity(num_vars);
    for (idx, poly) in rounds.iter().enumerate() {
        if !poly.deg_le(max_deg) {
            return Err(GoldilocksExecError::DegreeBoundExceeded {
                max_deg,
                actual_coeffs: poly.coeffs.len(),
            });
        }
        let p0 = poly.eval(GoldilocksExt2::ZERO);
        let p1 = poly.eval(GoldilocksExt2::ONE);
        if p0 + p1 != claimed_sum {
            return Err(GoldilocksExecError::RoundSumCheckFailed { round: idx });
        }
        tr.absorb(SUMCHECK_ROUND_LABEL, &poly.to_transcript_bytes());
        let r = tr.squeeze_ext2();
        claimed_sum = poly.eval(r);
        point.push(r);
    }
    Ok(SumcheckEvalClaimExt2 {
        point,
        expected_val: claimed_sum,
    })
}

/// Verify an `eq_poly`-weighted sumcheck proof reducing $\tilde{f}(\mathbf{z}) = y$ to
/// $\tilde{f}(\mathbf{r}) = y_{\text{final}}$, dividing out $\widetilde{\text{eq}}(\mathbf{z}, \mathbf{r})$
/// (or cross-checking $y_{\text{sub}} == \tilde{f}(\mathbf{r}) \cdot \widetilde{\text{eq}}(\mathbf{z}, \mathbf{r})$).
pub fn verify_eq_weighted_sumcheck_ext2(
    eval_point: &[GoldilocksExt2],
    claimed_eval: GoldilocksExt2,
    prover_claimed_f_at_r: GoldilocksExt2,
    rounds: &[SumcheckRoundPolyExt2],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<SumcheckEvalClaimExt2, GoldilocksExecError> {
    let raw_claim = verify_sumcheck_ext2(2, eval_point.len(), claimed_eval, rounds, tr)?;
    let eq_factor = eq_poly_at(eval_point, &raw_claim.point);
    if prover_claimed_f_at_r * eq_factor != raw_claim.expected_val {
        return Err(GoldilocksExecError::FinalEqEvaluationMismatch);
    }
    Ok(SumcheckEvalClaimExt2 {
        point: raw_claim.point,
        expected_val: prover_claimed_f_at_r,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::FenziTranscript;

    #[test]
    fn test_canonical_lift_rejects_entire_alias_band() {
        assert_eq!(
            CanonicalLift::try_new(GOLDILOCKS_PRIME - 1).unwrap().value(),
            GOLDILOCKS_PRIME - 1
        );
        assert!(CanonicalLift::try_new(GOLDILOCKS_PRIME).is_err());
        assert!(CanonicalLift::try_new(GOLDILOCKS_PRIME + 1).is_err());
        assert!(CanonicalLift::try_new(u64::MAX).is_err());
        assert!(Goldilocks::from_be_bytes_canonical(GOLDILOCKS_PRIME.to_be_bytes()).is_err());
        assert!(Goldilocks::from_le_bytes_canonical(u64::MAX.to_le_bytes()).is_err());
    }

    #[test]
    fn test_goldilocks_arithmetic_and_inverse_identities() {
        let edge_vals = [
            0u64,
            1,
            2,
            7,
            (1u64 << 32) - 1,
            1u64 << 32,
            GOLDILOCKS_PRIME - 2,
            GOLDILOCKS_PRIME - 1,
        ];
        let p = GOLDILOCKS_PRIME as u128;
        for &a_raw in &edge_vals {
            let a = Goldilocks::from_canonical(a_raw).unwrap();
            if a_raw != 0 {
                let inv = a.inv().expect("non-zero element invertible");
                assert_eq!(a * inv, Goldilocks::ONE);
            } else {
                assert!(a.inv().is_none());
            }
            for &b_raw in &edge_vals {
                let b = Goldilocks::from_canonical(b_raw).unwrap();
                let exp_add = ((a_raw as u128 + b_raw as u128) % p) as u64;
                let exp_sub = ((a_raw as u128 + p - b_raw as u128) % p) as u64;
                let exp_mul = ((a_raw as u128 * b_raw as u128) % p) as u64;
                assert_eq!((a + b).to_canonical_u64(), exp_add);
                assert_eq!((a - b).to_canonical_u64(), exp_sub);
                assert_eq!((a * b).to_canonical_u64(), exp_mul);
            }
        }
    }

    #[test]
    fn test_ext2_irreducibility_and_field_laws() {
        // Euler criterion: 7^((p-1)/2) == -1 mod p proves X^2 - 7 is irreducible over F_p
        let euler = Goldilocks::NON_RESIDUE.pow((GOLDILOCKS_PRIME - 1) / 2);
        assert_eq!(euler, Goldilocks::NEG_ONE);

        let x = GoldilocksExt2::from_canonical_u64_pair(GOLDILOCKS_PRIME - 5, 123_456_789).unwrap();
        let y = GoldilocksExt2::from_canonical_u64_pair(987_654_321, GOLDILOCKS_PRIME - 2).unwrap();
        let z = GoldilocksExt2::from_canonical_u64_pair(42, 777).unwrap();

        assert_eq!((x + y) * z, x * z + y * z);
        assert_eq!((x * y) * z, x * (y * z));
        assert_eq!(GoldilocksExt2::U_BASIS.square(), GoldilocksExt2::from_base(Goldilocks::NON_RESIDUE));

        let x_inv = x.inv().expect("non-zero Ext2 element is invertible");
        assert_eq!(x * x_inv, GoldilocksExt2::ONE);
        assert!(GoldilocksExt2::ZERO.inv().is_none());
    }

    #[test]
    fn test_radix2_ntt_intt_and_polynomial_convolution() {
        // Verify root of unity order
        let root32 = Goldilocks::primitive_root_of_unity(32).unwrap();
        assert_eq!(exp_pow2(root32, 31), Goldilocks::NEG_ONE);
        assert_eq!(exp_pow2(root32, 32), Goldilocks::ONE);

        // Roundtrip on N = 256
        let mut poly: Vec<Goldilocks> = (0..256u64)
            .map(|i| Goldilocks::from_u64_reduced(i.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
            .collect();
        let orig = poly.clone();
        ntt_in_place(&mut poly).unwrap();
        assert_ne!(poly, orig);
        intt_in_place(&mut poly).unwrap();
        assert_eq!(poly, orig);

        // Convolution check against naive schoolbook multiplication
        let a: Vec<Goldilocks> = (1..=8u64).map(Goldilocks::from_u64_reduced).collect();
        let b: Vec<Goldilocks> = (10..=17u64).map(Goldilocks::from_u64_reduced).collect();
        let mut expected = vec![Goldilocks::ZERO; 16];
        for i in 0..8 {
            for j in 0..8 {
                expected[i + j] += a[i] * b[j];
            }
        }
        let mut fa = vec![Goldilocks::ZERO; 16];
        let mut fb = vec![Goldilocks::ZERO; 16];
        fa[..8].copy_from_slice(&a);
        fb[..8].copy_from_slice(&b);
        ntt_in_place(&mut fa).unwrap();
        ntt_in_place(&mut fb).unwrap();
        for i in 0..16 {
            fa[i] *= fb[i];
        }
        intt_in_place(&mut fa).unwrap();
        assert_eq!(fa, expected);
    }

    #[test]
    fn test_eq_poly_and_linear_time_sumchecks() {
        let v = 6usize;
        let tbl: Vec<Goldilocks> = (0..(1usize << v))
            .map(|i| Goldilocks::from_u64_reduced((i as u64) * 13 + 5))
            .collect();
        let z: Vec<GoldilocksExt2> = (0..v)
            .map(|i| GoldilocksExt2::from_canonical_u64_pair(100 + i as u64, 200 + 3 * i as u64).unwrap())
            .collect();

        // Check hypercube sumcheck
        let mut hyper_sum = Goldilocks::ZERO;
        for &val in &tbl {
            hyper_sum += val;
        }
        let claimed_sum = GoldilocksExt2::from_base(hyper_sum);
        let vk = [0x11u8; 32];

        let mut prover_tr = FenziTranscript::new(b"test-seed")
            .bind_relation("OBEND.SUMCHECK.TEST/v1", &vk, b"deg1-hypercube")
            .bind_instance(b"mock-comm", claimed_sum, &[]);
        let mut verifier_tr = prover_tr.clone();

        let (rounds, prover_claim) = prove_multilinear_sumcheck_ext2(&tbl, &mut prover_tr).unwrap();
        let ver_claim = verify_sumcheck_ext2(1, v, claimed_sum, &rounds, &mut verifier_tr).unwrap();
        assert_eq!(prover_claim, ver_claim);
        assert_eq!(mle_eval_base_at_ext2(&tbl, &ver_claim.point).unwrap(), ver_claim.expected_val);

        // Check eq-weighted sumcheck reducing f(z) = y to f(r) = y_final
        let eval_z = mle_eval_base_at_ext2(&tbl, &z).unwrap();
        let mut prover_wtr = FenziTranscript::new(b"test-seed-eq")
            .bind_relation("OBEND.EQ_SUMCHECK.TEST/v1", &vk, b"deg2-eq-sumcheck")
            .bind_instance(b"mock-comm", eval_z, &z);
        let mut verifier_wtr = prover_wtr.clone();

        let (w_rounds, w_claim) = prove_eq_weighted_sumcheck_ext2(&tbl, &z, &mut prover_wtr).unwrap();
        let w_ver = verify_eq_weighted_sumcheck_ext2(
            &z,
            eval_z,
            w_claim.expected_val,
            &w_rounds,
            &mut verifier_wtr,
        )
        .unwrap();
        assert_eq!(w_claim, w_ver);
        assert_eq!(mle_eval_base_at_ext2(&tbl, &w_ver.point).unwrap(), w_ver.expected_val);
    }
}
