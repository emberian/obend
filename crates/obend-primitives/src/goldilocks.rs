//! The Goldilocks prime field `F_p`, `p = 2^64 - 2^32 + 1`: canonical `u64` elements with
//! branch-free `const` arithmetic, and the strict `CanonicalLift` that refuses the `2^32 - 1`
//! aliases in `[p, 2^64)`.

use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

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
    ZeroCosetShift,
    RoundCountMismatch {
        expected: usize,
        actual: usize,
    },
    DegreeBoundExceeded {
        max_deg: usize,
        actual_coeffs: usize,
    },
    RoundSumCheckFailed {
        round: usize,
    },
    FinalEqEvaluationMismatch,
    EmptyEvaluationTable,
}

impl fmt::Display for GoldilocksExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPowerOfTwoLength(n) => {
                write!(f, "length {n} is not a non-zero power of two")
            }
            Self::LogLengthExceedsTwoAdicity(k) => {
                write!(f, "log2(N)={k} exceeds Goldilocks 2-adicity 32")
            }
            Self::ZeroBlowupFactor => write!(f, "LDE blowup factor must be a power of two >= 1"),
            Self::ZeroCosetShift => write!(f, "coset LDE shift must be non-zero in F_p^*"),
            Self::RoundCountMismatch { expected, actual } => {
                write!(
                    f,
                    "sumcheck round count mismatch: expected {expected}, got {actual}"
                )
            }
            Self::DegreeBoundExceeded {
                max_deg,
                actual_coeffs,
            } => {
                write!(
                    f,
                    "round polynomial has {actual_coeffs} coeffs, exceeding max_deg {max_deg}"
                )
            }
            Self::RoundSumCheckFailed { round } => {
                write!(
                    f,
                    "sumcheck round {round} failed p(0) + p(1) == claimed_sum"
                )
            }
            Self::FinalEqEvaluationMismatch => {
                write!(
                    f,
                    "weighted sumcheck final evaluation disagrees with eq_poly factor"
                )
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

impl fmt::Display for Goldilocks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// Explicit witness-carrying canonical integer lift $< p$ (`K5` / closing `F4` & `0 vs p` alias).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalLift(Goldilocks);

impl CanonicalLift {
    /// Strictly validate `raw < GOLDILOCKS_PRIME`, rejecting all $2^{32}-1$ aliases in $[p, 2^{64})$.
    #[inline]
    pub const fn try_new(raw: u64) -> Result<Self, CanonicalLiftError> {
        match Goldilocks::from_canonical(raw) {
            Ok(x) => Ok(Self(x)),
            Err(err) => Err(err),
        }
    }

    #[inline]
    pub const fn into_field(self) -> Goldilocks {
        self.0
    }

    #[inline]
    pub const fn value(self) -> u64 {
        self.0.to_canonical_u64()
    }
}

impl Goldilocks {
    pub const P: u64 = GOLDILOCKS_PRIME;
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);
    pub const NON_RESIDUE: Self = Self(GOLDILOCKS_GENERATOR);
    pub const NEG_ONE: Self = Self(GOLDILOCKS_PRIME - 1);

    /// Reduce a machine word modulo the field prime.
    pub const fn new(raw: u64) -> Self {
        Self::from_u64_reduced(raw)
    }

    /// Strict constructor for a wire-format field element.
    pub const fn try_new(raw: u64) -> Result<Self, CanonicalLiftError> {
        Self::from_canonical(raw)
    }

    pub const fn from_canonical_u64(raw: u64) -> Option<Self> {
        match Self::from_canonical(raw) {
            Ok(value) => Some(value),
            Err(_) => None,
        }
    }

    pub const fn is_canonical(self) -> bool {
        self.0 < Self::P
    }

    pub const fn value(self) -> u64 {
        self.to_canonical_u64()
    }

    pub const fn reduce(raw: u128) -> Self {
        Self::from_u128_reduced(raw)
    }

    pub const fn reduce128(raw: u128) -> Self {
        Self::from_u128_reduced(raw)
    }

    // The proving worker exposes these operations to const callers.
    pub const fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }

    pub const fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }

    pub const fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }

    /// Strict canonical lift: rejects every integer in $[p, 2^{64})$.
    #[inline]
    pub const fn from_canonical(raw: u64) -> Result<Self, CanonicalLiftError> {
        if raw < GOLDILOCKS_PRIME {
            Ok(Self(raw))
        } else {
            Err(CanonicalLiftError { raw_value: raw })
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

    /// Hardware-exact branch-clean reduction of a 128-bit integer modulo $p$, matching
    /// `Obend.Apps.ZkNtt.goldilocksReduce128Spec`: with $x = lo + 2^{64}(hi_{lo} + 2^{32} hi_{hi})$,
    /// $2^{64} \equiv 2^{32} - 1$ and $2^{96} \equiv -1$.
    #[inline]
    pub const fn from_u128_reduced(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let hi_lo = hi & GOLDILOCKS_EPSILON;
        let hi_hi = hi >> 32;
        // hi_lo * (2^32 - 1) <= (2^32 - 1)^2 < p, so it is already canonical.
        let mid = (hi_lo << 32).wrapping_sub(hi_lo);
        Self::from_u64_reduced(lo)
            .const_add(Self(mid))
            .const_sub(Self(hi_hi))
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
        Self::from_u128_reduced((self.0 as u128) * (rhs.0 as u128))
    }

    #[inline]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    /// `self^(2^k)` by `k` squarings.
    #[inline]
    pub const fn exp_power_of_2(self, k: u32) -> Self {
        let mut x = self;
        let mut i = 0;
        while i < k {
            x = x.square();
            i += 1;
        }
        x
    }

    /// Binary exponentiation for public exponents.
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
        let t6 = t3.exp_power_of_2(3).const_mul(t3); // a^(2^6 - 1)
        let t12 = t6.exp_power_of_2(6).const_mul(t6); // a^(2^12 - 1)
        let t24 = t12.exp_power_of_2(12).const_mul(t12); // a^(2^24 - 1)
        let t30 = t24.exp_power_of_2(6).const_mul(t6); // a^(2^30 - 1)
        let t31 = t30.square().const_mul(self); // a^(2^31 - 1)
        let t32 = t31.square().const_mul(self); // a^(2^32 - 1)
                                                // a^((2^31 - 1) * 2^33 + (2^32 - 1)) = a^(2^64 - 2^33 + 2^32 - 1) = a^(p - 2)
        Some(t31.exp_power_of_2(33).const_mul(t32))
    }

    /// The canonical $2^k$-th primitive root of unity in $\mathbb{F}_p$ (error for $k > 32$).
    #[inline]
    pub const fn primitive_root_of_unity(log_n: u32) -> Result<Self, GoldilocksExecError> {
        if log_n > GOLDILOCKS_TWO_ADICITY {
            return Err(GoldilocksExecError::LogLengthExceedsTwoAdicity(log_n));
        }
        Ok(Self(GOLDILOCKS_ROOT_2_32).exp_power_of_2(GOLDILOCKS_TWO_ADICITY - log_n))
    }

    /// The distance from zero in the centered representation, $\min(x, p - x)$.
    #[inline]
    pub const fn centered_norm(self) -> u64 {
        let neg = GOLDILOCKS_PRIME - self.0;
        if self.0 <= neg {
            self.0
        } else {
            neg
        }
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = GOLDILOCKS_PRIME;

    #[test]
    fn canonical_lift_rejects_entire_alias_band() {
        assert_eq!(CanonicalLift::try_new(P - 1).unwrap().value(), P - 1);
        assert_eq!(
            CanonicalLift::try_new(P - 1).unwrap().into_field(),
            Goldilocks::NEG_ONE
        );
        for raw in [P, P + 1, P + GOLDILOCKS_EPSILON / 2, u64::MAX] {
            assert_eq!(
                CanonicalLift::try_new(raw),
                Err(CanonicalLiftError { raw_value: raw })
            );
            assert!(Goldilocks::from_canonical(raw).is_err());
            assert_eq!(
                Goldilocks::from_u64_reduced(raw).to_canonical_u64(),
                raw - P
            );
        }
        assert!(Goldilocks::from_be_bytes_canonical(P.to_be_bytes()).is_err());
        assert!(Goldilocks::from_le_bytes_canonical(u64::MAX.to_le_bytes()).is_err());
        let x = Goldilocks::from_be_bytes_canonical((P - 2).to_be_bytes()).unwrap();
        assert_eq!(Goldilocks::from_le_bytes_canonical(x.to_le_bytes()), Ok(x));
        assert_eq!(
            std::format!("{x} {x:?}"),
            std::format!("{} Goldilocks({})", P - 2, P - 2)
        );
    }

    #[test]
    fn arithmetic_and_inverse_on_edge_values() {
        let edge = [0u64, 1, 2, 7, GOLDILOCKS_EPSILON, 1 << 32, P - 2, P - 1];
        for &a_raw in &edge {
            let a = Goldilocks::from_canonical(a_raw).unwrap();
            match a.inv() {
                Some(inv) => assert_eq!(a * inv, Goldilocks::ONE),
                None => assert_eq!(a_raw, 0),
            }
            assert_eq!(a + -a, Goldilocks::ZERO);
            for &b_raw in &edge {
                let b = Goldilocks::from_canonical(b_raw).unwrap();
                let p = P as u128;
                let (x, y) = (a_raw as u128, b_raw as u128);
                assert_eq!((a + b).to_canonical_u64(), ((x + y) % p) as u64);
                assert_eq!((a - b).to_canonical_u64(), ((x + p - y) % p) as u64);
                assert_eq!((a * b).to_canonical_u64(), ((x * y) % p) as u64);
                let (mut c, mut d, mut e) = (a, a, a);
                c += b;
                d -= b;
                e *= b;
                assert_eq!((c, d, e), (a + b, a - b, a * b));
            }
        }
    }

    #[test]
    fn arithmetic_against_integer_reference() {
        let mut n = 0x1234_5678_9abc_def0u64;
        for _ in 0..10_000 {
            n ^= n << 13;
            n ^= n >> 7;
            n ^= n << 17;
            let a = Goldilocks::from_u64_reduced(n);
            n = n.rotate_left(29).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let b = Goldilocks::from_u64_reduced(n);
            let c = Goldilocks::from_u64_reduced(n.reverse_bits());
            let (x, y) = (a.to_canonical_u64() as u128, b.to_canonical_u64() as u128);
            assert_eq!((a * b).to_canonical_u64(), ((x * y) % P as u128) as u64);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            let wide = ((n as u128) << 64) | n.reverse_bits() as u128;
            assert_eq!(
                Goldilocks::from_u128_reduced(wide).to_canonical_u64(),
                (wide % P as u128) as u64
            );
            assert_eq!(a.pow(n), {
                let mut acc = Goldilocks::ONE;
                for bit in (0..64).rev() {
                    acc = acc.square();
                    if (n >> bit) & 1 == 1 {
                        acc *= a;
                    }
                }
                acc
            });
        }
        assert_eq!(
            Goldilocks::from_u128_reduced(u128::MAX).to_canonical_u64(),
            (u128::MAX % P as u128) as u64
        );
    }

    #[test]
    fn roots_of_unity_and_non_residue() {
        let root32 = Goldilocks::primitive_root_of_unity(32).unwrap();
        assert_eq!(root32.to_canonical_u64(), GOLDILOCKS_ROOT_2_32);
        assert_eq!(
            Goldilocks::NON_RESIDUE.pow((1 << 32) - 1),
            root32,
            "omega = 7^((p - 1) / 2^32)"
        );
        assert_eq!(root32.exp_power_of_2(31), Goldilocks::NEG_ONE);
        assert_eq!(root32.exp_power_of_2(32), Goldilocks::ONE);
        assert_eq!(
            Goldilocks::primitive_root_of_unity(1),
            Ok(Goldilocks::NEG_ONE)
        );
        assert_eq!(Goldilocks::primitive_root_of_unity(0), Ok(Goldilocks::ONE));
        assert_eq!(
            Goldilocks::primitive_root_of_unity(33),
            Err(GoldilocksExecError::LogLengthExceedsTwoAdicity(33))
        );
        // Euler's criterion: 7 is a quadratic non-residue, so X^2 - 7 is irreducible over F_p.
        assert_eq!(
            Goldilocks::NON_RESIDUE.pow((P - 1) / 2),
            Goldilocks::NEG_ONE
        );
    }

    #[test]
    fn centered_norm_is_distance_from_zero() {
        let norm = |x: u64| Goldilocks::from_u64_reduced(x).centered_norm();
        assert_eq!(norm(0), 0);
        assert_eq!(norm(1), 1);
        assert_eq!(norm(P - 1), 1);
        assert_eq!(norm(P / 2), P / 2);
        assert_eq!(norm(P / 2 + 1), P / 2);
        assert_eq!((-Goldilocks::from_u64_reduced(5)).centered_norm(), 5);
    }
}
