//! Constant-time equality for digests, MACs and other authenticators.
//!
//! For equal public lengths, the loop reads every pair and accumulates the full XOR difference.
//! The optimization barrier and out-of-line calls discourage early-exit code generation.
//! Constant-time machine code depends on the compiler and target.

/// OR of the byte-wise XOR of two equal-length slices.
#[inline(always)]
const fn fold_diff(a: &[u8], b: &[u8]) -> u8 {
    let mut diff = 0u8;
    let mut i = 0;
    while i < a.len() {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff
}

/// Constant-time byte-slice equality. Slices of unequal length compare unequal at once.
#[inline(never)]
pub const fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && core::hint::black_box(fold_diff(a, b)) == 0
}

/// Constant-time equality of two 32-byte digests.
#[inline(never)]
pub const fn ct_eq_32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    core::hint::black_box(fold_diff(a, b)) == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_byte_position_and_bit_is_compared() {
        let a: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0x5a);
        assert!(ct_eq_32(&a, &a));
        assert!(ct_eq(&a, &a));
        for i in 0..32 {
            for bit in 0..8 {
                let mut b = a;
                b[i] ^= 1 << bit;
                assert!(!ct_eq_32(&a, &b));
                assert!(!ct_eq(&a, &b));
            }
        }
    }

    #[test]
    fn lengths_must_agree() {
        assert!(ct_eq(&[], &[]));
        assert!(!ct_eq(&[0], &[]));
        assert!(!ct_eq(&[1, 2, 3], &[1, 2]));
        assert!(!ct_eq(&[1, 2], &[1, 2, 3]));
    }

    #[test]
    fn usable_in_constants() {
        const { assert!(ct_eq_32(&[7; 32], &[7; 32])) };
        const { assert!(!ct_eq(b"tag", b"tah")) };
    }
}
