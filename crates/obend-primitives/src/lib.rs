//! Primitives shared across the workspace: FIPS 180-4 SHA-256 and SHA-384/512 with RFC 2104 HMAC
//! and RFC 5869 HKDF, RFC 8032 Ed25519 strict verification, fixed-width Montgomery arithmetic over
//! `u64` limbs, the Goldilocks prime field `p = 2^64 - 2^32 + 1`, and constant-time equality.
//!
//! `no_std` and allocation-free. The `alloc` feature adds the `Vec`-returning big-integer encoders
//! `bigint::limbs_to_be` and `bigint::Mont::to_be`.
//!
//! Hash states and HMAC key blocks are cleared when they go out of scope. Without volatile writes
//! this is best effort: the compiler is discouraged from removing the clear, and copies it made
//! earlier are out of reach.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(test)]
extern crate std;

pub mod bigint;
pub mod ct;
pub mod ed25519;
pub mod goldilocks;
pub mod sha256;
pub mod sha512;
