//! Deterministic parallel `c = 1/4` windowed PoW / challenge grinder (`windowed_find_map_first`).
//!
//! Quarried cleanly from `breadstuffs/vendor/plonky3-challenger-82cfad73/src/grinding_challenger.rs`
//! onto pure `std::thread::scope` with zero external crate dependencies.
//!
//! ## Exact `1T == NT` lowest-nonce determinism
//! Upstream rayon `find_any` / `find_map_any` returns whichever worker thread finishes first,
//! causing non-deterministic PoW witnesses and non-reproducible Fiat-Shamir transcripts/proofs.
//! Upstream `find_first` preserves determinism but loses parallelism (measured at scale `1.00x`
//! across 12 threads) because workers steal far-above subranges that cannot abort until a lower
//! match is published.
//!
//! `windowed_find_map_first` scans `0..span` in contiguous ascending windows of `window` units
//! (default `c = 1/4` of `2^bits`, giving `~1.126x` expected total work while dividing critical
//! path across `T` threads). Inside each window:
//! - Units are eagerly partitioned into `worker_count * GRIND_TASKS_PER_WORKER` ascending chunks
//!   claimed atomically via `next_chunk`.
//! - A shared `best_unit` atomic upper bound (`AtomicU64`, initialized to `u64::MAX`) lets workers
//!   prune chunks strictly above an already-discovered match while **exhaustively verifying every
//!   unit strictly below `best_unit`**.
//! - Every worker's lowest hit is reduced via `min_by_key(|(unit, _)| *unit)`.
//!
//! Because windows are contiguous and ascending and every unit `< u*` in the first non-empty
//! window is checked before termination, the result is **bit-exact identical** to sequential
//! `(0..span).find_map(scan)` for EVERY thread count `threads >= 1` and EVERY `window >= 1`.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::service::CancelToken;

/// Minimax window fraction numerator (`c = 1/4`, from `grinding_challenger.rs:114`).
pub const GRIND_WINDOW_C_NUM: u64 = 1;

/// Minimax window fraction denominator (`c = 1/4`, from `grinding_challenger.rs:115`).
pub const GRIND_WINDOW_C_DEN: u64 = 4;

/// Minimum window width in units so tiny bit targets do not degenerate into barrier overhead
/// (`grinding_challenger.rs:119`).
pub const GRIND_WINDOW_MIN_UNITS: u64 = 64;

/// Number of eager chunks per worker inside a window (`grinding_challenger.rs:124`).
pub const GRIND_TASKS_PER_WORKER: u64 = 8;

/// Upper clamp for [`default_grind_threads`].
pub const MAX_DEFAULT_GRIND_THREADS: usize = 32;

/// Domain separation tag for the built-in deterministic SHA-256 PoW grinder.
pub const POW_DOMAIN_TAG: &[u8; 18] = b"obend-pow-grind-v1";

/// Computes the default `c = 1/4` search window in units for a `bits`-bit PoW grind at
/// `candidates_per_unit` candidates per unit (`grinding_challenger.rs:129-143`).
#[inline]
pub const fn default_grind_window(bits: usize, candidates_per_unit: u64) -> u64 {
    let shift = if bits >= 63 { 63 } else { bits };
    let expected = 1u128 << shift;
    let per_unit = if candidates_per_unit == 0 {
        1u128
    } else {
        candidates_per_unit as u128
    };
    let denom = (GRIND_WINDOW_C_DEN as u128) * per_unit;
    let units = (expected * (GRIND_WINDOW_C_NUM as u128)) / denom;
    if units < (GRIND_WINDOW_MIN_UNITS as u128) {
        GRIND_WINDOW_MIN_UNITS
    } else if units > (u64::MAX as u128) {
        u64::MAX
    } else {
        units as u64
    }
}

/// Returns the default worker thread count for parallel grinding (`available_parallelism` clamped
/// to `1..=32`).
pub fn default_grind_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get().clamp(1, MAX_DEFAULT_GRIND_THREADS))
        .unwrap_or(1)
}

/// Scans `0..span` in contiguous ascending windows of `window` units using
/// [`default_grind_threads`] OS threads and returns the value produced by the **lowest** unit
/// index that yields `Some`.
#[inline]
pub fn windowed_find_map_first<T, S>(span: u64, window: u64, scan: S) -> Option<T>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync,
{
    windowed_find_map_first_with_threads(span, window, default_grind_threads(), scan)
}

/// Scans `0..span` in contiguous ascending windows of `window` units across `threads` OS threads
/// (`std::thread::scope`) and returns the value produced by the **lowest** unit index that yields
/// `Some`.
///
/// Guaranteed bit-exact identical to `(0..span).find_map(scan)` for every `threads >= 1` and every
/// `window >= 1`.
#[inline]
pub fn windowed_find_map_first_with_threads<T, S>(
    span: u64,
    window: u64,
    threads: usize,
    scan: S,
) -> Option<T>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync,
{
    windowed_find_map_first_indexed(span, window, threads, scan).map(|(_, value)| value)
}

/// Like [`windowed_find_map_first_with_threads`], returning both the winning lowest `unit` index
/// and its mapped value `T`.
pub fn windowed_find_map_first_indexed<T, S>(
    span: u64,
    window: u64,
    threads: usize,
    scan: S,
) -> Option<(u64, T)>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync,
{
    windowed_find_map_first_impl(span, window, threads, None, scan)
}

/// Cooperatively cancellable variant of [`windowed_find_map_first_indexed`].
///
/// Checks `cancel.is_cancelled()` between windows and across chunk boundaries so a stale epoch
/// aborts promptly. When uncancelled, returns the exact same lowest `(unit, T)`.
pub fn windowed_find_map_first_cancellable<T, S>(
    span: u64,
    window: u64,
    threads: usize,
    cancel: &CancelToken,
    scan: S,
) -> Option<(u64, T)>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync,
{
    windowed_find_map_first_impl(span, window, threads, Some(cancel), scan)
}

fn windowed_find_map_first_impl<T, S>(
    span: u64,
    window: u64,
    threads: usize,
    cancel: Option<&CancelToken>,
    scan: S,
) -> Option<(u64, T)>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync,
{
    if span == 0 {
        return None;
    }

    let window = window.max(1).min(span);
    let threads = threads.max(1);
    let scan_ref = &scan;

    let mut lo = 0u64;
    while lo < span {
        if cancel.is_some_and(CancelToken::is_cancelled) {
            return None;
        }
        let hi = lo.saturating_add(window).min(span);
        let len = hi - lo;
        let worker_count = (threads as u64).min(len) as usize;

        if worker_count <= 1 {
            for unit in lo..hi {
                if cancel.is_some_and(CancelToken::is_cancelled) {
                    return None;
                }
                if let Some(found) = scan_ref(unit) {
                    return Some((unit, found));
                }
            }
            lo = hi;
            continue;
        }

        // Eagerly split the window into ascending chunks claimed via `next_chunk`.
        // `best_unit` is initialized to `u64::MAX`, which is strictly greater than every valid
        // unit `u < span <= u64::MAX`, making it an exact collision-free upper-bound sentinel.
        let target_chunks = (worker_count as u64)
            .saturating_mul(GRIND_TASKS_PER_WORKER)
            .max(1)
            .min(len);
        let chunk_size = len.div_ceil(target_chunks).max(1);
        let next_chunk = AtomicU64::new(0);
        let best_unit = AtomicU64::new(u64::MAX);

        let window_hit: Option<(u64, T)> = std::thread::scope(|scope| {
            let mut handles = Vec::with_capacity(worker_count);
            for _ in 0..worker_count {
                let next_chunk_ref = &next_chunk;
                let best_unit_ref = &best_unit;
                handles.push(scope.spawn(move || -> Option<(u64, T)> {
                    loop {
                        if cancel.is_some_and(CancelToken::is_cancelled) {
                            return None;
                        }
                        let chunk_idx = next_chunk_ref.fetch_add(1, Ordering::Relaxed);
                        let offset = chunk_idx.saturating_mul(chunk_size);
                        let chunk_lo = lo.saturating_add(offset);
                        if chunk_lo >= hi {
                            return None;
                        }
                        // Because chunks are issued strictly ascending, once `chunk_lo >= best`
                        // no remaining chunk can possibly contain a unit strictly below `best`.
                        let current_best = best_unit_ref.load(Ordering::Acquire);
                        if chunk_lo >= current_best {
                            return None;
                        }

                        let chunk_hi = chunk_lo.saturating_add(chunk_size).min(hi);
                        for unit in chunk_lo..chunk_hi {
                            if cancel.is_some_and(CancelToken::is_cancelled) {
                                return None;
                            }
                            if unit >= best_unit_ref.load(Ordering::Acquire) {
                                return None;
                            }
                            if let Some(found) = scan_ref(unit) {
                                best_unit_ref.fetch_min(unit, Ordering::AcqRel);
                                // Every remaining unit in this chunk and every future chunk is
                                // strictly > `unit`, so this worker's global best is finalized.
                                return Some((unit, found));
                            }
                        }
                    }
                }));
            }

            let mut best: Option<(u64, T)> = None;
            for handle in handles {
                if let Some((unit, val)) = handle.join().expect("grinder worker thread panicked") {
                    match &best {
                        Some((best_u, _)) if unit >= *best_u => {}
                        _ => best = Some((unit, val)),
                    }
                }
            }
            best
        });

        if cancel.is_some_and(CancelToken::is_cancelled) {
            return None;
        }
        if window_hit.is_some() {
            return window_hit;
        }
        lo = hi;
    }

    None
}

// ---------------------------------------------------------------------------
// Pure-Rust FIPS 180-4 SHA-256 + Domain-Separated PoW Challenge Grinder
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Computes FIPS 180-4 SHA-256 of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = SHA256_H0;
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity((data.len() + 9 + 63) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[4 * i],
                block[4 * i + 1],
                block[4 * i + 2],
                block[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// Computes the domain-separated PoW digest `SHA-256(POW_DOMAIN_TAG || transcript || nonce_le)`.
#[inline]
pub fn pow_digest(transcript: &[u8; 32], nonce: u64) -> [u8; 32] {
    let mut preimage = [0u8; 18 + 32 + 8];
    preimage[..18].copy_from_slice(POW_DOMAIN_TAG);
    preimage[18..50].copy_from_slice(transcript);
    preimage[50..58].copy_from_slice(&nonce.to_le_bytes());
    sha256(&preimage)
}

/// Checks whether `nonce` satisfies `bits` low zero bits on [`pow_digest`].
#[inline]
pub fn verify_pow(transcript: &[u8; 32], bits: usize, nonce: u64) -> bool {
    if bits == 0 {
        return true;
    }
    if bits > 64 {
        return false;
    }
    let digest = pow_digest(transcript, nonce);
    let sample = u64::from_le_bytes([
        digest[0], digest[1], digest[2], digest[3], digest[4], digest[5], digest[6], digest[7],
    ]);
    if bits == 64 {
        sample == 0
    } else {
        (sample & ((1u64 << bits) - 1)) == 0
    }
}

/// Finds the globally lowest `nonce` in `0..u64::MAX` satisfying `bits` low zero bits using the
/// default `c = 1/4` window and [`default_grind_threads`].
pub fn grind_pow(transcript: &[u8; 32], bits: usize) -> Option<u64> {
    if bits == 0 {
        return Some(0);
    }
    if bits >= 64 {
        return None;
    }
    grind_pow_with(
        transcript,
        bits,
        u64::MAX,
        default_grind_window(bits, 1),
        default_grind_threads(),
    )
}

/// Finds the globally lowest `nonce` in `0..span` satisfying `bits` low zero bits using explicit
/// `window` and `threads`.
pub fn grind_pow_with(
    transcript: &[u8; 32],
    bits: usize,
    span: u64,
    window: u64,
    threads: usize,
) -> Option<u64> {
    if bits == 0 {
        return (span > 0).then_some(0);
    }
    if bits >= 64 {
        return None;
    }
    let transcript = *transcript;
    windowed_find_map_first_with_threads(span, window, threads, move |nonce| {
        verify_pow(&transcript, bits, nonce).then_some(nonce)
    })
}

/// Cooperatively cancellable PoW grinder returning the globally lowest `nonce` in `0..span`.
pub fn grind_pow_cancellable(
    transcript: &[u8; 32],
    bits: usize,
    span: u64,
    window: u64,
    threads: usize,
    cancel: &CancelToken,
) -> Option<u64> {
    if bits == 0 {
        return (!cancel.is_cancelled() && span > 0).then_some(0);
    }
    if bits >= 64 {
        return None;
    }
    let transcript = *transcript;
    windowed_find_map_first_cancellable(span, window, threads, cancel, move |nonce| {
        verify_pow(&transcript, bits, nonce).then_some(nonce)
    })
    .map(|(nonce, _)| nonce)
}
