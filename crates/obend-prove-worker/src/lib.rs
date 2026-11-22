#![forbid(unsafe_code)]
//! Phase-1 hardened proving worker pool and deterministic parallel PoW / challenge grinder.
//!
//! Quarried cleanly from:
//! - `breadstuffs/dreggnet-prove-service/src/lib.rs` and `breadstuffs/node/src/prove_pool.rs`
//!   (moving CPU-heavy proving strictly off the commit/state write lock, closing the 5-minute
//!   inline `state.write()` wedge `F-DOS-1`, while burning `dreggnet-game-board::prove_tug_match`
//!   and its `20-15-5=0` `win_leaf` mannequin `B2`).
//! - `breadstuffs/vendor/plonky3-challenger-82cfad73/src/grinding_challenger.rs` (porting the
//!   `c = 1/4` contiguous ascending windowed parallel min `windowed_find_map_first` onto pure
//!   `std::thread::scope` with zero rayon or Plonky3 dependencies).
//!
//! ## Hardening invariants
//! 1. **Off-lock execution:** Worker threads hold the internal state mutex only for O(log K) queue
//!    pickup and settlement; backend proving runs completely off-lock.
//! 2. **Bounded memory:** Both the pending queue (`queue_depth`) and terminal tombstones
//!    (`max_retained_settled`, evicted by deterministic LRU and optional TTL) are strictly bounded.
//!    No map or index grows without bound under sustained throughput.
//! 3. **Backpressure & deduplication:** Queue saturation fails fast with `EnqueueError::QueueFull`
//!    without blocking callers; idempotent `JobId` and 256-bit digest deduplication returns the
//!    existing live or completed `JobId` without re-queuing or double-executing the backend.
//! 4. **Epoch cancellation:** `cancel_stale_epoch` removes stale queued jobs immediately (freeing
//!    queue capacity), flips cooperative `CancelToken`s on stale in-flight jobs, discards stale
//!    completions as `JobStatus::Cancelled`, and rejects subsequent stale-epoch submissions.
//! 5. **Exact `1T == NT` grinder determinism:** `windowed_find_map_first_with_threads` returns the
//!    exact lowest matching unit index across any thread count `1..=32` and any window size `>= 1`.

pub mod grinder;
pub mod service;

pub use grinder::{
    default_grind_threads, default_grind_window, grind_pow, grind_pow_cancellable, grind_pow_with,
    pow_digest, sha256, verify_pow, windowed_find_map_first, windowed_find_map_first_cancellable,
    windowed_find_map_first_indexed, windowed_find_map_first_with_threads, GRIND_TASKS_PER_WORKER,
    GRIND_WINDOW_C_DEN, GRIND_WINDOW_C_NUM, GRIND_WINDOW_MIN_UNITS, MAX_DEFAULT_GRIND_THREADS,
    POW_DOMAIN_TAG,
};
pub use service::{
    Backend, CancelReport, CancelToken, CancellableBackend, EnqueueError, EnqueueOutcome, JobId,
    JobStatus, Metrics, ProveService, ProveServiceConfig, WaitError, DEFAULT_MAX_RETAINED_SETTLED,
    DEFAULT_QUEUE_DEPTH, DEFAULT_WORKERS,
};
