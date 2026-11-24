//! Conformance, bounded-memory, backpressure, epoch-cancellation, and multi-threaded
//! determinism test suite for `obend-prove-worker`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use obend_prove_worker::{
    default_grind_window, grind_pow_cancellable, grind_pow_with, sha256, verify_pow,
    windowed_find_map_first_with_threads, CancelToken, EnqueueError, JobId, JobStatus,
    ProveService, ProveServiceConfig, WaitError, GRIND_WINDOW_MIN_UNITS,
};

struct Gate {
    started: AtomicUsize,
    open: Mutex<bool>,
    cv: Condvar,
}

impl Gate {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            started: AtomicUsize::new(0),
            open: Mutex::new(false),
            cv: Condvar::new(),
        })
    }

    fn enter(&self) {
        self.started.fetch_add(1, Ordering::SeqCst);
        let mut open = self.open.lock().expect("gate mutex");
        while !*open {
            open = self.cv.wait(open).expect("gate condvar");
        }
    }

    fn release(&self) {
        *self.open.lock().expect("gate mutex") = true;
        self.cv.notify_all();
    }

    fn wait_started(&self, target: usize) {
        let deadline = Instant::now() + Duration::from_secs(5);
        while self.started.load(Ordering::SeqCst) < target {
            assert!(
                Instant::now() < deadline,
                "workers never reached {target} started (got {})",
                self.started.load(Ordering::SeqCst)
            );
            std::thread::sleep(Duration::from_millis(2));
        }
    }
}

// ---------------------------------------------------------------------------
// 1. Off-lock concurrency & bounded-queue QueueFull backpressure
// ---------------------------------------------------------------------------

#[test]
fn n_workers_prove_concurrently_off_lock_and_enqueue_never_blocks() {
    let gate = Gate::new();
    let g = gate.clone();
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(move |x: u64| {
            g.enter();
            Ok(x * 3)
        }),
        3,
        16,
    );

    let ids: Vec<JobId> = (1..=3)
        .map(|i| svc.enqueue(i).expect("accepted into pool"))
        .collect();
    gate.wait_started(3);

    let m = svc.metrics();
    assert_eq!(m.in_flight, 3, "all 3 workers must prove in parallel");
    for id in &ids {
        assert_eq!(svc.status(*id), JobStatus::Proving);
    }

    // While all 3 workers are blocked inside proving, enqueue + status + metrics must remain
    // strictly off-lock and return immediately.
    let t0 = Instant::now();
    let extra = svc.enqueue(100).expect("queued while workers busy");
    assert!(
        t0.elapsed() < Duration::from_millis(200),
        "enqueue blocked for {:?} while workers were proving",
        t0.elapsed()
    );
    assert_eq!(svc.status(extra), JobStatus::Queued);

    gate.release();
    assert_eq!(svc.wait(ids[0]), Ok(3));
    assert_eq!(svc.wait(ids[1]), Ok(6));
    assert_eq!(svc.wait(ids[2]), Ok(9));
    assert_eq!(svc.wait(extra), Ok(300));

    let m = svc.metrics();
    assert_eq!(m.completed, 4);
    assert_eq!(m.in_flight, 0);
    assert_eq!(m.queued, 0);
}

#[test]
fn full_queue_returns_queue_full_backpressure_without_blocking() {
    let gate = Gate::new();
    let g = gate.clone();
    // 1 worker + queue_depth 2 => 1 in-flight + 2 queued = 3 admitted; 4th refuses with QueueFull.
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(move |x: u64| {
            g.enter();
            Ok(x * 2)
        }),
        1,
        2,
    );

    let j1 = svc.enqueue(1).expect("admitted to worker");
    gate.wait_started(1);

    let j2 = svc.enqueue(2).expect("buffered slot 1");
    let j3 = svc.enqueue(3).expect("buffered slot 2");

    let t0 = Instant::now();
    let refused = svc.enqueue(4);
    assert_eq!(refused, Err(EnqueueError::QueueFull { capacity: 2 }));
    assert!(
        t0.elapsed() < Duration::from_millis(200),
        "QueueFull backpressure must return fast: {:?}",
        t0.elapsed()
    );
    assert_eq!(svc.metrics().dropped, 1);

    gate.release();
    assert_eq!(svc.wait(j1), Ok(2));
    assert_eq!(svc.wait(j2), Ok(4));
    assert_eq!(svc.wait(j3), Ok(6));

    let m = svc.metrics();
    assert_eq!(m.enqueued, 3);
    assert_eq!(m.completed, 3);
    assert_eq!(m.dropped, 1);
}

// ---------------------------------------------------------------------------
// 2. Bounded memory eviction (10,000 completed jobs, deterministic LRU, TTL)
// ---------------------------------------------------------------------------

#[test]
fn ten_thousand_completed_jobs_retain_at_most_max_retained() {
    let max_retained = 64usize;
    let svc = ProveService::<u64, u64>::spawn_with_config(
        Arc::new(|x: u64| Ok(x.wrapping_mul(7))),
        ProveServiceConfig {
            workers: 4,
            queue_depth: 512,
            max_retained_settled: max_retained,
            settled_ttl: None,
        },
    );

    const TOTAL_JOBS: u64 = 10_000;
    let mut ids = Vec::with_capacity(TOTAL_JOBS as usize);
    for i in 0..TOTAL_JOBS {
        let mut key = [0u8; 32];
        key[..8].copy_from_slice(&i.to_le_bytes());
        loop {
            match svc.enqueue_dedup(key, 1, i) {
                Ok(out) => {
                    assert!(!out.deduplicated);
                    ids.push(out.id);
                    break;
                }
                Err(EnqueueError::QueueFull { .. }) => {
                    std::thread::yield_now();
                }
                Err(e) => panic!("unexpected enqueue error at job {i}: {e}"),
            }
        }
        // Check bounded settled cap periodically mid-flight.
        if i % 500 == 0 {
            assert!(
                svc.retained_settled() <= max_retained,
                "retained settled exceeded cap mid-flight: {} > {max_retained}",
                svc.retained_settled()
            );
        }
    }

    // Drain until all 10,000 jobs complete.
    let deadline = Instant::now() + Duration::from_secs(20);
    while svc.metrics().completed < TOTAL_JOBS {
        assert!(
            Instant::now() < deadline,
            "timed out waiting for 10,000 jobs (completed={})",
            svc.metrics().completed
        );
        std::thread::sleep(Duration::from_millis(2));
    }

    let m = svc.metrics();
    assert_eq!(m.completed, TOTAL_JOBS);
    assert_eq!(m.in_flight, 0);
    assert_eq!(m.queued, 0);
    assert!(
        svc.retained_settled() <= max_retained,
        "retained settled {} > {max_retained}",
        svc.retained_settled()
    );
    assert!(
        svc.tracked_jobs() <= max_retained,
        "tracked jobs {} > {max_retained}",
        svc.tracked_jobs()
    );
    assert!(
        svc.dedup_entries() <= max_retained,
        "dedup index leaked: {} > {max_retained}",
        svc.dedup_entries()
    );
    assert_eq!(m.evicted_capacity, TOTAL_JOBS - max_retained as u64);
    assert_eq!(m.evicted, TOTAL_JOBS - max_retained as u64);

    // Earliest job must have been evicted and read Unknown.
    assert_eq!(svc.status(ids[0]), JobStatus::Unknown);
}

#[test]
fn deterministic_lru_eviction_keeps_recently_polled_entries() {
    let svc = ProveService::<u64, u64>::spawn_with_config(
        Arc::new(|x: u64| Ok(x + 10)),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 16,
            max_retained_settled: 2,
            settled_ttl: None,
        },
    );

    let j1 = svc.enqueue(1).expect("j1");
    assert_eq!(svc.wait(j1), Ok(11));
    let j2 = svc.enqueue(2).expect("j2");
    assert_eq!(svc.wait(j2), Ok(12));

    // Poll j1 so j1 becomes more recently used than j2.
    assert_eq!(svc.status(j1), JobStatus::Done(Box::new(11)));

    // Completing j3 must evict j2 (LRU) while keeping j1 and j3!
    let j3 = svc.enqueue(3).expect("j3");
    assert_eq!(svc.wait(j3), Ok(13));

    assert_eq!(svc.retained_settled(), 2);
    assert_eq!(svc.status(j1), JobStatus::Done(Box::new(11)));
    assert_eq!(svc.status(j3), JobStatus::Done(Box::new(13)));
    assert_eq!(svc.status(j2), JobStatus::Unknown);
    assert_eq!(svc.metrics().evicted_capacity, 1);
}

#[test]
fn settled_ttl_eviction_prunes_expired_entries() {
    let svc = ProveService::<u64, u64>::spawn_with_config(
        Arc::new(|x: u64| Ok(x)),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 8,
            max_retained_settled: 64,
            settled_ttl: Some(Duration::from_millis(35)),
        },
    );

    let j1 = svc.enqueue(42).expect("j1");
    assert_eq!(svc.wait(j1), Ok(42));
    assert_eq!(svc.retained_settled(), 1);

    std::thread::sleep(Duration::from_millis(60));
    let pruned = svc.prune_expired();
    assert_eq!(pruned, 1);
    assert_eq!(svc.retained_settled(), 0);
    assert_eq!(svc.tracked_jobs(), 0);
    assert_eq!(svc.status(j1), JobStatus::Unknown);
    assert_eq!(svc.metrics().evicted_ttl, 1);
}

#[test]
fn wait_delivers_result_even_when_max_retained_is_zero() {
    let gate = Gate::new();
    let g = gate.clone();
    let svc = Arc::new(ProveService::<u64, u64>::spawn_with_config(
        Arc::new(move |x: u64| {
            g.enter();
            Ok(x + 99)
        }),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 4,
            max_retained_settled: 0,
            settled_ttl: None,
        },
    ));

    let j1 = svc.enqueue(1).expect("j1");
    gate.wait_started(1);

    let svc_waiter = svc.clone();
    let waiter = std::thread::spawn(move || svc_waiter.wait(j1));
    std::thread::sleep(Duration::from_millis(10));
    gate.release();

    assert_eq!(waiter.join().expect("waiter thread"), Ok(100));
    assert_eq!(svc.retained_settled(), 0);
    assert_eq!(svc.status(j1), JobStatus::Unknown);
    assert_eq!(svc.metrics().evicted_capacity, 1);
}

// ---------------------------------------------------------------------------
// 3. Idempotent job-ID & 256-bit digest deduplication
// ---------------------------------------------------------------------------

#[test]
fn idempotent_job_id_and_digest_deduplication_runs_backend_once() {
    let calls = Arc::new(AtomicUsize::new(0));
    let gate = Gate::new();
    let c = calls.clone();
    let g = gate.clone();

    let svc = ProveService::<u64, u64>::spawn_with_config(
        Arc::new(move |x: u64| {
            c.fetch_add(1, Ordering::SeqCst);
            g.enter();
            Ok(x * 10)
        }),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 1,
            max_retained_settled: 32,
            settled_ttl: None,
        },
    );

    // 1. Explicit JobId dedup while Proving and even when queue is full.
    let first = svc
        .enqueue_with_id(JobId(77), 1, 5)
        .expect("initial explicit id");
    assert_eq!(first.id, JobId(77));
    assert!(!first.deduplicated);
    gate.wait_started(1);

    // Fill the single pending queue slot with a digest-keyed job.
    let key = sha256(b"epoch-1-turn-commitment");
    let queued = svc
        .enqueue_dedup(key, 1, 9)
        .expect("fills the 1 queue slot");
    assert!(!queued.deduplicated);

    // Queue is now full, yet duplicate submissions for BOTH JobId(77) (Proving) and `key`
    // (Queued) must succeed idempotently without returning QueueFull or double-running!
    let dup_proving = svc
        .enqueue_with_id(JobId(77), 1, 5)
        .expect("dedup while proving");
    assert!(dup_proving.deduplicated);
    assert_eq!(dup_proving.id, JobId(77));

    let dup_queued = svc.enqueue_dedup(key, 1, 9).expect("dedup while queued");
    assert!(dup_queued.deduplicated);
    assert_eq!(dup_queued.id, queued.id);

    // A genuinely distinct key IS refused with QueueFull.
    assert_eq!(
        svc.enqueue_dedup(sha256(b"other-key"), 1, 11),
        Err(EnqueueError::QueueFull { capacity: 1 })
    );

    gate.release();
    assert_eq!(svc.wait(JobId(77)), Ok(50));
    assert_eq!(svc.wait(queued.id), Ok(90));
    assert_eq!(calls.load(Ordering::SeqCst), 2, "backend ran exactly twice");

    // Dedup also holds after Done!
    let dup_done_id = svc
        .enqueue_with_id(JobId(77), 1, 5)
        .expect("dedup after done");
    assert!(dup_done_id.deduplicated);
    let dup_done_key = svc.enqueue_dedup(key, 1, 9).expect("dedup key after done");
    assert!(dup_done_key.deduplicated);
    assert_eq!(dup_done_key.id, queued.id);
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert_eq!(svc.metrics().deduplicated, 4);
}

// ---------------------------------------------------------------------------
// 4. Epoch cancellation (queued eviction, in-flight suppression, stale refusal)
// ---------------------------------------------------------------------------

#[test]
fn cancel_stale_epoch_evicts_queued_cancels_in_flight_and_rejects_stale_submissions() {
    let gate = Gate::new();
    let backend_calls = Arc::new(AtomicUsize::new(0));
    let observed_cancel = Arc::new(AtomicUsize::new(0));

    let g = gate.clone();
    let calls = backend_calls.clone();
    let obs = observed_cancel.clone();

    let svc = ProveService::<u64, u64>::spawn_cancellable(
        Arc::new(move |x: u64, token: &CancelToken| {
            calls.fetch_add(1, Ordering::SeqCst);
            g.enter();
            if token.is_cancelled() {
                obs.fetch_add(1, Ordering::SeqCst);
                return Err("cooperative cancel".into());
            }
            Ok(x * 100)
        }),
        ProveServiceConfig {
            workers: 1,
            queue_depth: 2,
            max_retained_settled: 64,
            settled_ttl: None,
        },
    );

    // Epoch 1: 1 job in-flight + 2 jobs queued (queue now full).
    let stale_in_flight = svc.enqueue_with_epoch(1, 10).expect("epoch 1 in-flight");
    gate.wait_started(1);
    let stale_q1 = svc.enqueue_with_epoch(1, 20).expect("epoch 1 queued 1");
    let stale_q2 = svc.enqueue_with_epoch(2, 30).expect("epoch 2 queued 2");

    assert_eq!(
        svc.enqueue_with_epoch(3, 40),
        Err(EnqueueError::QueueFull { capacity: 2 })
    );

    // Advance epoch floor to 3: both stale queued jobs (epochs 1 & 2) must be evicted immediately
    // from the queue (freeing queue slots!) and the in-flight epoch-1 job marked cancelled.
    let report = svc.cancel_stale_epoch(3);
    assert_eq!(report.min_active_epoch, 3);
    assert_eq!(report.cancelled_queued, 2);
    assert_eq!(report.marked_in_flight, 1);

    assert_eq!(svc.status(stale_q1), JobStatus::Cancelled);
    assert_eq!(svc.status(stale_q2), JobStatus::Cancelled);
    assert_eq!(svc.wait(stale_q1), Err(WaitError::Cancelled(stale_q1)));
    assert_eq!(svc.wait(stale_q2), Err(WaitError::Cancelled(stale_q2)));

    // Stale admissions are rejected immediately.
    assert_eq!(
        svc.enqueue_with_epoch(2, 99),
        Err(EnqueueError::StaleEpoch {
            job_epoch: 2,
            min_active_epoch: 3
        })
    );

    // Freed queue slots immediately accept fresh epoch-3 jobs!
    let fresh = svc
        .enqueue_with_epoch(3, 7)
        .expect("fresh epoch-3 job admitted into freed queue");

    // Release gate: in-flight epoch-1 job observes CancelToken and settles Cancelled; stale queued
    // jobs never ran; fresh epoch-3 job executes and settles Done(700).
    gate.release();
    assert_eq!(
        svc.wait(stale_in_flight),
        Err(WaitError::Cancelled(stale_in_flight))
    );
    assert_eq!(svc.wait(fresh), Ok(700));
    assert_eq!(observed_cancel.load(Ordering::SeqCst), 1);
    assert_eq!(
        backend_calls.load(Ordering::SeqCst),
        2,
        "only stale_in_flight and fresh ran; stale_q1 and stale_q2 never entered backend"
    );

    let m = svc.metrics();
    assert_eq!(m.cancelled, 3);
    assert_eq!(m.completed, 1);
    assert_eq!(m.rejected_stale_epoch, 1);
}

#[test]
fn panicking_backend_settles_failed_without_poisoning_pool() {
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(|x: u64| {
            if x == 0 {
                panic!("boom-on-zero");
            }
            Ok(x + 1)
        }),
        1,
        4,
    );

    let bad = svc.enqueue(0).expect("bad");
    let good = svc.enqueue(41).expect("good");
    match svc.wait(bad) {
        Err(WaitError::Failed(msg)) => assert!(msg.contains("boom-on-zero"), "got {msg}"),
        other => panic!("expected Failed panic error, got {other:?}"),
    }
    assert_eq!(svc.wait(good), Ok(42));
    assert_eq!(svc.metrics().failed, 1);
    assert_eq!(svc.metrics().completed, 1);
}

// ---------------------------------------------------------------------------
// 5. Deterministic parallel windowed_find_map_first (1T == 2T == 8T == 16T == 32T)
// ---------------------------------------------------------------------------

#[test]
fn sha256_matches_nist_abc_kat_and_default_window_follows_quarter_law() {
    let digest = sha256(b"abc");
    assert_eq!(
        digest,
        [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
            0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
            0xf2, 0x00, 0x15, 0xad,
        ]
    );

    // c = 1/4: at bits=16, 2^16 / 4 = 16_384; at 4 lanes = 4_096; tiny bits clamp to 64.
    assert_eq!(default_grind_window(16, 1), 16_384);
    assert_eq!(default_grind_window(16, 4), 4_096);
    assert_eq!(default_grind_window(4, 1), GRIND_WINDOW_MIN_UNITS);
    assert_eq!(default_grind_window(0, 1), GRIND_WINDOW_MIN_UNITS);
    assert_eq!(default_grind_window(63, 1), 1u64 << 61);
    assert_eq!(default_grind_window(128, 1), 1u64 << 61);
}

#[test]
fn pow_grinder_is_bit_exact_deterministic_across_1t_2t_4t_8t_16t_32t_and_windows() {
    let transcripts = [
        sha256(b"obend-whir-ext4-transcript-0"),
        sha256(b"obend-whir-pcs61-transcript-1"),
        sha256(b"obend-tower256-transcript-2"),
    ];

    for (idx, transcript) in transcripts.iter().enumerate() {
        for &bits in &[0usize, 8, 11, 13] {
            let default_win = default_grind_window(bits, 1);
            let baseline_1t = grind_pow_with(transcript, bits, 1 << 24, default_win, 1)
                .expect("1T witness exists");
            assert!(verify_pow(transcript, bits, baseline_1t));

            // Strictly verify minimality: no nonce < baseline_1t satisfies the predicate.
            if bits > 0 {
                for lower in 0..baseline_1t {
                    assert!(
                        !verify_pow(transcript, bits, lower),
                        "transcript {idx} bits={bits}: lower nonce {lower} < {baseline_1t} was valid!"
                    );
                }
            }

            // Sweep thread counts 1, 2, 4, 8, 16, 32 AND multiple window sizes.
            for &threads in &[1usize, 2, 4, 8, 16, 32] {
                for &win in &[1u64, 17, 64, 257, default_win, 4096] {
                    let got = grind_pow_with(transcript, bits, 1 << 24, win, threads)
                        .expect("NT witness exists");
                    assert_eq!(
                        got, baseline_1t,
                        "determinism mismatch for transcript={idx} bits={bits} threads={threads} window={win}"
                    );
                }
            }
        }
    }
}

#[test]
fn adversarial_slow_low_thread_fast_high_thread_still_returns_lowest_nonce() {
    // Nonces 7 and 900 are both valid; nonce 7 is artificially delayed so a higher-indexed worker
    // ALWAYS discovers 900 long before chunk 0 finishes checking 7.
    // An unordered `find_any` grinder would return 900; `windowed_find_map_first` MUST return 7.
    let lowest = 7u64;
    let decoy = 900u64;

    for &threads in &[1usize, 2, 8, 16] {
        for &window in &[64u64, 1024, 4096] {
            let found = windowed_find_map_first_with_threads(2048, window, threads, |u| {
                if u == lowest {
                    std::thread::sleep(Duration::from_millis(15));
                    Some(u * 10 + 1)
                } else if u == decoy {
                    Some(u * 10 + 1)
                } else {
                    None
                }
            });
            assert_eq!(
                found,
                Some(lowest * 10 + 1),
                "higher fast thread stole lowest witness at threads={threads} window={window}"
            );
        }
    }
}

#[test]
fn windowed_find_map_first_handles_boundary_spans_and_misses() {
    assert_eq!(windowed_find_map_first_with_threads(0, 64, 8, Some), None);
    assert_eq!(
        windowed_find_map_first_with_threads(1, 64, 8, |u| (u == 0).then_some(99u64)),
        Some(99)
    );
    assert_eq!(
        windowed_find_map_first_with_threads(500, 0, 8, |u| (u == 499).then_some(u)),
        Some(499)
    );
    assert_eq!(
        windowed_find_map_first_with_threads(500, 10_000, 16, |u| (u == 499).then_some(u)),
        Some(499)
    );
    assert_eq!(
        windowed_find_map_first_with_threads::<u64, _>(500, 37, 8, |_| None),
        None
    );
}

#[test]
fn prove_service_drives_cancellable_deterministic_grinder_end_to_end() {
    #[derive(Clone)]
    struct PowJob {
        transcript: [u8; 32],
        bits: usize,
        threads: usize,
    }

    let svc = ProveService::<PowJob, u64>::spawn_cancellable(
        Arc::new(|job: PowJob, cancel: &CancelToken| {
            let win = default_grind_window(job.bits, 1);
            grind_pow_cancellable(&job.transcript, job.bits, 1 << 28, win, job.threads, cancel)
                .ok_or_else(|| "grind cancelled or exhausted".to_string())
        }),
        ProveServiceConfig {
            workers: 2,
            queue_depth: 8,
            max_retained_settled: 16,
            settled_ttl: None,
        },
    );

    let transcript = sha256(b"obend-end-to-end-epoch-1");
    let j_1t = svc
        .enqueue_with_epoch(
            1,
            PowJob {
                transcript,
                bits: 12,
                threads: 1,
            },
        )
        .expect("enqueue 1T");
    let j_8t = svc
        .enqueue_with_epoch(
            1,
            PowJob {
                transcript,
                bits: 12,
                threads: 8,
            },
        )
        .expect("enqueue 8T");

    let n1 = svc.wait(j_1t).expect("1T completes");
    let n8 = svc.wait(j_8t).expect("8T completes");
    assert_eq!(n1, n8);
    assert!(verify_pow(&transcript, 12, n1));

    // Launch an intentionally hard (bits=28) job at epoch 1 and cancel it cooperatively by
    // advancing to epoch 2.
    let hard = svc
        .enqueue_with_epoch(
            1,
            PowJob {
                transcript: sha256(b"obend-cancel-hard"),
                bits: 28,
                threads: 2,
            },
        )
        .expect("enqueue hard");

    // Wait briefly until the worker picks it up (or even while queued).
    std::thread::sleep(Duration::from_millis(15));
    let t0 = Instant::now();
    svc.cancel_stale_epoch(2);
    assert_eq!(svc.wait(hard), Err(WaitError::Cancelled(hard)));
    assert!(
        t0.elapsed() < Duration::from_secs(2),
        "cooperative cancellation took too long: {:?}",
        t0.elapsed()
    );
}

#[test]
fn stale_epoch_discards_plain_non_cancellable_backend_ok_output() {
    let gate = Gate::new();
    let g = gate.clone();
    // Plain backend ignores CancelToken and always returns Ok(x * 5).
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(move |x: u64| {
            g.enter();
            Ok(x * 5)
        }),
        1,
        4,
    );

    let stale = svc.enqueue_with_epoch(1, 12).expect("enqueue epoch 1");
    gate.wait_started(1);

    let report = svc.cancel_stale_epoch(2);
    assert_eq!(report.marked_in_flight, 1);

    // Backend finishes and returns Ok(60), which MUST be discarded as Cancelled.
    gate.release();
    assert_eq!(svc.wait(stale), Err(WaitError::Cancelled(stale)));
    assert_eq!(svc.status(stale), JobStatus::Cancelled);
    assert_eq!(svc.metrics().completed, 0);
    assert_eq!(svc.metrics().cancelled, 1);
}

#[test]
fn cancel_job_cancels_queued_and_in_flight_jobs_and_frees_queue_slot() {
    let gate = Gate::new();
    let g = gate.clone();
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(move |x: u64| {
            g.enter();
            Ok(x + 1)
        }),
        1,
        1,
    );

    let running = svc.enqueue(1).expect("running");
    gate.wait_started(1);
    let queued = svc.enqueue(2).expect("queued fills depth=1");
    assert_eq!(svc.enqueue(3), Err(EnqueueError::QueueFull { capacity: 1 }));

    // Cancelling the queued job frees the queue slot immediately.
    assert!(svc.cancel_job(queued));
    assert_eq!(svc.status(queued), JobStatus::Cancelled);
    let replacement = svc.enqueue(3).expect("freed slot accepts replacement");

    // Cancelling the running job suppresses its completion as Cancelled.
    assert!(svc.cancel_job(running));
    gate.release();

    assert_eq!(svc.wait(running), Err(WaitError::Cancelled(running)));
    assert_eq!(svc.wait(replacement), Ok(4));
    assert_eq!(svc.metrics().completed, 1);
    assert_eq!(svc.metrics().cancelled, 2);
}

#[test]
fn deployed_16bit_pow_grinder_exact_1t_2t_8t_16t_parity() {
    let transcript = sha256(b"obend-deployed-16bit-pow-parity");
    let win = default_grind_window(16, 1);
    assert_eq!(win, 16_384);

    let n1 = grind_pow_with(&transcript, 16, 1 << 24, win, 1).expect("1T 16-bit witness");
    assert!(verify_pow(&transcript, 16, n1));
    for lower in 0..n1 {
        assert!(!verify_pow(&transcript, 16, lower));
    }

    for &threads in &[2usize, 8, 16] {
        let nt = grind_pow_with(&transcript, 16, 1 << 24, win, threads).expect("NT 16-bit witness");
        assert_eq!(nt, n1, "16-bit PoW mismatch at threads={threads}");
    }
}
