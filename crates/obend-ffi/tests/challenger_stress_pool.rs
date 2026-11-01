use obend_ffi::pool::{ensure_lean_thread_initialized, LeanWorkerPool};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

#[test]
fn test_challenger_pool_rapid_spawn_join_cycles() {
    // Stress test rapid creation and teardown of worker pools
    // to detect thread creation leaks or cleanup panics.
    for _ in 0..50 {
        let pool = LeanWorkerPool::new(4);
        let rx = pool.execute(|| 42);
        assert_eq!(rx.recv().unwrap(), 42);
        // pool is dropped immediately here
    }
}

#[test]
fn test_challenger_pool_concurrent_flood() {
    ensure_lean_thread_initialized();
    let pool = Arc::new(LeanWorkerPool::new(8));
    let counter = Arc::new(AtomicUsize::new(0));

    let mut handles = Vec::new();
    let num_threads = 10;
    let jobs_per_thread = 50;

    for _ in 0..num_threads {
        let pool_clone = Arc::clone(&pool);
        let counter_clone = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            let mut rxs = Vec::new();
            for _ in 0..jobs_per_thread {
                let c = Arc::clone(&counter_clone);
                let rx = pool_clone.execute(move || {
                    c.fetch_add(1, Ordering::Relaxed);
                });
                rxs.push(rx);
            }
            for rx in rxs {
                rx.recv().unwrap();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(counter.load(Ordering::SeqCst), num_threads * jobs_per_thread);
}

#[test]
fn test_challenger_pool_queue_saturation_stress() {
    // Channel capacity in pool.rs is hardcoded to 64.
    // Dispatching 200 items rapidly tests queue backpressure and synchronization.
    let pool = LeanWorkerPool::new(4);
    let mut receivers = Vec::new();

    for i in 0..200 {
        receivers.push(pool.execute(move || i * 2));
    }

    for (i, rx) in receivers.into_iter().enumerate() {
        assert_eq!(rx.recv().unwrap(), i * 2);
    }
}

#[test]
fn test_challenger_pool_thread_starvation_and_slow_jobs() {
    let pool = LeanWorkerPool::new(2);

    // Queue 2 slow jobs that occupy both threads
    let s1 = pool.execute(|| {
        thread::sleep(Duration::from_millis(50));
        "slow1"
    });
    let s2 = pool.execute(|| {
        thread::sleep(Duration::from_millis(50));
        "slow2"
    });

    // Queue quick jobs right after
    let q1 = pool.execute(|| "quick1");
    let q2 = pool.execute(|| "quick2");

    assert_eq!(s1.recv().unwrap(), "slow1");
    assert_eq!(s2.recv().unwrap(), "slow2");
    assert_eq!(q1.recv().unwrap(), "quick1");
    assert_eq!(q2.recv().unwrap(), "quick2");
}

#[test]
fn test_challenger_pool_drop_with_pending_work() {
    // Probe what happens when the pool is dropped while items might still be in the channel
    let pool = LeanWorkerPool::new(2);
    for _ in 0..20 {
        let _ = pool.execute(|| {
            thread::sleep(Duration::from_millis(5));
        });
    }
    // Drop pool immediately without waiting for receivers
    drop(pool);
}

#[test]
fn test_challenger_pool_reentrant_deadlock() {
    let pool = Arc::new(LeanWorkerPool::new(1));
    let pool_clone = Arc::clone(&pool);

    let rx = pool.execute(move || {
        // Nested dispatch on a 1-worker pool deadlocks the worker thread
        let inner_rx = pool_clone.execute(|| 99);
        inner_rx.recv_timeout(Duration::from_millis(100))
    });

    let res = rx.recv().unwrap();
    assert!(res.is_err(), "Nested dispatch on single-worker pool must deadlock");
}

#[test]
fn test_challenger_pool_zero_workers_hang() {
    let pool = LeanWorkerPool::new(0);
    let rx = pool.execute(|| 123);
    let res = rx.recv_timeout(Duration::from_millis(100));
    assert!(res.is_err(), "0-worker pool has no threads to consume jobs");
}

