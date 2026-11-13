use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::mpsc::{channel, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread::{spawn, JoinHandle};

use crate::error::ObendError;

thread_local! {
    static THREAD_ATTACHED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Attach the calling thread to the Lean runtime, initializing the runtime first if this process
/// has not yet (`obend_ensure_lean_thread` in `lean/c/obend_bridge.c` orders
/// `lean_initialize_runtime_module`, `lean_initialize`, the module initializer, then
/// `lean_initialize_thread`). Calling `lean_initialize_thread` first, as this function did until
/// 2026-11-04, is undefined behaviour and segfaulted hosts that opened no session before using
/// the pool.
pub fn ensure_lean_thread_initialized() {
    THREAD_ATTACHED.with(|attached| {
        if !attached.get() {
            unsafe {
                crate::sys::obend_ensure_lean_thread();
            }
            attached.set(true);
        }
    });
}

struct LeanThreadFinalizeGuard;

impl Drop for LeanThreadFinalizeGuard {
    fn drop(&mut self) {
        THREAD_ATTACHED.with(|attached| {
            if attached.get() {
                unsafe {
                    crate::sys::lean_finalize_thread();
                }
                attached.set(false);
            }
        });
    }
}

type Job = Box<dyn FnOnce() + Send + 'static>;

pub type LeanPool = LeanWorkerPool;

pub struct LeanWorkerPool {
    tx: SyncSender<Option<Job>>,
    workers: Vec<JoinHandle<()>>,
}

impl LeanWorkerPool {
    /// Fallible constructor rejecting `num_threads == 0`.
    pub fn try_new(num_threads: usize) -> Result<Self, ObendError> {
        if num_threads == 0 {
            return Err(ObendError::WithDetail(
                Box::new(ObendError::InitializationFailed),
                "LeanWorkerPool requires num_threads >= 1 (got 0)".to_string(),
            ));
        }

        let (tx, rx) = std::sync::mpsc::sync_channel::<Option<Job>>(64);
        let rx = Arc::new(Mutex::new(rx));
        let mut workers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let rx_clone = Arc::clone(&rx);
            workers.push(spawn(move || {
                ensure_lean_thread_initialized();
                let _finalize_guard = LeanThreadFinalizeGuard;

                loop {
                    let msg = {
                        let guard = rx_clone
                            .lock()
                            .unwrap_or_else(|poisoned| poisoned.into_inner());
                        guard.recv()
                    };
                    let Ok(Some(job)) = msg else { break };
                    let _ = catch_unwind(AssertUnwindSafe(job));
                }
            }));
        }

        Ok(Self { tx, workers })
    }

    /// Create a worker pool with `num_threads >= 1` attached Lean worker threads.
    ///
    /// # Panics
    /// Panics if `num_threads == 0`.
    pub fn new(num_threads: usize) -> Self {
        assert!(
            num_threads > 0,
            "LeanWorkerPool::new requires num_threads >= 1 (got 0)"
        );
        Self::try_new(num_threads).expect("num_threads > 0 checked")
    }

    pub fn execute<F, R>(&self, f: F) -> Receiver<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        let (resp_tx, resp_rx) = channel();
        let job = Box::new(move || {
            let result = f();
            let _ = resp_tx.send(result);
        });
        self.tx.send(Some(job)).expect("Worker pool active");
        resp_rx
    }
}

impl Drop for LeanWorkerPool {
    fn drop(&mut self) {
        for _ in 0..self.workers.len() {
            let _ = self.tx.send(None);
        }
        for worker in self.workers.drain(..) {
            let _ = worker.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn test_zero_workers_rejected_by_try_new() {
        assert!(LeanWorkerPool::try_new(0).is_err());
    }

    #[test]
    #[should_panic(expected = "num_threads >= 1")]
    fn test_zero_workers_panics_in_new() {
        let _ = LeanWorkerPool::new(0);
    }

    #[test]
    fn test_worker_panic_caught_and_pool_recovers_and_finalizes() {
        let pool = LeanWorkerPool::new(1);
        let panicking_rx = pool.execute(|| -> usize {
            panic!("simulated job panic inside LeanWorkerPool");
        });
        assert!(
            panicking_rx.recv().is_err(),
            "panicking job must drop response sender cleanly instead of hanging"
        );

        let counter = Arc::new(AtomicUsize::new(0));
        let c2 = Arc::clone(&counter);
        let ok_rx = pool.execute(move || {
            c2.fetch_add(1, Ordering::SeqCst);
            77usize
        });
        assert_eq!(ok_rx.recv().unwrap(), 77);
        assert_eq!(counter.load(Ordering::SeqCst), 1);
        drop(pool);
    }
}

