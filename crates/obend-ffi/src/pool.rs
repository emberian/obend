use std::sync::mpsc::{channel, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread::{spawn, JoinHandle};

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

type Job = Box<dyn FnOnce() + Send + 'static>;

pub struct LeanWorkerPool {
    tx: SyncSender<Option<Job>>,
    workers: Vec<JoinHandle<()>>,
    _unconsumed_rx: Option<Arc<Mutex<Receiver<Option<Job>>>>>,
}

impl LeanWorkerPool {
    pub fn new(num_threads: usize) -> Self {
        let (tx, rx) = std::sync::mpsc::sync_channel::<Option<Job>>(64);
        let rx = Arc::new(Mutex::new(rx));
        let mut workers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let rx_clone = Arc::clone(&rx);
            workers.push(spawn(move || {
                ensure_lean_thread_initialized();

                while let Ok(Some(job)) = rx_clone.lock().unwrap().recv() {
                    job();
                }

                unsafe { crate::sys::lean_finalize_thread() };
            }));
        }

        let unconsumed_rx = if num_threads == 0 {
            Some(rx)
        } else {
            None
        };

        Self {
            tx,
            workers,
            _unconsumed_rx: unconsumed_rx,
        }
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

