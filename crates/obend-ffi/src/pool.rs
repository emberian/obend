use std::sync::mpsc::{channel, SyncSender};
use std::thread::{spawn, JoinHandle};

thread_local! {
    static THREAD_ATTACHED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub fn ensure_lean_thread_initialized() {
    THREAD_ATTACHED.with(|attached| {
        if !attached.get() {
            unsafe {
                crate::sys::lean_initialize_thread();
            }
            attached.set(true);
        }
    });
}

type Job = Box<dyn FnOnce() + Send + 'static>;

pub struct LeanWorkerPool {
    tx: SyncSender<Option<Job>>,
    workers: Vec<JoinHandle<()>>,
}

impl LeanWorkerPool {
    pub fn new(num_threads: usize) -> Self {
        let (tx, rx) = std::sync::mpsc::sync_channel::<Option<Job>>(64);
        let rx = std::sync::Arc::new(std::sync::Mutex::new(rx));
        let mut workers = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let rx_clone = std::sync::Arc::clone(&rx);
            workers.push(spawn(move || {
                unsafe { crate::sys::lean_initialize_thread() };

                while let Ok(Some(job)) = rx_clone.lock().unwrap().recv() {
                    job();
                }

                unsafe { crate::sys::lean_finalize_thread() };
            }));
        }

        Self { tx, workers }
    }

    pub fn execute<F, R>(&self, f: F) -> std::sync::mpsc::Receiver<R>
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
