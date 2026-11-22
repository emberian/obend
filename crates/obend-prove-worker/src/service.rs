//! Off-lock bounded-backpressure async proving service (`ProveService<I, O>`).
//!
//! Hardens the `dreggnet-prove-service` / `node/src/prove_pool.rs` worker-pool pattern:
//! - Strictly off-lock backend execution (no mutex held while proving).
//! - Hard bounded queue admission (`EnqueueError::QueueFull` backpressure, never blocks caller).
//! - Hard bounded `Done` / `Failed` / `Cancelled` tombstone retention via deterministic LRU + TTL
//!   eviction (closing the unbounded `HashMap` memory leak of `dreggnet-prove-service`).
//! - Monotonic epoch invalidation (`cancel_stale_epoch`) with immediate queue eviction, cooperative
//!   in-flight `CancelToken`, stale-result suppression, and stale-admission rejection.
//! - Idempotent job-ID (`enqueue_with_id`) and 256-bit digest (`enqueue_dedup`) deduplication.
//! - Zero `dreggnet-game-board` / `prove_tug_match` (`B2`) mannequin dependencies.

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// Default worker thread count.
pub const DEFAULT_WORKERS: usize = 2;

/// Default bounded pending-queue depth.
pub const DEFAULT_QUEUE_DEPTH: usize = 64;

/// Default maximum number of retained settled (`Done` / `Failed` / `Cancelled`) tombstones.
pub const DEFAULT_MAX_RETAINED_SETTLED: usize = 1024;

/// Handle to a proving job inside [`ProveService`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JobId(pub u64);

impl fmt::Display for JobId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Lifecycle state of a proving job.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JobStatus<O> {
    /// Accepted into the bounded queue; waiting for a free worker.
    Queued,
    /// Currently executing inside a worker thread, off-lock.
    Proving,
    /// Completed successfully with proof output `O`.
    Done(Box<O>),
    /// Backend returned an error or panicked.
    Failed(String),
    /// Invalidated by [`ProveService::cancel_stale_epoch`], [`ProveService::cancel_job`], or
    /// service shutdown before its output could be published.
    Cancelled,
    /// Never submitted, or already pruned from the bounded settled cache by LRU/TTL eviction.
    Unknown,
}

impl<O> JobStatus<O> {
    /// Returns a reference to the completed output if [`JobStatus::Done`].
    pub fn done(&self) -> Option<&O> {
        match self {
            JobStatus::Done(out) => Some(out),
            _ => None,
        }
    }

    /// Returns `true` iff the job has reached a terminal state (`Done`, `Failed`, or `Cancelled`).
    pub fn is_settled(&self) -> bool {
        matches!(
            self,
            JobStatus::Done(_) | JobStatus::Failed(_) | JobStatus::Cancelled
        )
    }

    /// Returns `true` iff the job was cancelled.
    pub fn is_cancelled(&self) -> bool {
        matches!(self, JobStatus::Cancelled)
    }
}

/// Error returned when [`ProveService`] refuses to admit a job.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnqueueError {
    /// Bounded pending queue is full; caller should shed load or retry later.
    QueueFull { capacity: usize },
    /// Job's epoch is strictly older than the service's current `min_active_epoch`.
    StaleEpoch {
        job_epoch: u64,
        min_active_epoch: u64,
    },
    /// Service is shutting down and no longer accepts jobs.
    Shutdown,
}

impl fmt::Display for EnqueueError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnqueueError::QueueFull { capacity } => {
                write!(f, "prove queue full (capacity={capacity})")
            }
            EnqueueError::StaleEpoch {
                job_epoch,
                min_active_epoch,
            } => write!(
                f,
                "stale epoch {job_epoch} < min_active_epoch {min_active_epoch}"
            ),
            EnqueueError::Shutdown => write!(f, "prove service shutting down"),
        }
    }
}

impl std::error::Error for EnqueueError {}

/// Outcome of an idempotent enqueue call (`enqueue_with_id` or `enqueue_dedup`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnqueueOutcome {
    /// The job handle (either freshly created or the existing deduplicated handle).
    pub id: JobId,
    /// `true` if an existing live (`Queued` / `Proving`) or `Done` job was returned without
    /// consuming queue capacity or re-running the backend.
    pub deduplicated: bool,
}

/// Error returned by [`ProveService::wait`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WaitError {
    /// Prover backend returned an error or panicked.
    Failed(String),
    /// Job was cancelled (stale epoch, explicit cancel, or service drop).
    Cancelled(JobId),
    /// Job was never enqueued or its settled tombstone was already evicted.
    Unknown(JobId),
}

impl fmt::Display for WaitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WaitError::Failed(msg) => write!(f, "prove job failed: {msg}"),
            WaitError::Cancelled(id) => write!(f, "prove job {id} cancelled"),
            WaitError::Unknown(id) => write!(f, "unknown prove job {id}"),
        }
    }
}

impl std::error::Error for WaitError {}

/// Summary returned by [`ProveService::cancel_stale_epoch`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CancelReport {
    /// Active epoch floor after the call.
    pub min_active_epoch: u64,
    /// Stale `Queued` jobs immediately removed from the pending queue and settled `Cancelled`.
    pub cancelled_queued: usize,
    /// Stale in-flight (`Proving`) jobs flagged for cancellation (their `CancelToken` is set and
    /// their result will be discarded as `Cancelled` on completion).
    pub marked_in_flight: usize,
}

/// Cooperative cancellation handle passed to [`CancellableBackend`] invocations.
#[derive(Clone, Debug, Default)]
pub struct CancelToken {
    flag: Arc<AtomicBool>,
}

impl CancelToken {
    /// Creates a fresh non-cancelled token.
    pub fn new() -> Self {
        Self {
            flag: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Marks this token as cancelled.
    pub fn cancel(&self) {
        self.flag.store(true, Ordering::Release);
    }

    /// Returns `true` once cancellation has been requested.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        self.flag.load(Ordering::Acquire)
    }
}

/// Plain proving backend: one job input -> proof output or error string.
pub type Backend<I, O> = Arc<dyn Fn(I) -> Result<O, String> + Send + Sync>;

/// Cooperatively cancellable proving backend: receives a [`CancelToken`] flipped immediately on
/// stale-epoch invalidation or explicit cancellation.
pub type CancellableBackend<I, O> = Arc<dyn Fn(I, &CancelToken) -> Result<O, String> + Send + Sync>;

/// Explicit configuration for [`ProveService`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProveServiceConfig {
    /// Number of OS worker threads (clamped to `>= 1`).
    pub workers: usize,
    /// Maximum number of queued (pending) jobs waiting for a worker (clamped to `>= 1`).
    pub queue_depth: usize,
    /// Hard upper bound on retained terminal (`Done` / `Failed` / `Cancelled`) tombstones.
    pub max_retained_settled: usize,
    /// Optional wall-clock TTL after which settled tombstones are pruned even if under capacity.
    pub settled_ttl: Option<Duration>,
}

impl Default for ProveServiceConfig {
    fn default() -> Self {
        Self {
            workers: DEFAULT_WORKERS,
            queue_depth: DEFAULT_QUEUE_DEPTH,
            max_retained_settled: DEFAULT_MAX_RETAINED_SETTLED,
            settled_ttl: None,
        }
    }
}

impl ProveServiceConfig {
    /// Constructs a config from `OBEND_PROVE_*` environment variables, falling back to defaults.
    pub fn from_env() -> Self {
        let workers = env_usize("OBEND_PROVE_WORKERS", DEFAULT_WORKERS).max(1);
        let queue_depth = env_usize("OBEND_PROVE_QUEUE_DEPTH", DEFAULT_QUEUE_DEPTH).max(1);
        let max_retained_settled =
            env_usize_allow_zero("OBEND_PROVE_MAX_RETAINED", DEFAULT_MAX_RETAINED_SETTLED);
        let settled_ttl = std::env::var("OBEND_PROVE_SETTLED_TTL_SECS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|&s| s > 0)
            .map(Duration::from_secs);
        Self {
            workers,
            queue_depth,
            max_retained_settled,
            settled_ttl,
        }
    }

    fn normalized(self) -> Self {
        Self {
            workers: self.workers.max(1),
            queue_depth: self.queue_depth.max(1),
            max_retained_settled: self.max_retained_settled,
            settled_ttl: self.settled_ttl,
        }
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(default)
}

fn env_usize_allow_zero(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(default)
}

/// Snapshot of [`ProveService`] lifetime counters and current occupancy gauges.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Metrics {
    /// New jobs accepted into the pending queue.
    pub enqueued: u64,
    /// Idempotent submissions resolved to an existing `Queued`, `Proving`, or `Done` job.
    pub deduplicated: u64,
    /// Submissions refused because the bounded queue was full (`EnqueueError::QueueFull`).
    pub dropped: u64,
    /// Submissions refused because `epoch < min_active_epoch`.
    pub rejected_stale_epoch: u64,
    /// Jobs that settled `Done`.
    pub completed: u64,
    /// Jobs that settled `Failed`.
    pub failed: u64,
    /// Jobs that settled `Cancelled` (queued eviction or in-flight invalidation).
    pub cancelled: u64,
    /// Total settled tombstones evicted (capacity LRU + TTL).
    pub evicted: u64,
    /// Settled tombstones evicted by deterministic LRU capacity cap.
    pub evicted_capacity: u64,
    /// Settled tombstones evicted by TTL expiry.
    pub evicted_ttl: u64,
    /// Current jobs executing in workers (gauge).
    pub in_flight: u64,
    /// Current jobs waiting in the bounded queue (gauge).
    pub queued: u64,
    /// Current retained settled tombstones (gauge; always `<= max_retained_settled`).
    pub retained_settled: u64,
    /// Cumulative wall time spent executing the backend across settled jobs.
    pub total_prove_secs: f64,
}

#[derive(Default)]
struct Counters {
    enqueued: AtomicU64,
    deduplicated: AtomicU64,
    dropped: AtomicU64,
    rejected_stale_epoch: AtomicU64,
    completed: AtomicU64,
    failed: AtomicU64,
    cancelled: AtomicU64,
    evicted_capacity: AtomicU64,
    evicted_ttl: AtomicU64,
    in_flight: AtomicU64,
    prove_nanos: AtomicU64,
}

/// Per-waiter rendezvous slot so a caller already blocked in `wait(id)` receives its outcome
/// reliably even if `max_retained_settled == 0` or heavy throughput evicts the tombstone
/// immediately after settlement.
struct WaiterSlot<O> {
    outcome: Mutex<Option<Result<O, WaitError>>>,
    cv: Condvar,
}

impl<O> WaiterSlot<O> {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            outcome: Mutex::new(None),
            cv: Condvar::new(),
        })
    }

    fn deliver(&self, result: Result<O, WaitError>) {
        let mut guard = self.outcome.lock().expect("waiter slot mutex");
        *guard = Some(result);
        self.cv.notify_all();
    }

    fn wait(&self) -> Result<O, WaitError> {
        let mut guard = self.outcome.lock().expect("waiter slot mutex");
        loop {
            if let Some(res) = guard.take() {
                return res;
            }
            guard = self.cv.wait(guard).expect("waiter slot condvar");
        }
    }
}

struct QueuedJob<I> {
    id: JobId,
    epoch: u64,
    input: I,
}

#[derive(Clone, Copy, Debug)]
struct SettledMeta {
    lru_tick: u64,
    settled_at: Instant,
    settle_seq: u64,
}

struct JobEntry<O> {
    epoch: u64,
    status: JobStatus<O>,
    dedup_key: Option<[u8; 32]>,
    cancel_token: Option<CancelToken>,
    cancel_requested: bool,
    waiters: Vec<Arc<WaiterSlot<O>>>,
    settled_meta: Option<SettledMeta>,
}

struct ServiceState<I, O> {
    config: ProveServiceConfig,
    shutdown: bool,
    min_active_epoch: u64,
    next_id: u64,
    access_tick: u64,
    settle_seq: u64,
    queue: VecDeque<QueuedJob<I>>,
    jobs: HashMap<JobId, JobEntry<O>>,
    dedup_index: HashMap<[u8; 32], JobId>,
    /// Deterministic LRU index: strictly monotonic `access_tick -> JobId` for retained settled jobs.
    lru_order: BTreeMap<u64, JobId>,
    /// TTL index: `(settled_at, settle_seq) -> JobId` for retained settled jobs.
    ttl_order: BTreeMap<(Instant, u64), JobId>,
}

impl<I, O> ServiceState<I, O>
where
    O: Clone,
{
    fn new(config: ProveServiceConfig) -> Self {
        Self {
            config,
            shutdown: false,
            min_active_epoch: 0,
            next_id: 1,
            access_tick: 0,
            settle_seq: 0,
            queue: VecDeque::with_capacity(config.queue_depth),
            jobs: HashMap::new(),
            dedup_index: HashMap::new(),
            lru_order: BTreeMap::new(),
            ttl_order: BTreeMap::new(),
        }
    }

    fn alloc_job_id(&mut self) -> JobId {
        loop {
            let candidate = self.next_id;
            self.next_id = self.next_id.wrapping_add(1);
            if candidate == 0 {
                continue;
            }
            let id = JobId(candidate);
            if !self.jobs.contains_key(&id) {
                return id;
            }
        }
    }

    fn next_tick(&mut self) -> u64 {
        self.access_tick = self.access_tick.wrapping_add(1);
        self.access_tick
    }

    fn next_settle_seq(&mut self) -> u64 {
        self.settle_seq = self.settle_seq.wrapping_add(1);
        self.settle_seq
    }

    /// Touches a retained settled job in the deterministic LRU index.
    fn touch_settled(&mut self, id: JobId) {
        let new_tick = self.next_tick();
        if let Some(entry) = self.jobs.get_mut(&id) {
            if let Some(meta) = entry.settled_meta.as_mut() {
                self.lru_order.remove(&meta.lru_tick);
                meta.lru_tick = new_tick;
                self.lru_order.insert(new_tick, id);
            }
        }
    }

    /// Removes a settled job from all maps and indexes.
    fn remove_settled_entry(&mut self, id: JobId) -> bool {
        let Some(entry) = self.jobs.remove(&id) else {
            return false;
        };
        if let Some(meta) = entry.settled_meta {
            self.lru_order.remove(&meta.lru_tick);
            self.ttl_order.remove(&(meta.settled_at, meta.settle_seq));
        }
        if let Some(key) = entry.dedup_key {
            if self.dedup_index.get(&key) == Some(&id) {
                self.dedup_index.remove(&key);
            }
        }
        true
    }

    /// Evicts all settled tombstones older than `config.settled_ttl`.
    fn prune_expired(&mut self, now: Instant, counters: &Counters) -> usize {
        let Some(ttl) = self.config.settled_ttl else {
            return 0;
        };
        let mut removed = 0usize;
        loop {
            let Some((&(settled_at, seq), &id)) = self.ttl_order.first_key_value() else {
                break;
            };
            if now.saturating_duration_since(settled_at) < ttl {
                break;
            }
            self.ttl_order.remove(&(settled_at, seq));
            if let Some(entry) = self.jobs.remove(&id) {
                if let Some(meta) = entry.settled_meta {
                    self.lru_order.remove(&meta.lru_tick);
                }
                if let Some(key) = entry.dedup_key {
                    if self.dedup_index.get(&key) == Some(&id) {
                        self.dedup_index.remove(&key);
                    }
                }
                counters.evicted_ttl.fetch_add(1, Ordering::Relaxed);
                removed += 1;
            }
        }
        removed
    }

    /// Enforces `lru_order.len() <= config.max_retained_settled` by evicting the least-recently
    /// accessed settled entries in deterministic `access_tick` order.
    fn enforce_capacity(&mut self, counters: &Counters) -> usize {
        let cap = self.config.max_retained_settled;
        let mut evicted = 0usize;
        while self.lru_order.len() > cap {
            let Some((_, id)) = self.lru_order.pop_first() else {
                break;
            };
            if let Some(entry) = self.jobs.remove(&id) {
                if let Some(meta) = entry.settled_meta {
                    self.ttl_order.remove(&(meta.settled_at, meta.settle_seq));
                }
                if let Some(key) = entry.dedup_key {
                    if self.dedup_index.get(&key) == Some(&id) {
                        self.dedup_index.remove(&key);
                    }
                }
                counters.evicted_capacity.fetch_add(1, Ordering::Relaxed);
                evicted += 1;
            }
        }
        evicted
    }

    /// Transitions an active entry (`Queued` or `Proving`) into a terminal settled state, notifies
    /// all direct waiters, updates dedup index (clearing key on `Failed`/`Cancelled`), and runs
    /// bounded TTL + LRU eviction.
    fn settle_job(&mut self, id: JobId, terminal: JobStatus<O>, now: Instant, counters: &Counters) {
        let wait_result = match &terminal {
            JobStatus::Done(out) => Ok((**out).clone()),
            JobStatus::Failed(msg) => Err(WaitError::Failed(msg.clone())),
            JobStatus::Cancelled => Err(WaitError::Cancelled(id)),
            JobStatus::Queued | JobStatus::Proving | JobStatus::Unknown => {
                unreachable!("settle_job called with non-terminal status")
            }
        };

        let clear_dedup = !matches!(terminal, JobStatus::Done(_));
        let waiters = if let Some(entry) = self.jobs.get_mut(&id) {
            entry.cancel_token = None;
            entry.cancel_requested = false;
            entry.status = terminal;
            if clear_dedup {
                if let Some(key) = entry.dedup_key.take() {
                    if self.dedup_index.get(&key) == Some(&id) {
                        self.dedup_index.remove(&key);
                    }
                }
            }
            std::mem::take(&mut entry.waiters)
        } else {
            Vec::new()
        };

        // Deliver directly to every thread already blocked in `wait(id)` before eviction runs.
        for waiter in waiters {
            waiter.deliver(wait_result.clone());
        }

        self.prune_expired(now, counters);

        if self.config.max_retained_settled == 0 {
            if self.remove_settled_entry(id) {
                counters.evicted_capacity.fetch_add(1, Ordering::Relaxed);
            }
            return;
        }

        let tick = self.next_tick();
        let seq = self.next_settle_seq();
        if let Some(entry) = self.jobs.get_mut(&id) {
            entry.settled_meta = Some(SettledMeta {
                lru_tick: tick,
                settled_at: now,
                settle_seq: seq,
            });
            self.lru_order.insert(tick, id);
            self.ttl_order.insert((now, seq), id);
        }

        self.enforce_capacity(counters);
    }
}

/// Off-lock bounded-backpressure async proving service.
///
/// Proving runs exclusively on dedicated background worker threads without holding any lock.
/// Callers submit jobs via [`enqueue`](Self::enqueue), [`enqueue_with_epoch`](Self::enqueue_with_epoch),
/// [`enqueue_with_id`](Self::enqueue_with_id), or [`enqueue_dedup`](Self::enqueue_dedup); poll
/// [`status`](Self::status) or block on [`wait`](Self::wait); and invalidate stale epochs via
/// [`cancel_stale_epoch`](Self::cancel_stale_epoch).
pub struct ProveService<I, O>
where
    I: Send + 'static,
    O: Clone + Send + 'static,
{
    inner: Arc<(Mutex<ServiceState<I, O>>, Condvar)>,
    counters: Arc<Counters>,
    workers: Vec<JoinHandle<()>>,
    config: ProveServiceConfig,
}

impl<I, O> ProveService<I, O>
where
    I: Send + 'static,
    O: Clone + Send + 'static,
{
    /// Spawns a proving service configured from `OBEND_PROVE_*` env vars (or defaults).
    pub fn spawn(backend: Backend<I, O>) -> Self {
        Self::spawn_with_config(backend, ProveServiceConfig::from_env())
    }

    /// Spawns a proving service with explicit worker count and queue depth (default settled cap).
    pub fn spawn_with(backend: Backend<I, O>, n_workers: usize, queue_depth: usize) -> Self {
        Self::spawn_with_config(
            backend,
            ProveServiceConfig {
                workers: n_workers,
                queue_depth,
                ..ProveServiceConfig::default()
            },
        )
    }

    /// Spawns a proving service with full explicit [`ProveServiceConfig`].
    pub fn spawn_with_config(backend: Backend<I, O>, config: ProveServiceConfig) -> Self {
        let wrapped: CancellableBackend<I, O> = Arc::new(move |input, _cancel| backend(input));
        Self::spawn_cancellable(wrapped, config)
    }

    /// Spawns a proving service whose backend cooperatively observes [`CancelToken`].
    pub fn spawn_cancellable(
        backend: CancellableBackend<I, O>,
        config: ProveServiceConfig,
    ) -> Self {
        let config = config.normalized();
        let inner = Arc::new((Mutex::new(ServiceState::new(config)), Condvar::new()));
        let counters = Arc::new(Counters::default());

        let mut workers = Vec::with_capacity(config.workers);
        for wid in 0..config.workers {
            let inner = inner.clone();
            let counters = counters.clone();
            let backend = backend.clone();
            let handle = std::thread::Builder::new()
                .name(format!("obend-prover-{wid}"))
                .spawn(move || worker_loop(inner, counters, backend))
                .expect("spawn obend-prover worker thread");
            workers.push(handle);
        }

        Self {
            inner,
            counters,
            workers,
            config,
        }
    }

    /// Enqueues a job at the service's current `min_active_epoch` with a fresh auto-assigned
    /// [`JobId`]. Never blocks on proving; fails fast with [`EnqueueError::QueueFull`] on
    /// saturation.
    pub fn enqueue(&self, input: I) -> Result<JobId, EnqueueError> {
        let (mutex, cv) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        if state.shutdown {
            return Err(EnqueueError::Shutdown);
        }
        if state.queue.len() >= state.config.queue_depth {
            self.counters.dropped.fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::QueueFull {
                capacity: state.config.queue_depth,
            });
        }

        let epoch = state.min_active_epoch;
        let id = state.alloc_job_id();
        state.jobs.insert(
            id,
            JobEntry {
                epoch,
                status: JobStatus::Queued,
                dedup_key: None,
                cancel_token: None,
                cancel_requested: false,
                waiters: Vec::new(),
                settled_meta: None,
            },
        );
        state.queue.push_back(QueuedJob { id, epoch, input });
        self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
        cv.notify_one();
        Ok(id)
    }

    /// Enqueues a job tagged with an explicit `epoch`. Rejects `epoch < min_active_epoch` with
    /// [`EnqueueError::StaleEpoch`].
    pub fn enqueue_with_epoch(&self, epoch: u64, input: I) -> Result<JobId, EnqueueError> {
        let (mutex, cv) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        if state.shutdown {
            return Err(EnqueueError::Shutdown);
        }
        if epoch < state.min_active_epoch {
            self.counters
                .rejected_stale_epoch
                .fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::StaleEpoch {
                job_epoch: epoch,
                min_active_epoch: state.min_active_epoch,
            });
        }
        if state.queue.len() >= state.config.queue_depth {
            self.counters.dropped.fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::QueueFull {
                capacity: state.config.queue_depth,
            });
        }

        let id = state.alloc_job_id();
        state.jobs.insert(
            id,
            JobEntry {
                epoch,
                status: JobStatus::Queued,
                dedup_key: None,
                cancel_token: None,
                cancel_requested: false,
                waiters: Vec::new(),
                settled_meta: None,
            },
        );
        state.queue.push_back(QueuedJob { id, epoch, input });
        self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
        cv.notify_one();
        Ok(id)
    }

    /// Idempotently submits a job under a caller-chosen [`JobId`].
    ///
    /// - If `id` is already tracked as `Queued`, `Proving`, or `Done`, returns
    ///   `Ok(EnqueueOutcome { id, deduplicated: true })` without consuming queue capacity or
    ///   re-running the backend.
    /// - If `id` previously settled `Failed` or `Cancelled`, admits a fresh attempt (subject to
    ///   epoch and bounded queue capacity).
    pub fn enqueue_with_id(
        &self,
        id: JobId,
        epoch: u64,
        input: I,
    ) -> Result<EnqueueOutcome, EnqueueError> {
        let (mutex, cv) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        if state.shutdown {
            return Err(EnqueueError::Shutdown);
        }
        if epoch < state.min_active_epoch {
            self.counters
                .rejected_stale_epoch
                .fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::StaleEpoch {
                job_epoch: epoch,
                min_active_epoch: state.min_active_epoch,
            });
        }

        if let Some(existing) = state.jobs.get(&id) {
            match existing.status {
                JobStatus::Queued | JobStatus::Proving => {
                    self.counters.deduplicated.fetch_add(1, Ordering::Relaxed);
                    return Ok(EnqueueOutcome {
                        id,
                        deduplicated: true,
                    });
                }
                JobStatus::Done(_) => {
                    state.touch_settled(id);
                    self.counters.deduplicated.fetch_add(1, Ordering::Relaxed);
                    return Ok(EnqueueOutcome {
                        id,
                        deduplicated: true,
                    });
                }
                JobStatus::Failed(_) | JobStatus::Cancelled | JobStatus::Unknown => {}
            }
        }

        if state.queue.len() >= state.config.queue_depth {
            self.counters.dropped.fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::QueueFull {
                capacity: state.config.queue_depth,
            });
        }

        // Replace any prior Failed/Cancelled tombstone cleanly before inserting fresh entry.
        state.remove_settled_entry(id);
        if id.0 >= state.next_id {
            state.next_id = id.0.saturating_add(1);
        }

        state.jobs.insert(
            id,
            JobEntry {
                epoch,
                status: JobStatus::Queued,
                dedup_key: None,
                cancel_token: None,
                cancel_requested: false,
                waiters: Vec::new(),
                settled_meta: None,
            },
        );
        state.queue.push_back(QueuedJob { id, epoch, input });
        self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
        cv.notify_one();
        Ok(EnqueueOutcome {
            id,
            deduplicated: false,
        })
    }

    /// Idempotently submits a job keyed by a 256-bit content digest (`[u8; 32]`).
    ///
    /// - If `key` currently maps to a `Queued`, `Proving`, or `Done` job, returns that existing
    ///   [`JobId`] with `deduplicated = true` without consuming queue capacity or re-running the
    ///   backend.
    /// - Otherwise allocates a new [`JobId`] (subject to epoch and bounded queue capacity).
    pub fn enqueue_dedup(
        &self,
        key: [u8; 32],
        epoch: u64,
        input: I,
    ) -> Result<EnqueueOutcome, EnqueueError> {
        let (mutex, cv) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        if state.shutdown {
            return Err(EnqueueError::Shutdown);
        }
        if epoch < state.min_active_epoch {
            self.counters
                .rejected_stale_epoch
                .fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::StaleEpoch {
                job_epoch: epoch,
                min_active_epoch: state.min_active_epoch,
            });
        }

        if let Some(&existing_id) = state.dedup_index.get(&key) {
            let live_or_done = state.jobs.get(&existing_id).map(|e| match e.status {
                JobStatus::Queued | JobStatus::Proving => Some(false),
                JobStatus::Done(_) => Some(true),
                JobStatus::Failed(_) | JobStatus::Cancelled | JobStatus::Unknown => None,
            });
            if let Some(Some(is_done)) = live_or_done {
                if is_done {
                    state.touch_settled(existing_id);
                }
                self.counters.deduplicated.fetch_add(1, Ordering::Relaxed);
                return Ok(EnqueueOutcome {
                    id: existing_id,
                    deduplicated: true,
                });
            }
            state.dedup_index.remove(&key);
        }

        if state.queue.len() >= state.config.queue_depth {
            self.counters.dropped.fetch_add(1, Ordering::Relaxed);
            return Err(EnqueueError::QueueFull {
                capacity: state.config.queue_depth,
            });
        }

        let id = state.alloc_job_id();
        state.dedup_index.insert(key, id);
        state.jobs.insert(
            id,
            JobEntry {
                epoch,
                status: JobStatus::Queued,
                dedup_key: Some(key),
                cancel_token: None,
                cancel_requested: false,
                waiters: Vec::new(),
                settled_meta: None,
            },
        );
        state.queue.push_back(QueuedJob { id, epoch, input });
        self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
        cv.notify_one();
        Ok(EnqueueOutcome {
            id,
            deduplicated: false,
        })
    }

    /// Polls the current [`JobStatus`] for `id`.
    ///
    /// Runs cheap TTL pruning first and refreshes LRU recency if `id` is a retained settled entry.
    pub fn status(&self, id: JobId) -> JobStatus<O> {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        let is_settled = state
            .jobs
            .get(&id)
            .is_some_and(|entry| entry.settled_meta.is_some());
        if is_settled {
            state.touch_settled(id);
        }

        state
            .jobs
            .get(&id)
            .map(|entry| entry.status.clone())
            .unwrap_or(JobStatus::Unknown)
    }

    /// Blocks until `id` reaches a terminal state (`Done`, `Failed`, or `Cancelled`).
    ///
    /// If `id` is currently `Queued` or `Proving`, registers a direct waiter slot so the caller
    /// receives the outcome even if the settled tombstone is immediately evicted.
    pub fn wait(&self, id: JobId) -> Result<O, WaitError> {
        let slot = {
            let (mutex, _) = &*self.inner;
            let mut state = mutex.lock().expect("prove service state mutex");
            let now = Instant::now();
            state.prune_expired(now, &self.counters);

            if let Some(entry) = state.jobs.get(&id) {
                match &entry.status {
                    JobStatus::Done(out) => {
                        let out = (**out).clone();
                        state.touch_settled(id);
                        return Ok(out);
                    }
                    JobStatus::Failed(err) => {
                        let err = err.clone();
                        state.touch_settled(id);
                        return Err(WaitError::Failed(err));
                    }
                    JobStatus::Cancelled => {
                        state.touch_settled(id);
                        return Err(WaitError::Cancelled(id));
                    }
                    JobStatus::Unknown => return Err(WaitError::Unknown(id)),
                    JobStatus::Queued | JobStatus::Proving => {
                        let slot = WaiterSlot::new();
                        state
                            .jobs
                            .get_mut(&id)
                            .expect("entry just checked")
                            .waiters
                            .push(slot.clone());
                        slot
                    }
                }
            } else {
                return Err(WaitError::Unknown(id));
            }
        };

        slot.wait()
    }

    /// Advances the monotonic active-epoch floor to `min_active_epoch` and invalidates all pending
    /// and in-flight jobs whose `epoch < min_active_epoch`.
    ///
    /// - Stale `Queued` jobs are removed from the queue immediately (freeing queue slots for fresh
    ///   epoch admissions) and settled as [`JobStatus::Cancelled`].
    /// - Stale in-flight (`Proving`) jobs have their [`CancelToken`] flipped immediately and will
    ///   have their output discarded as [`JobStatus::Cancelled`] when the worker returns.
    /// - Subsequent submissions with `epoch < min_active_epoch` are rejected with
    ///   [`EnqueueError::StaleEpoch`].
    pub fn cancel_stale_epoch(&self, min_active_epoch: u64) -> CancelReport {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        if min_active_epoch <= state.min_active_epoch {
            return CancelReport {
                min_active_epoch: state.min_active_epoch,
                cancelled_queued: 0,
                marked_in_flight: 0,
            };
        }
        state.min_active_epoch = min_active_epoch;

        // 1. Evict all stale queued jobs from the pending queue immediately.
        let mut stale_queued_ids = Vec::new();
        let mut kept_queue = VecDeque::with_capacity(state.queue.len());
        while let Some(job) = state.queue.pop_front() {
            if job.epoch < min_active_epoch {
                stale_queued_ids.push(job.id);
            } else {
                kept_queue.push_back(job);
            }
        }
        state.queue = kept_queue;

        let cancelled_queued = stale_queued_ids.len();
        for id in stale_queued_ids {
            self.counters.cancelled.fetch_add(1, Ordering::Relaxed);
            state.settle_job(id, JobStatus::Cancelled, now, &self.counters);
        }

        // 2. Flag all stale in-flight jobs and trigger their cooperative CancelToken.
        let mut marked_in_flight = 0usize;
        for entry in state.jobs.values_mut() {
            if matches!(entry.status, JobStatus::Proving)
                && entry.epoch < min_active_epoch
                && !entry.cancel_requested
            {
                entry.cancel_requested = true;
                if let Some(token) = &entry.cancel_token {
                    token.cancel();
                }
                marked_in_flight += 1;
            }
        }

        CancelReport {
            min_active_epoch,
            cancelled_queued,
            marked_in_flight,
        }
    }

    /// Cancels a single job by [`JobId`]. Returns `true` if the job was `Queued` (evicted
    /// immediately) or `Proving` (flagged + `CancelToken` flipped).
    pub fn cancel_job(&self, id: JobId) -> bool {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        state.prune_expired(now, &self.counters);

        let status_kind = match state.jobs.get(&id).map(|e| &e.status) {
            Some(JobStatus::Queued) => 1u8,
            Some(JobStatus::Proving) => 2u8,
            _ => return false,
        };

        if status_kind == 1 {
            if let Some(pos) = state.queue.iter().position(|j| j.id == id) {
                state.queue.remove(pos);
            }
            self.counters.cancelled.fetch_add(1, Ordering::Relaxed);
            state.settle_job(id, JobStatus::Cancelled, now, &self.counters);
            return true;
        }

        if let Some(entry) = state.jobs.get_mut(&id) {
            entry.cancel_requested = true;
            if let Some(token) = &entry.cancel_token {
                token.cancel();
            }
            return true;
        }
        false
    }

    /// Explicitly sweeps and evicts all settled entries whose age `>= settled_ttl`.
    pub fn prune_expired(&self) -> usize {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        state.prune_expired(Instant::now(), &self.counters)
    }

    /// Returns a snapshot of lifetime counters and live occupancy gauges.
    pub fn metrics(&self) -> Metrics {
        let (mutex, _) = &*self.inner;
        let (queued, retained_settled) = {
            let state = mutex.lock().expect("prove service state mutex");
            (state.queue.len() as u64, state.lru_order.len() as u64)
        };
        let evicted_capacity = self.counters.evicted_capacity.load(Ordering::Relaxed);
        let evicted_ttl = self.counters.evicted_ttl.load(Ordering::Relaxed);
        Metrics {
            enqueued: self.counters.enqueued.load(Ordering::Relaxed),
            deduplicated: self.counters.deduplicated.load(Ordering::Relaxed),
            dropped: self.counters.dropped.load(Ordering::Relaxed),
            rejected_stale_epoch: self.counters.rejected_stale_epoch.load(Ordering::Relaxed),
            completed: self.counters.completed.load(Ordering::Relaxed),
            failed: self.counters.failed.load(Ordering::Relaxed),
            cancelled: self.counters.cancelled.load(Ordering::Relaxed),
            evicted: evicted_capacity.saturating_add(evicted_ttl),
            evicted_capacity,
            evicted_ttl,
            in_flight: self.counters.in_flight.load(Ordering::Relaxed),
            queued,
            retained_settled,
            total_prove_secs: self.counters.prove_nanos.load(Ordering::Relaxed) as f64 / 1e9,
        }
    }

    /// Current monotonic minimum active epoch floor.
    pub fn min_active_epoch(&self) -> u64 {
        let (mutex, _) = &*self.inner;
        mutex.lock().expect("prove service state mutex").min_active_epoch
    }

    /// Number of retained settled tombstones (always `<= max_retained_settled`).
    pub fn retained_settled(&self) -> usize {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        state.prune_expired(Instant::now(), &self.counters);
        state.lru_order.len()
    }

    /// Total number of entries currently in the internal job map (active + retained settled).
    pub fn tracked_jobs(&self) -> usize {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        state.prune_expired(Instant::now(), &self.counters);
        state.jobs.len()
    }

    /// Total number of live entries in the deduplication digest index.
    pub fn dedup_entries(&self) -> usize {
        let (mutex, _) = &*self.inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        state.prune_expired(Instant::now(), &self.counters);
        state.dedup_index.len()
    }

    /// Number of background worker threads.
    pub fn workers(&self) -> usize {
        self.config.workers
    }

    /// Configured bounded pending-queue depth.
    pub fn queue_depth(&self) -> usize {
        self.config.queue_depth
    }

    /// Configured maximum retained settled tombstones.
    pub fn max_retained_settled(&self) -> usize {
        self.config.max_retained_settled
    }
}

impl<I, O> Drop for ProveService<I, O>
where
    I: Send + 'static,
    O: Clone + Send + 'static,
{
    fn drop(&mut self) {
        {
            let (mutex, cv) = &*self.inner;
            let mut state = mutex.lock().expect("prove service state mutex");
            state.shutdown = true;
            let now = Instant::now();

            let pending_ids: Vec<JobId> = state.queue.drain(..).map(|j| j.id).collect();
            for id in pending_ids {
                self.counters.cancelled.fetch_add(1, Ordering::Relaxed);
                state.settle_job(id, JobStatus::Cancelled, now, &self.counters);
            }

            for entry in state.jobs.values_mut() {
                if matches!(entry.status, JobStatus::Proving) {
                    entry.cancel_requested = true;
                    if let Some(token) = &entry.cancel_token {
                        token.cancel();
                    }
                }
            }
            cv.notify_all();
        }

        for worker in self.workers.drain(..) {
            let _ = worker.join();
        }
    }
}

fn worker_loop<I, O>(
    inner: Arc<(Mutex<ServiceState<I, O>>, Condvar)>,
    counters: Arc<Counters>,
    backend: CancellableBackend<I, O>,
) where
    I: Send + 'static,
    O: Clone + Send + 'static,
{
    loop {
        // Brief lock ONLY for job pickup; released before calling `backend`.
        let picked = {
            let (mutex, cv) = &*inner;
            let mut state = mutex.lock().expect("prove service state mutex");
            loop {
                if let Some(job) = state.queue.pop_front() {
                    if job.epoch < state.min_active_epoch {
                        let now = Instant::now();
                        counters.cancelled.fetch_add(1, Ordering::Relaxed);
                        state.settle_job(job.id, JobStatus::Cancelled, now, &counters);
                        continue;
                    }
                    let token = CancelToken::new();
                    if let Some(entry) = state.jobs.get_mut(&job.id) {
                        entry.status = JobStatus::Proving;
                        entry.cancel_token = Some(token.clone());
                    }
                    counters.in_flight.fetch_add(1, Ordering::Relaxed);
                    break Some((job.id, job.epoch, job.input, token));
                }
                if state.shutdown {
                    break None;
                }
                state = cv.wait(state).expect("prove service condvar");
            }
        };

        let Some((id, epoch, input, token)) = picked else {
            return;
        };

        // OFF-LOCK proving execution (panic-isolated so a panicking backend never poisons state).
        let started = Instant::now();
        let raw_result = catch_unwind(AssertUnwindSafe(|| backend(input, &token)));
        let elapsed_nanos = started.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        counters
            .prove_nanos
            .fetch_add(elapsed_nanos, Ordering::Relaxed);
        counters.in_flight.fetch_sub(1, Ordering::Relaxed);

        // Brief lock ONLY to settle the job, notify direct waiters, and enforce bounded eviction.
        let (mutex, _) = &*inner;
        let mut state = mutex.lock().expect("prove service state mutex");
        let now = Instant::now();
        let was_cancelled = token.is_cancelled()
            || epoch < state.min_active_epoch
            || state
                .jobs
                .get(&id)
                .is_some_and(|entry| entry.cancel_requested);

        let terminal = if was_cancelled {
            counters.cancelled.fetch_add(1, Ordering::Relaxed);
            JobStatus::Cancelled
        } else {
            match raw_result {
                Ok(Ok(output)) => {
                    counters.completed.fetch_add(1, Ordering::Relaxed);
                    JobStatus::Done(Box::new(output))
                }
                Ok(Err(err)) => {
                    counters.failed.fetch_add(1, Ordering::Relaxed);
                    JobStatus::Failed(err)
                }
                Err(payload) => {
                    let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                        format!("prover backend panicked: {s}")
                    } else if let Some(s) = payload.downcast_ref::<String>() {
                        format!("prover backend panicked: {s}")
                    } else {
                        "prover backend panicked".to_string()
                    };
                    counters.failed.fetch_add(1, Ordering::Relaxed);
                    JobStatus::Failed(msg)
                }
            }
        };

        state.settle_job(id, terminal, now, &counters);
    }
}
