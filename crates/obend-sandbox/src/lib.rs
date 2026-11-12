//! Obend Sandbox: Bubblewrap Confinement Runner & DreggNet `Grain` R0–R4 Deterministic Executor
pub mod bwrap;
pub mod cloud_custody;
pub mod gate;
pub mod grain;
pub mod meter;
pub mod policy;

pub use bwrap::{
    BubblewrapRunner, SandboxBackend, SandboxConfig, SandboxError, SandboxRunReceipt,
    DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
};
pub use gate::{GateStatus, LaunchGate};
pub use grain::{
    digest_slot_entries, sha256, GrainBudget, GrainCapabilities, GrainExecutionReceipt,
    GrainExecutor, GrainOp, GrainProgram, GrainTermination, ReproducibilityTier, GRAIN_PAGE_SIZE,
};
pub use meter::CpuMeter;
pub use policy::ConfinementPolicy;

pub use cloud_custody::{
    compute_var_data_root, turn_request_digest, AriadneIngressLog, AriadneTicket, ConfinedForkSpec,
    ConfinedGrainSession, CustodyAuthenticator, CustodyDigest, CustodyError, CustodyPoisonReason,
    ForkError, ForkGenesis, GrainCustodyAnchor, GrainCustodyHost, GrainCustodyStatus, LeaseError,
    PrepaidLease, SignedGrainPackage,
};
