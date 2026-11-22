//! Obend Sandbox (`G11` Hardened): OS Confinement (`bwrap` / Default-Deny Seatbelt / Seccomp `AF_UNIX`
//! & `ADDFD` / `PR_SET_PDEATHSIG(SIGKILL)` / Strict Env Allowlist), Pure-Rust Sandstorm `.spk`
//! `verify_strict` & Fixed `BridgeConfig` Role Extractor, Bounded `LineChannel`, Fuel-Metered Core
//! WebAssembly Sandbox (`CAP-23`), Slot-Path-Bound AEAD Secret Store, and `Grain` R0–R4 Custody.

pub mod bwrap;
pub mod capnp_wire;
pub mod cloud_custody;
pub mod gate;
pub mod grain;
pub mod line_channel;
pub mod meter;
pub mod policy;
pub mod secret_seal;
pub mod spk;
pub mod wasm_budget;

pub use bwrap::{
    BubblewrapRunner, SandboxBackend, SandboxConfig, SandboxError, SandboxRunReceipt,
    DEFAULT_MAX_PROCESS_OUTPUT_BYTES, install_pdeathsig_sigkill,
};
pub use gate::{GateStatus, LaunchGate};
pub use grain::{
    GrainBudget, GrainCapabilities, GrainExecutionReceipt, GrainExecutor, GrainOp, GrainProgram,
    GrainTermination, ReproducibilityTier, GRAIN_PAGE_SIZE, digest_slot_entries, sha256,
};
pub use line_channel::{
    BodyChannel, BodyMsg, ConfinedAction, ConfinedBrain, DEFAULT_MAX_LINE_BYTES, DoneNote,
    LineChannel, MAX_CONSECUTIVE_EMPTY_LINES, MapError, Proposal, Verdict, map_proposal,
};
pub use meter::CpuMeter;
pub use policy::{
    AddFdError, AllowedEndpoint, BpfInsn, CheckedAddFdSpec, ConfinementPolicy, ConnectFilterError,
    DoorMode, EnvAllowlistPolicy, EnvPolicyError, FORBIDDEN_ENV_KEYS, SeccompProfileSpec,
    build_hardened_seccomp_bpf, check_addfd_ioctl_result, eval_seccomp_bpf,
    validate_connect_sockaddr,
};
pub use secret_seal::{
    SECRET_ENVELOPE_MAGIC, SecretMetadata, SecretSealError, SecretSlotId, SecretValue,
    SlotBoundSecretStore, chacha20_poly1305_open, chacha20_poly1305_seal, seal_secret_for_slot,
    unseal_secret_for_slot,
};
pub use spk::{
    AppId, BRIDGE_CONFIG_PATH, BridgeConfig, Ed25519SigningKey, FileContent, MANIFEST_PATH,
    ManifestError, PermissionDef, Role, SPK_MAGIC, Spk, SpkAction, SpkArchive, SpkBuilder,
    SpkCommand, SpkError, SpkFile, SpkManifest, decode_bridge_config_capnp, ed25519_verify_strict,
    sandstorm_base32_encode, xz_compress, xz_decompress_bounded,
};
pub use wasm_budget::{
    EgressPosture, WASM_PAGE_SIZE, WasmCapTier, WasmExecutionBudget, WasmExecutionReceipt,
    WasmRunError, WasmVal, run_wasm_metered, wasm_egress_posture,
};

pub use cloud_custody::{
    AriadneIngressLog, AriadneTicket, ConfinedForkSpec, ConfinedGrainSession, CustodyAuthenticator,
    CustodyDigest, CustodyError, CustodyPoisonReason, ForkError, ForkGenesis, GrainCustodyAnchor,
    GrainCustodyHost, GrainCustodyStatus, LeaseError, PrepaidLease, SignedGrainPackage,
    compute_var_data_root, turn_request_digest,
};
