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
    install_pdeathsig_sigkill, BubblewrapRunner, SandboxBackend, SandboxConfig, SandboxError,
    SandboxRunReceipt, DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
};
pub use gate::{GateStatus, LaunchGate};
pub use grain::{
    digest_slot_entries, sha256, GrainBudget, GrainCapabilities, GrainExecutionReceipt,
    GrainExecutor, GrainOp, GrainProgram, GrainTermination, ReproducibilityTier, GRAIN_PAGE_SIZE,
};
pub use line_channel::{
    map_proposal, BodyChannel, BodyMsg, ConfinedAction, ConfinedBrain, DoneNote, LineChannel,
    MapError, Proposal, Verdict, DEFAULT_MAX_LINE_BYTES, MAX_CONSECUTIVE_EMPTY_LINES,
};
pub use meter::CpuMeter;
pub use policy::{
    build_hardened_seccomp_bpf, check_addfd_ioctl_result, eval_seccomp_bpf,
    validate_connect_sockaddr, AddFdError, AllowedEndpoint, BpfInsn, CheckedAddFdSpec,
    ConfinementPolicy, ConnectFilterError, DoorMode, EnvAllowlistPolicy, EnvPolicyError,
    SeccompProfileSpec, FORBIDDEN_ENV_KEYS,
};
pub use secret_seal::{
    chacha20_poly1305_open, chacha20_poly1305_seal, seal_secret_for_slot, unseal_secret_for_slot,
    SecretMetadata, SecretSealError, SecretSlotId, SecretValue, SlotBoundSecretStore,
    SECRET_ENVELOPE_MAGIC,
};
pub use spk::{
    decode_bridge_config_capnp, ed25519_verify_strict, sandstorm_base32_encode, xz_compress,
    xz_decompress_bounded, AppId, BridgeConfig, Ed25519SigningKey, FileContent, ManifestError,
    PermissionDef, Role, Spk, SpkAction, SpkArchive, SpkBuilder, SpkCommand, SpkError, SpkFile,
    SpkManifest, BRIDGE_CONFIG_PATH, MANIFEST_PATH, SPK_MAGIC,
};
pub use wasm_budget::{
    run_wasm_metered, wasm_egress_posture, EgressPosture, WasmCapTier, WasmExecutionBudget,
    WasmExecutionReceipt, WasmRunError, WasmVal, WASM_PAGE_SIZE,
};

pub use cloud_custody::{
    compute_var_data_root, turn_request_digest, AriadneIngressLog, AriadneTicket, ConfinedForkSpec,
    ConfinedGrainSession, CustodyAuthenticator, CustodyDigest, CustodyError, CustodyPoisonReason,
    ForkError, ForkGenesis, GrainCustodyAnchor, GrainCustodyHost, GrainCustodyStatus, LeaseError,
    PrepaidLease, SignedGrainPackage,
};
