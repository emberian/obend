//! `obend-node::net` — Multi-Validator Networked `Simplex` BFT Daemon & Sandboxed `Grain` Execution (`WS 32`)
//!
//! Upgrades `obend-node` into a real multi-validator networked cluster over OS loopback sockets
//! (`127.0.0.1:0` ephemeral TCP and UDP ports) with:
//! - Wire-serialized, Ed25519-signed, and `cSHAKE256` domain-separated `PropCert`, `SkipCert`,
//!   `FinCert`, and `SlashingReceipt` (`EquivocationSlashReceipt`) consensus messages.
//! - 4-Tier Finality Routing:
//!   - Tier 0 (`Speculative`): Local uncommitted proposal.
//!   - Tier 1 (`AttestedFastPath`): Disjoint `VaultTurn` fast-path (`disjoint_turns_commute`)
//!     committing immediately with a single quorum acknowledgement without waiting for a full
//!     `Simplex` block height.
//!   - Tier 2 (`QuorumFinal`): Contended `Simplex` BFT consensus + automated per-epoch
//!     `solve_drex_batch` primal-dual LP clearing verified via `DrexClearingCertificate::verify_with_kernel`
//!     (`ObendSession` FFI) and `FogOfWar` Merkle state root updates.
//!   - Tier 3 (`Collapsed`): `Fold::collapse` epoch checkpointing compressing finalized multi-height
//!     epoch chains into a single `CollapsedEpochReceipt` binding initial and final state roots and
//!     cumulative clearing conservation.
//! - Sandboxed `Grain` Execution (`crates/obend-sandbox`): Integrates `Powerbox`, `Mandate`,
//!   `GrainConfig`, and `SandboxRunner` (`BubblewrapRunner`, `ConfinementPolicy`, `LaunchGate`,
//!   `CpuMeter`) to enforce capability and slot confinement before turn admission.

use crate::{
    cshake256_domain, merkle_root_from_leaves, net_flow, solve_primal_dual_clearing,
    BlindedVaultMultiProof, DrexClearingCertificate, EquivocationSlashReceipt, FinCert, IpcAuth,
    LimitOrder, PropCert, SignedSimplexVote, SimplexVoteKind, SkipCert, ValidatorKeypair,
    VaultCellRecord,
};
use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
pub use obend_sandbox::{
    BubblewrapRunner, ConfinementPolicy, CpuMeter, GateStatus, LaunchGate, SandboxConfig,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Global lock serializing FFI calls into the Lean runtime across validator threads.
static FFI_KERNEL_LOCK: Mutex<()> = Mutex::new(());

/// Type alias harmonizing `SlashingReceipt` with `EquivocationSlashReceipt`.
pub type SlashingReceipt = EquivocationSlashReceipt;

/// Automated per-epoch primal-dual LP batch clearing solver (`drex-clearing@1`).
pub fn solve_drex_batch(
    currency: &str,
    goods: &str,
    epsilon: u64,
    orders: &[LimitOrder],
) -> Option<DrexClearingCertificate> {
    solve_primal_dual_clearing(currency, goods, epsilon, orders)
}

// ============================================================================
// 1. Errors & 4-Tier Finality Ladder (`Obend.Consensus.Finality`)
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
pub enum SandboxViolation {
    #[error("agent '{agent}' has no registered mandate in Powerbox")]
    MissingMandate { agent: String },
    #[error("turn agent '{actual}' does not match mandate holder '{expected}'")]
    AgentMismatch { expected: String, actual: String },
    #[error("agent '{agent}' attempted unauthorized access to slot {slot_id}")]
    UnauthorizedSlotAccess { agent: String, slot_id: u64 },
    #[error("agent '{agent}' lacks required capability {required:?}")]
    MissingCapability { agent: String, required: IpcAuth },
    #[error("agent '{agent}' exceeded mandate budget (requested {requested}, remaining {remaining})")]
    BudgetExceeded {
        agent: String,
        requested: u64,
        remaining: u64,
    },
    #[error("agent '{agent}' mandate expired at epoch {expires_at} (turn epoch {turn_epoch})")]
    MandateExpired {
        agent: String,
        turn_epoch: u64,
        expires_at: u64,
    },
    #[error("agent '{agent}' invoked disallowed method {method} under mandate caveat")]
    MethodDisallowed { agent: String, method: u64 },
    #[error("agent '{agent}' exceeded CPU meter quota (used {used_usec} us, quota {quota_usec} us)")]
    CpuQuotaExceeded {
        agent: String,
        used_usec: u64,
        quota_usec: u64,
    },
    #[error("grain launch gate '{unit}' is not started (status: {status})")]
    GateNotOperational { unit: String, status: String },
    #[error("grain confinement policy violation: {reason}")]
    InsecureConfinementPolicy { reason: String },
    #[error("turn from agent '{agent}' contains duplicate write slots")]
    DuplicateWriteSlot { agent: String },
}

/// Errors returned by durable Write-Ahead Log (`DurableNodeWal`) and outbox exposure operations
/// mirroring `Obend.Run.Durable.HRefusal`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
pub enum ExposedOnceError {
    #[error("volatile memory is down after crash; recover_from_wal() required first")]
    NodeDown,
    #[error("journal position {0} does not hold a dispatch effect")]
    NotDispatch(u64),
    #[error("outbox receipt position {0} has already been exposed (`expose_once`)")]
    AlreadyExposed(u64),
    #[error("volatile memory is already up; nothing to recover")]
    AlreadyUp,
    #[error("corrupt write-ahead log byte frame: {0}")]
    CorruptWal(String),
    #[error("token {token_id} already consumed at journal position {existing_pos} (`journal_once`)")]
    TokenAlreadyConsumed { token_id: u64, existing_pos: u64 },
    #[error("post-recovery equivocation refused at view {view} for kind {kind:?}: already voted {existing_block_hash:?}, refused {attempted_block_hash:?}")]
    EquivocationRefused {
        view: u64,
        kind: SimplexVoteKind,
        existing_block_hash: [u8; 32],
        attempted_block_hash: [u8; 32],
    },
}

#[derive(Debug, thiserror::Error)]
pub enum NodeError {
    #[error("sandbox confinement violation: {0}")]
    Sandbox(#[from] SandboxViolation),
    #[error("durable WAL / outbox error: {0}")]
    Wal(#[from] ExposedOnceError),
    #[error("FFI kernel error: {0}")]
    Ffi(#[from] ObendError),
    #[error("I/O socket error: {0}")]
    Io(#[from] std::io::Error),
    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    #[error("consensus verification failed: {0}")]
    ConsensusVerification(String),
    #[error("quorum timeout waiting for networked validators: {0}")]
    QuorumTimeout(String),
}

/// 4-Tier Finality Ladder matching `Obend.Consensus.Finality.FinalityTier`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FinalityTier {
    /// Tier 0: Local speculative turn proposal, uncommitted.
    Speculative = 0,
    /// Tier 1: Disjoint Fast-Path (`disjoint_turns_commute`), single-round quorum ack.
    AttestedFastPath = 1,
    /// Tier 2: Contended `Simplex` BFT (`FinCert`) + per-epoch `solve_drex_batch` clearing.
    QuorumFinal = 2,
    /// Tier 3: `Fold.collapse` epoch checkpointing into a `CollapsedEpochReceipt`.
    Collapsed = 3,
}

impl FinalityTier {
    pub fn rank(self) -> u8 {
        self as u8
    }

    /// Monotonic promotion check (`FinalityStep` in `Obend/Consensus/Finality.lean`).
    pub fn can_promote_to(self, target: Self) -> bool {
        self.rank() <= target.rank()
    }
}

// ============================================================================
// 2. `VaultTurn` Footprints & Tier 1 `disjoint_turns_commute` (`Obend.Vault.Hyperedge`)
// ============================================================================

/// Multi-slot wide-pullback turn structure with explicit read and write slot footprints.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VaultTurn {
    pub turn_id: [u8; 32],
    pub agent: String,
    pub read_slots: Vec<u64>,
    pub write_slots: Vec<(u64, Vec<u8>)>,
    pub required_auth: Vec<IpcAuth>,
    pub cost: u64,
    pub epoch: u64,
    pub method: u64,
}

impl VaultTurn {
    pub fn new(
        turn_id: [u8; 32],
        agent: impl Into<String>,
        read_slots: Vec<u64>,
        write_slots: Vec<(u64, Vec<u8>)>,
    ) -> Self {
        let mut required_auth = Vec::new();
        if !read_slots.is_empty() {
            required_auth.push(IpcAuth::Read);
        }
        if !write_slots.is_empty() {
            required_auth.push(IpcAuth::Write);
        }
        Self {
            turn_id,
            agent: agent.into(),
            read_slots,
            write_slots,
            required_auth,
            cost: 1,
            epoch: 1,
            method: 0,
        }
    }

    pub fn with_mandate_params(
        mut self,
        required_auth: Vec<IpcAuth>,
        cost: u64,
        epoch: u64,
        method: u64,
    ) -> Self {
        self.required_auth = required_auth;
        self.cost = cost;
        self.epoch = epoch;
        self.method = method;
        self
    }

    /// Read slot footprint (`VaultTurn.readFootprint`).
    pub fn read_footprint(&self) -> Vec<u64> {
        let mut out = Vec::new();
        for &s in &self.read_slots {
            if !out.contains(&s) {
                out.push(s);
            }
        }
        out
    }

    /// Write slot footprint (`VaultTurn.writeFootprint`).
    pub fn write_footprint(&self) -> Vec<u64> {
        self.write_slots.iter().map(|(id, _)| *id).collect()
    }

    /// Combined access footprint (`VaultTurn.accessFootprint = (readFootprint ++ writeFootprint).eraseDups`).
    pub fn access_footprint(&self) -> Vec<u64> {
        let mut out = self.read_footprint();
        for (id, _) in &self.write_slots {
            if !out.contains(id) {
                out.push(*id);
            }
        }
        out
    }

    /// Checks whether `write_slots` contains duplicate slot IDs (`nodup_cells` in `Obend.Vault.Hyperedge`).
    pub fn has_duplicate_write_slots(&self) -> bool {
        let mut seen = BTreeSet::new();
        for (id, _) in &self.write_slots {
            if !seen.insert(*id) {
                return true;
            }
        }
        false
    }

    /// Domain-separated `cSHAKE256` commitment digest of this `VaultTurn`.
    pub fn digest(&self) -> [u8; 32] {
        let mut meta = Vec::new();
        meta.extend_from_slice(&self.turn_id);
        meta.extend_from_slice(self.agent.as_bytes());
        meta.extend_from_slice(&self.cost.to_be_bytes());
        meta.extend_from_slice(&self.epoch.to_be_bytes());
        meta.extend_from_slice(&self.method.to_be_bytes());
        for &r in &self.read_slots {
            meta.extend_from_slice(&r.to_be_bytes());
        }
        let mut writes = Vec::new();
        for (slot_id, content) in &self.write_slots {
            writes.extend_from_slice(&slot_id.to_be_bytes());
            writes.extend_from_slice(&(content.len() as u64).to_be_bytes());
            writes.extend_from_slice(content);
        }
        cshake256_domain(b"obend.vault.turn", &meta, &writes)
    }

    /// Apply this turn's write deltas to a vault cell store (`Obend.Vault.applyTurn`).
    pub fn apply_to_cells(&self, cells: &mut Vec<VaultCellRecord>) {
        for (slot_id, post_content) in &self.write_slots {
            if let Some(cell) = cells.iter_mut().find(|c| c.id == *slot_id) {
                cell.content = post_content.clone();
            } else {
                let salt = cshake256_domain(
                    b"obend.vault.cell.salt",
                    &slot_id.to_be_bytes(),
                    &self.turn_id,
                );
                cells.push(VaultCellRecord {
                    id: *slot_id,
                    required: vec![IpcAuth::Read],
                    salt,
                    content: post_content.clone(),
                });
                cells.sort_by_key(|c| c.id);
            }
        }
    }
}

/// Mirrors `DisjointTurns` and `vaultTurn_disjoint_commutes` in `Obend/Vault/Hyperedge.lean`:
/// Returns `true` iff neither turn writes to any slot in the other turn's access footprint
/// (read slots union write slots) and neither turn has duplicate write slots.
pub fn disjoint_turns_commute(t1: &VaultTurn, t2: &VaultTurn) -> bool {
    if t1.has_duplicate_write_slots() || t2.has_duplicate_write_slots() {
        return false;
    }
    let w1 = t1.write_footprint();
    let w2 = t2.write_footprint();
    let acc1 = t1.access_footprint();
    let acc2 = t2.access_footprint();

    let w1_disjoint_acc2 = w1.iter().all(|c| !acc2.contains(c));
    let w2_disjoint_acc1 = w2.iter().all(|c| !acc1.contains(c));
    w1_disjoint_acc2 && w2_disjoint_acc1
}

/// Concretely verifies `vaultTurn_disjoint_commutes` on a slice of `VaultCellRecord`s:
/// checks that applying `t1` then `t2` produces the exact same `FogOfWar` Merkle root
/// and cell states as applying `t2` then `t1`.
pub fn verify_turns_commute_on_vault(
    cells: &[VaultCellRecord],
    t1: &VaultTurn,
    t2: &VaultTurn,
) -> bool {
    let mut order_12 = cells.to_vec();
    t1.apply_to_cells(&mut order_12);
    t2.apply_to_cells(&mut order_12);

    let mut order_21 = cells.to_vec();
    t2.apply_to_cells(&mut order_21);
    t1.apply_to_cells(&mut order_21);

    let leaves_12: Vec<[u8; 32]> = order_12.iter().map(|c| c.leaf_hash()).collect();
    let leaves_21: Vec<[u8; 32]> = order_21.iter().map(|c| c.leaf_hash()).collect();

    order_12 == order_21 && merkle_root_from_leaves(&leaves_12) == merkle_root_from_leaves(&leaves_21)
}

/// Validator Ed25519 acknowledgement for a Tier 1 Disjoint Fast-Path turn.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedFastPathAck {
    pub voter_id: usize,
    pub public_key: [u8; 32],
    pub turn_id: [u8; 32],
    pub turn_digest: [u8; 32],
    pub signature: Vec<u8>,
}

impl SignedFastPathAck {
    pub fn canonical_bytes(turn_id: &[u8; 32], turn_digest: &[u8; 32]) -> [u8; 32] {
        cshake256_domain(b"obend.fastpath.ack", turn_id, turn_digest)
    }

    pub fn new(kp: &ValidatorKeypair, turn: &VaultTurn) -> Self {
        let turn_digest = turn.digest();
        let msg = Self::canonical_bytes(&turn.turn_id, &turn_digest);
        let sig = kp.sign(&msg);
        Self {
            voter_id: kp.node_id,
            public_key: kp.public_key,
            turn_id: turn.turn_id,
            turn_digest,
            signature: sig.to_vec(),
        }
    }

    pub fn verify(&self) -> bool {
        if self.signature.len() != 64 {
            return false;
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&self.signature);
        let msg = Self::canonical_bytes(&self.turn_id, &self.turn_digest);
        ValidatorKeypair::verify(&self.public_key, &msg, &sig)
    }
}

/// Tier 1 Disjoint Fast-Path Quorum Certificate (`2f + 1` single-round acknowledgements).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FastPathCert {
    pub turn: VaultTurn,
    pub turn_digest: [u8; 32],
    pub acks: Vec<SignedFastPathAck>,
    pub post_state_root: [u8; 32],
    #[serde(default)]
    pub anchor_height: u64,
    pub tier: FinalityTier,
}

impl FastPathCert {
    pub fn verify(&self, quorum_size: usize) -> bool {
        if self.tier != FinalityTier::AttestedFastPath
            || self.turn.digest() != self.turn_digest
            || self.turn.has_duplicate_write_slots()
        {
            return false;
        }
        let mut seen = BTreeSet::new();
        for ack in &self.acks {
            if ack.turn_id != self.turn.turn_id
                || ack.turn_digest != self.turn_digest
                || !seen.insert(ack.voter_id)
                || !ack.verify()
            {
                return false;
            }
        }
        seen.len() >= quorum_size
    }
}

// ============================================================================
// 3. Sandboxed `Grain` Execution (`Powerbox`, `Mandate`, `GrainConfig`, `SandboxRunner`)
// ============================================================================

/// Confined agent capability mandate mirroring `Obend.Vault.Mandate.Mandate`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Mandate {
    pub grantor: String,
    pub holder: String,
    pub target: String,
    pub rights: Vec<IpcAuth>,
    pub budget: u64,
    pub allowed_slots: Vec<u64>,
    pub expires_at: u64,
    pub allowed_methods: Option<Vec<u64>>,
}

impl Mandate {
    pub fn admits_method(&self, method: u64) -> bool {
        match &self.allowed_methods {
            None => true,
            Some(list) => list.contains(&method),
        }
    }

    /// Strict sub-delegation constructor mirroring `Obend.Vault.Mandate.Mandate.subDelegate`.
    /// Narrows rights, clamps budget, intersects slot masks, bounds expiration, and conjoins caveats.
    pub fn sub_delegate(
        &self,
        child_holder: impl Into<String>,
        req_rights: &[IpcAuth],
        quota: u64,
        slot_mask: &[u64],
        term: u64,
        child_methods: Option<Vec<u64>>,
    ) -> Self {
        let rights = self
            .rights
            .iter()
            .copied()
            .filter(|r| req_rights.contains(r))
            .collect();
        let allowed_slots = self
            .allowed_slots
            .iter()
            .copied()
            .filter(|s| slot_mask.contains(s))
            .collect();
        let allowed_methods = match (&self.allowed_methods, child_methods) {
            (None, None) => None,
            (Some(parent_m), None) => Some(parent_m.clone()),
            (None, Some(child_m)) => Some(child_m),
            (Some(parent_m), Some(child_m)) => Some(
                parent_m
                    .iter()
                    .copied()
                    .filter(|m| child_m.contains(m))
                    .collect(),
            ),
        };
        Self {
            grantor: self.holder.clone(),
            holder: child_holder.into(),
            target: self.target.clone(),
            rights,
            budget: self.budget.min(quota),
            allowed_slots,
            expires_at: self.expires_at.min(term),
            allowed_methods,
        }
    }

    /// Checks `attenuates child parent` (`Obend/Vault/Mandate.lean` lines 94-100).
    pub fn attenuates(&self, parent: &Mandate) -> bool {
        let rights_sub = self.rights.iter().all(|r| parent.rights.contains(r));
        let budget_le = self.budget <= parent.budget;
        let slots_sub = self
            .allowed_slots
            .iter()
            .all(|s| parent.allowed_slots.contains(s));
        let expires_le = self.expires_at <= parent.expires_at;
        let target_eq = self.target == parent.target;
        let caveat_sub = match (&self.allowed_methods, &parent.allowed_methods) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(c), Some(p)) => c.iter().all(|m| p.contains(m)),
        };
        rights_sub && budget_le && slots_sub && expires_le && target_eq && caveat_sub
    }

    /// Validates a `VaultTurn` against this `Mandate`'s identity, capabilities, slot mask,
    /// budget, expiration epoch, and method caveat (`Obend.Vault.Mandate.checkInvocation`).
    pub fn check_turn(&self, turn: &VaultTurn) -> Result<(), SandboxViolation> {
        if turn.agent != self.holder {
            return Err(SandboxViolation::AgentMismatch {
                expected: self.holder.clone(),
                actual: turn.agent.clone(),
            });
        }
        if turn.has_duplicate_write_slots() {
            return Err(SandboxViolation::DuplicateWriteSlot {
                agent: turn.agent.clone(),
            });
        }
        if turn.epoch > self.expires_at {
            return Err(SandboxViolation::MandateExpired {
                agent: turn.agent.clone(),
                turn_epoch: turn.epoch,
                expires_at: self.expires_at,
            });
        }
        if !self.admits_method(turn.method) {
            return Err(SandboxViolation::MethodDisallowed {
                agent: turn.agent.clone(),
                method: turn.method,
            });
        }
        // Check explicit required capabilities as well as implicit Read/Write capabilities
        let mut needed = turn.required_auth.clone();
        if !turn.read_slots.is_empty() && !needed.contains(&IpcAuth::Read) {
            needed.push(IpcAuth::Read);
        }
        if !turn.write_slots.is_empty() && !needed.contains(&IpcAuth::Write) {
            needed.push(IpcAuth::Write);
        }
        for req in needed {
            if !self.rights.contains(&req) {
                return Err(SandboxViolation::MissingCapability {
                    agent: turn.agent.clone(),
                    required: req,
                });
            }
        }
        // Enforce slot mask confinement over all read and write slots in the turn
        for slot_id in turn.access_footprint() {
            if !self.allowed_slots.contains(&slot_id) {
                return Err(SandboxViolation::UnauthorizedSlotAccess {
                    agent: turn.agent.clone(),
                    slot_id,
                });
            }
        }
        if turn.cost > self.budget {
            return Err(SandboxViolation::BudgetExceeded {
                agent: turn.agent.clone(),
                requested: turn.cost,
                remaining: self.budget,
            });
        }
        Ok(())
    }
}

/// Capability `Powerbox` table managing active agent `Mandate`s and cumulative resource budgets.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Powerbox {
    pub target_domain: String,
    pub mandates: BTreeMap<String, Mandate>,
    pub spent_budget: BTreeMap<String, u64>,
}

impl Powerbox {
    pub fn new(target_domain: impl Into<String>) -> Self {
        Self {
            target_domain: target_domain.into(),
            mandates: BTreeMap::new(),
            spent_budget: BTreeMap::new(),
        }
    }

    pub fn grant_mandate(&mut self, mandate: Mandate) -> Result<(), SandboxViolation> {
        let holder = mandate.holder.clone();
        self.mandates.insert(holder.clone(), mandate);
        self.spent_budget.entry(holder).or_insert(0);
        Ok(())
    }

    /// Strictly attenuate an existing parent mandate to a child agent (`subDelegate_attenuates`).
    /// Requires the parent mandate to hold `IpcAuth::Grant` and clamps the delegated quota
    /// to the parent's remaining unspent budget.
    pub fn delegate(
        &mut self,
        parent_holder: &str,
        child_holder: &str,
        req_rights: &[IpcAuth],
        quota: u64,
        slot_mask: &[u64],
        term: u64,
        allowed_methods: Option<Vec<u64>>,
    ) -> Result<Mandate, SandboxViolation> {
        let parent = self.mandates.get(parent_holder).ok_or_else(|| {
            SandboxViolation::MissingMandate {
                agent: parent_holder.to_string(),
            }
        })?;
        if !parent.rights.contains(&IpcAuth::Grant) {
            return Err(SandboxViolation::MissingCapability {
                agent: parent_holder.to_string(),
                required: IpcAuth::Grant,
            });
        }
        let parent_remaining = self.remaining_budget(parent_holder).unwrap_or(0);
        let clamped_quota = quota.min(parent_remaining);
        let child = parent.sub_delegate(
            child_holder,
            req_rights,
            clamped_quota,
            slot_mask,
            term,
            allowed_methods,
        );
        debug_assert!(child.attenuates(parent));
        self.grant_mandate(child.clone())?;
        Ok(child)
    }

    pub fn remaining_budget(&self, agent: &str) -> Option<u64> {
        let m = self.mandates.get(agent)?;
        let spent = self.spent_budget.get(agent).copied().unwrap_or(0);
        Some(m.budget.saturating_sub(spent))
    }

    /// Check a `VaultTurn` against its agent's `Mandate` and deduct `turn.cost` from remaining quota.
    pub fn check_and_consume(&mut self, turn: &VaultTurn) -> Result<(), SandboxViolation> {
        let mandate = self
            .mandates
            .get(&turn.agent)
            .ok_or_else(|| SandboxViolation::MissingMandate {
                agent: turn.agent.clone(),
            })?;
        mandate.check_turn(turn)?;
        let spent = self.spent_budget.get(&turn.agent).copied().unwrap_or(0);
        let remaining = mandate.budget.saturating_sub(spent);
        if turn.cost > remaining {
            return Err(SandboxViolation::BudgetExceeded {
                agent: turn.agent.clone(),
                requested: turn.cost,
                remaining,
            });
        }
        self.spent_budget
            .insert(turn.agent.clone(), spent + turn.cost);
        Ok(())
    }
}

/// Configuration for a sandboxed `Grain` execution unit binding `obend-sandbox` primitives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrainConfig {
    pub unit_id: String,
    pub state_dir: PathBuf,
    pub sandbox_config: SandboxConfig,
    pub policy: ConfinementPolicy,
    pub cpu_quota_usec: u64,
}

impl GrainConfig {
    /// Construct a strict, network-isolated `GrainConfig` for `agent` using `obend-sandbox`.
    pub fn strict_for_agent(agent: &str, state_dir: PathBuf) -> Self {
        let unit_id = format!("obend-grain-{agent}");
        let mut sandbox_config = SandboxConfig::default();
        sandbox_config.allow_network = false;
        sandbox_config.workspace_dir = state_dir.join(format!("ws-{agent}"));
        Self {
            unit_id,
            state_dir,
            sandbox_config,
            policy: ConfinementPolicy::strict(),
            cpu_quota_usec: 10_000_000, // 10s default CPU quota
        }
    }

    /// Verify that the `GrainConfig` enforces strict Bubblewrap namespace and capability isolation.
    pub fn verify_strict_policy(&self) -> Result<(), SandboxViolation> {
        if self.sandbox_config.allow_network || !self.policy.unshare_net {
            return Err(SandboxViolation::InsecureConfinementPolicy {
                reason: "untrusted Grain must have network namespace unshared".to_string(),
            });
        }
        if !self.policy.drop_all_caps
            || !self.policy.disable_userns
            || !self.policy.unshare_user
            || !self.policy.unshare_pid
            || !self.policy.unshare_ipc
            || !self.policy.unshare_uts
            || !self.policy.unshare_cgroup
            || !self.policy.die_with_parent
            || !self.policy.new_session
            || !self.policy.clearenv
        {
            return Err(SandboxViolation::InsecureConfinementPolicy {
                reason: "untrusted Grain must drop all capabilities and isolate user/pid/ipc/uts/cgroup namespaces"
                    .to_string(),
            });
        }
        Ok(())
    }

    /// Build the concrete `bwrap` command-line flags via `obend_sandbox::BubblewrapRunner`.
    pub fn bwrap_flags(&self) -> Vec<String> {
        BubblewrapRunner::build_flags(&self.sandbox_config)
    }
}

/// Sandboxed `Grain` execution gatekeeper integrating `Powerbox`, `GrainConfig`, `LaunchGate`, and `CpuMeter`.
#[derive(Debug, Clone)]
pub struct SandboxRunner {
    pub powerbox: Powerbox,
    pub grain_configs: BTreeMap<String, GrainConfig>,
    pub rejected_turns: Vec<(VaultTurn, SandboxViolation)>,
    pub admitted_turns: usize,
}

impl SandboxRunner {
    pub fn new(powerbox: Powerbox) -> Self {
        Self {
            powerbox,
            grain_configs: BTreeMap::new(),
            rejected_turns: Vec::new(),
            admitted_turns: 0,
        }
    }

    /// Register and arm a confined `Grain` unit via `obend_sandbox::LaunchGate` and `CpuMeter`.
    pub fn register_grain(
        &mut self,
        agent: &str,
        config: GrainConfig,
    ) -> Result<GateStatus, SandboxViolation> {
        config.verify_strict_policy()?;
        let _ = std::fs::create_dir_all(&config.state_dir);
        let gate = LaunchGate::new(&config.state_dir, &config.unit_id);
        let _ = std::fs::remove_file(gate.gate_path());
        gate.init()
            .map_err(|reason| SandboxViolation::GateNotOperational {
                unit: config.unit_id.clone(),
                status: reason,
            })?;
        gate.transition_to_started()
            .map_err(|reason| SandboxViolation::GateNotOperational {
                unit: config.unit_id.clone(),
                status: reason,
            })?;
        CpuMeter::write_cpu_record(&config.state_dir, &config.unit_id, 0).map_err(|reason| {
            SandboxViolation::GateNotOperational {
                unit: config.unit_id.clone(),
                status: reason,
            }
        })?;
        let status = gate
            .status()
            .map_err(|reason| SandboxViolation::GateNotOperational {
                unit: config.unit_id.clone(),
                status: reason,
            })?;
        self.grain_configs.insert(agent.to_string(), config);
        Ok(status)
    }

    /// Query the `LaunchGate` status of a registered agent `Grain`.
    pub fn grain_gate_status(&self, agent: &str) -> Option<GateStatus> {
        let cfg = self.grain_configs.get(agent)?;
        let gate = LaunchGate::new(&cfg.state_dir, &cfg.unit_id);
        gate.status().ok()
    }

    /// Query the metered CPU usage (`obend-grain-cpu-v1`) of a registered agent `Grain`.
    pub fn grain_cpu_usec(&self, agent: &str) -> Option<u64> {
        let cfg = self.grain_configs.get(agent)?;
        let path = cfg.state_dir.join(format!("{}.cpu", cfg.unit_id));
        CpuMeter::read_cpu_record(&path).ok()
    }

    /// Capability-check and meter an untrusted `Grain` turn before admitting it into the node pipeline.
    /// If the turn violates its `Mandate` (e.g. unauthorized slot access), fences the agent's
    /// `LaunchGate` and records the rejection.
    pub fn validate_and_meter_turn(
        &mut self,
        turn: &VaultTurn,
        cpu_usec_delta: u64,
    ) -> Result<(), SandboxViolation> {
        if let Some(cfg) = self.grain_configs.get(&turn.agent).cloned() {
            cfg.verify_strict_policy()?;
            let gate = LaunchGate::new(&cfg.state_dir, &cfg.unit_id);
            let status = gate
                .status()
                .map_err(|e| SandboxViolation::GateNotOperational {
                    unit: cfg.unit_id.clone(),
                    status: e,
                })?;
            if status != GateStatus::Started {
                let err = SandboxViolation::GateNotOperational {
                    unit: cfg.unit_id.clone(),
                    status: format!("{status:?}"),
                };
                self.rejected_turns.push((turn.clone(), err.clone()));
                return Err(err);
            }

            let cpu_path = cfg.state_dir.join(format!("{}.cpu", cfg.unit_id));
            let prev_cpu = CpuMeter::read_cpu_record(&cpu_path).unwrap_or(0);
            let new_cpu = prev_cpu.saturating_add(cpu_usec_delta);
            if new_cpu > cfg.cpu_quota_usec {
                let _ = gate.fence();
                let err = SandboxViolation::CpuQuotaExceeded {
                    agent: turn.agent.clone(),
                    used_usec: new_cpu,
                    quota_usec: cfg.cpu_quota_usec,
                };
                self.rejected_turns.push((turn.clone(), err.clone()));
                return Err(err);
            }

            if let Err(violation) = self.powerbox.check_and_consume(turn) {
                let _ = gate.fence();
                self.rejected_turns.push((turn.clone(), violation.clone()));
                return Err(violation);
            }

            let _ = CpuMeter::write_cpu_record(&cfg.state_dir, &cfg.unit_id, new_cpu);
            self.admitted_turns += 1;
            Ok(())
        } else {
            if let Err(violation) = self.powerbox.check_and_consume(turn) {
                self.rejected_turns.push((turn.clone(), violation.clone()));
                return Err(violation);
            }
            self.admitted_turns += 1;
            Ok(())
        }
    }
}

// ============================================================================
// 4. Tier 2 Block Payloads & Tier 3 `Fold.collapse` Epoch Checkpointing
// ============================================================================

/// Contended block payload proposed in a `Simplex` BFT height.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockPayload {
    pub height: u64,
    pub view: u64,
    pub turns: Vec<VaultTurn>,
    pub drex_currency: String,
    pub drex_goods: String,
    pub drex_epsilon: u64,
    pub drex_orders: Vec<LimitOrder>,
}

impl BlockPayload {
    pub fn is_empty(&self) -> bool {
        self.turns.is_empty() && self.drex_orders.is_empty()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(self).expect("BlockPayload serializes to JSON")
    }
}

/// Finalized block record produced at each `Simplex` BFT height upon reaching `FinCert` quorum.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalizedBlockRecord {
    pub height: u64,
    pub view: u64,
    pub block_hash: [u8; 32],
    pub parent_hash: [u8; 32],
    pub prop_cert: Option<PropCert>,
    pub fin_cert: FinCert,
    pub payload: BlockPayload,
    #[serde(default)]
    pub pre_block_fast_path_turns: Vec<VaultTurn>,
    pub clearing_cert: Option<DrexClearingCertificate>,
    pub clearing_kernel_verified: bool,
    pub pre_state_root: [u8; 32],
    pub post_state_root: [u8; 32],
    pub multiproof: BlindedVaultMultiProof,
    pub tier: FinalityTier,
}

/// Tier 3 `Fold.collapse` compressed epoch receipt binding initial and final state roots,
/// active block transitions (with empty-block pruning invariance), and cumulative clearing conservation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollapsedEpochReceipt {
    pub epoch_id: u64,
    pub start_height: u64,
    pub end_height: u64,
    pub total_block_count: usize,
    pub active_block_count: usize,
    pub pruned_empty_block_count: usize,
    pub initial_state_root: [u8; 32],
    pub final_state_root: [u8; 32],
    pub active_block_hashes: Vec<[u8; 32]>,
    pub fin_cert_hashes: Vec<[u8; 32]>,
    pub cumulative_clearing_volume: i64,
    pub cumulative_currency_net_flow: i64,
    pub cumulative_goods_net_flow: i64,
    pub clearing_conserved: bool,
    pub collapsed_root: [u8; 32],
    pub ffi_verified: bool,
    pub tier: FinalityTier,
}

impl CollapsedEpochReceipt {
    /// Compute the canonical domain-separated `cSHAKE256` root for an epoch rollup.
    pub fn compute_collapsed_root(
        epoch_id: u64,
        start_height: u64,
        end_height: u64,
        initial_state_root: &[u8; 32],
        final_state_root: &[u8; 32],
        active_block_hashes: &[[u8; 32]],
        cumulative_clearing_volume: i64,
    ) -> [u8; 32] {
        let trace_merkle = merkle_root_from_leaves(active_block_hashes);
        let mut left = Vec::with_capacity(88);
        left.extend_from_slice(&epoch_id.to_be_bytes());
        left.extend_from_slice(&start_height.to_be_bytes());
        left.extend_from_slice(&end_height.to_be_bytes());
        left.extend_from_slice(initial_state_root);
        left.extend_from_slice(final_state_root);

        let mut right = Vec::with_capacity(40);
        right.extend_from_slice(&trace_merkle);
        right.extend_from_slice(&cumulative_clearing_volume.to_be_bytes());

        cshake256_domain(b"obend.fold.collapse.epoch", &left, &right)
    }

    /// Stranger-checkable verification of the `CollapsedEpochReceipt` and FFI receipt binding.
    pub fn verify(&self, session: &mut ObendSession) -> Result<bool, ObendError> {
        if self.tier != FinalityTier::Collapsed
            || !self.clearing_conserved
            || self.cumulative_currency_net_flow != 0
            || self.cumulative_goods_net_flow != 0
            || self.active_block_count + self.pruned_empty_block_count != self.total_block_count
        {
            return Ok(false);
        }
        let expected = Self::compute_collapsed_root(
            self.epoch_id,
            self.start_height,
            self.end_height,
            &self.initial_state_root,
            &self.final_state_root,
            &self.active_block_hashes,
            self.cumulative_clearing_volume,
        );
        if self.collapsed_root != expected {
            return Ok(false);
        }
        let _guard = FFI_KERNEL_LOCK.lock().unwrap();
        session.verify_receipt(&self.collapsed_root)
    }
}

/// Namespace mirroring `Obend.Fold.Collapse` for compressing finalized multi-height epoch chains.
pub struct Fold;

impl Fold {
    /// Compress a finalized multi-height block chain into a single `CollapsedEpochReceipt`
    /// (`Obend.Fold.Collapse.collapseTrace`), verifying empty-block pruning invariance
    /// (`collapseTrace_prune_empty`) and cumulative `drex-clearing@1` conservation.
    pub fn collapse(
        epoch_id: u64,
        initial_cells: &[VaultCellRecord],
        blocks: &[FinalizedBlockRecord],
        session: &mut ObendSession,
    ) -> Result<CollapsedEpochReceipt, NodeError> {
        if blocks.is_empty() {
            return Err(NodeError::ConsensusVerification(
                "cannot collapse empty block range".to_string(),
            ));
        }

        for pair in blocks.windows(2) {
            if pair[1].height != pair[0].height + 1 || pair[1].parent_hash != pair[0].block_hash {
                return Err(NodeError::ConsensusVerification(
                    "epoch blocks are not height-contiguous or hash-linked".to_string(),
                ));
            }
        }
        for blk in blocks {
            if blk.fin_cert.block_hash != blk.block_hash || !blk.fin_cert.verify(1) {
                return Err(NodeError::ConsensusVerification(format!(
                    "block at height {} has invalid FinCert",
                    blk.height
                )));
            }
        }

        let start_height = blocks.first().unwrap().height;
        let end_height = blocks.last().unwrap().height;
        let initial_leaves: Vec<[u8; 32]> = initial_cells.iter().map(|c| c.leaf_hash()).collect();
        let computed_initial_root = merkle_root_from_leaves(&initial_leaves);
        let initial_state_root = blocks.first().unwrap().pre_state_root;
        if computed_initial_root != initial_state_root {
            return Err(NodeError::ConsensusVerification(
                "initial_cells Merkle root does not match epoch pre_state_root".to_string(),
            ));
        }

        // Fold full trace (including empty/skip blocks and any interleaved Tier 1 fast-path turns)
        let mut full_folded = initial_cells.to_vec();
        for (idx, blk) in blocks.iter().enumerate() {
            if idx > 0 {
                for fp_turn in &blk.pre_block_fast_path_turns {
                    fp_turn.apply_to_cells(&mut full_folded);
                }
            }
            let pre_leaves: Vec<[u8; 32]> = full_folded.iter().map(|c| c.leaf_hash()).collect();
            if merkle_root_from_leaves(&pre_leaves) != blk.pre_state_root {
                return Err(NodeError::ConsensusVerification(format!(
                    "block height {} pre_state_root mismatch during Fold.collapse",
                    blk.height
                )));
            }
            Self::apply_block_to_cells(&mut full_folded, &blk.payload, blk.clearing_cert.as_ref());
        }
        let full_leaves: Vec<[u8; 32]> = full_folded.iter().map(|c| c.leaf_hash()).collect();
        let full_root = merkle_root_from_leaves(&full_leaves);

        // Fold pruned active trace (`filterActive` / `collapseTrace_prune_empty` in `Obend/Fold/Collapse.lean`)
        let active_blocks: Vec<(usize, &FinalizedBlockRecord)> = blocks
            .iter()
            .enumerate()
            .filter(|(idx, b)| {
                !b.payload.is_empty() || (*idx > 0 && !b.pre_block_fast_path_turns.is_empty())
            })
            .collect();
        let mut pruned_folded = initial_cells.to_vec();
        for &(idx, blk) in &active_blocks {
            if idx > 0 {
                for fp_turn in &blk.pre_block_fast_path_turns {
                    fp_turn.apply_to_cells(&mut pruned_folded);
                }
            }
            Self::apply_block_to_cells(&mut pruned_folded, &blk.payload, blk.clearing_cert.as_ref());
        }
        let pruned_leaves: Vec<[u8; 32]> = pruned_folded.iter().map(|c| c.leaf_hash()).collect();
        let pruned_root = merkle_root_from_leaves(&pruned_leaves);

        let final_state_root = blocks.last().unwrap().post_state_root;
        if full_root != pruned_root || full_root != final_state_root {
            return Err(NodeError::ConsensusVerification(
                "Fold.collapse state root mismatch across full vs pruned active trace".to_string(),
            ));
        }

        // Verify cumulative clearing conservation across all blocks in the epoch
        let mut cumulative_clearing_volume = 0i64;
        let mut cumulative_currency_net_flow = 0i64;
        let mut cumulative_goods_net_flow = 0i64;
        let mut clearing_conserved = true;

        for blk in blocks {
            if let Some(cert) = &blk.clearing_cert {
                if !blk.clearing_kernel_verified || cert.duality_gap > (cert.epsilon as i64) {
                    clearing_conserved = false;
                }
                cumulative_clearing_volume += cert.objective_volume;

                // Collect all distinct accounts participating in transfers
                let mut accounts = BTreeSet::new();
                for o in &blk.payload.drex_orders {
                    accounts.insert(o.account.as_str());
                }
                for t in &cert.transfers {
                    accounts.insert(t.source.as_str());
                    accounts.insert(t.destination.as_str());
                }
                let block_curr_net: i64 = accounts
                    .iter()
                    .map(|acct| net_flow(&cert.transfers, acct, &cert.currency))
                    .sum();
                let block_goods_net: i64 = accounts
                    .iter()
                    .map(|acct| net_flow(&cert.transfers, acct, &cert.goods))
                    .sum();
                cumulative_currency_net_flow += block_curr_net;
                cumulative_goods_net_flow += block_goods_net;
                if block_curr_net != 0 || block_goods_net != 0 {
                    clearing_conserved = false;
                }
            }
        }

        if !clearing_conserved {
            return Err(NodeError::ConsensusVerification(
                "cumulative clearing conservation violated in epoch".to_string(),
            ));
        }

        let active_block_hashes: Vec<[u8; 32]> =
            active_blocks.iter().map(|(_, b)| b.block_hash).collect();
        let fin_cert_hashes: Vec<[u8; 32]> = blocks.iter().map(|b| b.fin_cert.block_hash).collect();
        let collapsed_root = CollapsedEpochReceipt::compute_collapsed_root(
            epoch_id,
            start_height,
            end_height,
            &initial_state_root,
            &final_state_root,
            &active_block_hashes,
            cumulative_clearing_volume,
        );

        let ffi_verified = {
            let _guard = FFI_KERNEL_LOCK.lock().unwrap();
            let tid = session.propose_turn(&collapsed_root)?;
            session.commit_turn(&tid)?;
            session.verify_receipt(&collapsed_root)?
        };

        Ok(CollapsedEpochReceipt {
            epoch_id,
            start_height,
            end_height,
            total_block_count: blocks.len(),
            active_block_count: active_blocks.len(),
            pruned_empty_block_count: blocks.len() - active_blocks.len(),
            initial_state_root,
            final_state_root,
            active_block_hashes,
            fin_cert_hashes,
            cumulative_clearing_volume,
            cumulative_currency_net_flow,
            cumulative_goods_net_flow,
            clearing_conserved,
            collapsed_root,
            ffi_verified,
            tier: FinalityTier::Collapsed,
        })
    }

    /// Deterministic single-block state transition helper used by both `NetworkedValidatorNode` and `Fold::collapse`.
    pub fn apply_block_to_cells(
        cells: &mut Vec<VaultCellRecord>,
        payload: &BlockPayload,
        clearing_cert: Option<&DrexClearingCertificate>,
    ) {
        for turn in &payload.turns {
            turn.apply_to_cells(cells);
        }
        if let Some(cert) = clearing_cert {
            // Bind the verified drex-clearing@1 certificate digest into reserved clearing slot 0xD2E8
            const CLEARING_SLOT_ID: u64 = 0xD2E8;
            let salt = cshake256_domain(
                b"obend.vault.clearing.salt",
                &payload.height.to_be_bytes(),
                &cert.digest,
            );
            if let Some(cell) = cells.iter_mut().find(|c| c.id == CLEARING_SLOT_ID) {
                cell.salt = salt;
                cell.content = cert.digest.to_vec();
            } else {
                cells.push(VaultCellRecord {
                    id: CLEARING_SLOT_ID,
                    required: vec![IpcAuth::Read],
                    salt,
                    content: cert.digest.to_vec(),
                });
                cells.sort_by_key(|c| c.id);
            }
        }
    }
}

// ============================================================================
// 5. Wire Protocol & Real TCP/UDP Loopback `NetworkedValidatorNode`
// ============================================================================

/// Underlying socket transport protocol used by validator nodes on `127.0.0.1:0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransportProtocol {
    Tcp,
    Udp,
}

/// Consensus and fast-path messages exchanged over TCP/UDP loopback sockets.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConsensusNetMessage {
    /// Leader block proposal (`PropCert`) + contended block payload.
    Propose(PropCert, BlockPayload),
    /// Validator vote (`Propose`, `Vote`, `Skip`, or `Finalize`).
    Vote(SignedSimplexVote),
    /// Assembled `SkipCert` ($2f + 1$ `Skip` votes) advancing view.
    SkipCertificate(SkipCert),
    /// Assembled `FinCert` ($2f + 1$ `Finalize` votes) finalizing block at `view`/`height`.
    FinalizationCertificate(FinCert, BlockPayload),
    /// Accountable Byzantine equivocation slashing receipt (`SlashingReceipt`).
    Slashing(SlashingReceipt),
    /// Tier 1 Disjoint Fast-Path turn proposal.
    FastPathPropose(VaultTurn),
    /// Tier 1 Disjoint Fast-Path validator acknowledgement (`SignedFastPathAck`).
    FastPathAck(SignedFastPathAck),
    /// Tier 1 Disjoint Fast-Path quorum certificate (`FastPathCert`).
    FastPathCommit(FastPathCert),
}

/// Authenticated wire frame carrying a `cSHAKE256` domain-separated digest and `Ed25519` signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WireEnvelope {
    pub magic: [u8; 4],
    pub version: u8,
    pub sender_id: usize,
    pub sender_pk: [u8; 32],
    pub payload: ConsensusNetMessage,
    pub payload_digest: [u8; 32],
    pub signature: Vec<u8>,
}

impl WireEnvelope {
    pub const MAGIC: [u8; 4] = *b"OBND";
    pub const VERSION: u8 = 1;

    pub fn create(kp: &ValidatorKeypair, payload: ConsensusNetMessage) -> Self {
        let payload_bytes = serde_json::to_vec(&payload).expect("serialize ConsensusNetMessage");
        let payload_digest = cshake256_domain(
            b"obend.net.wire",
            &kp.node_id.to_be_bytes(),
            &payload_bytes,
        );
        let sig = kp.sign(&payload_digest);
        Self {
            magic: Self::MAGIC,
            version: Self::VERSION,
            sender_id: kp.node_id,
            sender_pk: kp.public_key,
            payload,
            payload_digest,
            signature: sig.to_vec(),
        }
    }

    pub fn verify(&self, peer_public_keys: &[[u8; 32]]) -> bool {
        if self.magic != Self::MAGIC
            || self.version != Self::VERSION
            || self.signature.len() != 64
        {
            return false;
        }
        let Some(expected_pk) = peer_public_keys.get(self.sender_id) else {
            return false;
        };
        if &self.sender_pk != expected_pk {
            return false;
        }
        let Ok(payload_bytes) = serde_json::to_vec(&self.payload) else {
            return false;
        };
        let expected_digest = cshake256_domain(
            b"obend.net.wire",
            &self.sender_id.to_be_bytes(),
            &payload_bytes,
        );
        if self.payload_digest != expected_digest {
            return false;
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&self.signature);
        ValidatorKeypair::verify(&self.sender_pk, &self.payload_digest, &sig)
    }
}

// ============================================================================
// 5b. Durable Consensus & Outbox Write-Ahead Log (`DurableNodeWal`, `Obend.Run.Durable`)
// ============================================================================

/// Durable receipt identity naming a position in the Write-Ahead Log (`Obend.Run.Durable`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OutboxReceiptId(pub u64);

impl OutboxReceiptId {
    pub fn pos(self) -> u64 {
        self.0
    }
}

impl From<u64> for OutboxReceiptId {
    fn from(pos: u64) -> Self {
        Self(pos)
    }
}

impl From<OutboxReceiptId> for u64 {
    fn from(id: OutboxReceiptId) -> Self {
        id.0
    }
}

/// Write-Ahead Log entry recorded before consensus messages or dispatch effects are exposed (`Obend.Run.Durable`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WalEntry {
    /// Validator vote cast in a `Simplex` view (`Propose`, `Vote`, `Skip`, or `Finalize`).
    VoteCast(SignedSimplexVote),
    /// Tier 2 finalized block record (`FinCert` quorum).
    BlockFinalized(FinalizedBlockRecord),
    /// Tier 1 disjoint fast-path commit certificate (`FastPathCert`).
    FastPathCommitted(FastPathCert),
    /// View-skip certificate (`SkipCert`).
    SkipCertified(SkipCert),
    /// Tier 3 collapsed epoch receipt (`CollapsedEpochReceipt`).
    EpochCollapsed(CollapsedEpochReceipt),
    /// Accepted dispatch effect (`Obend.Run.Durable.JEvent.dispatch`) with optional one-use token ID.
    DispatchEffect {
        turn: VaultTurn,
        token_id: Option<u64>,
    },
    /// Durable outbox exposure marker recording that journal position `pos` has been exposed (`expose n`).
    OutboxExposed {
        pos: u64,
    },
}

/// Durable Consensus & Outbox Write-Ahead Log (`Obend.Run.Durable.DState`):
/// - `journal`: durable append-only log of accepted consensus and dispatch events (`Vec<WalEntry>`),
/// - `outbox`: durable set of exposed journal positions (`BTreeSet<u64>`),
/// - `byte_log`: serialized, length-prefixed, `cSHAKE256`-authenticated byte log,
/// - volatile in-memory state (`memory_up`, `voted_by_view`, `highest_voted_view`, `consumed_tokens`, etc.)
///   lost on `simulate_crash()` and deterministically reconstructed by `recover_from_wal()`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DurableNodeWal {
    /// Durable append-only journal (`DState.journal`).
    pub journal: Vec<WalEntry>,
    /// Durable exposed outbox receipt positions (`DState.outbox`).
    pub outbox: BTreeSet<u64>,
    /// Durable framed & `cSHAKE256`-authenticated byte log of all journal and outbox events.
    pub byte_log: Vec<u8>,
    /// Whether volatile memory is currently up (`DState.mem.isSome`).
    pub memory_up: bool,
    /// Volatile in-memory map of `(view, kind_tag) -> SignedSimplexVote` preventing double-voting in the same view.
    pub voted_by_view: BTreeMap<(u64, u8), SignedSimplexVote>,
    /// Volatile in-memory highest voted view.
    pub highest_voted_view: u64,
    /// Volatile in-memory finalized blocks replayed from the journal.
    pub replayed_blocks: Vec<FinalizedBlockRecord>,
    /// Volatile in-memory Tier 1 fast-path certificates replayed from the journal.
    pub replayed_fast_path: Vec<FastPathCert>,
    /// Volatile in-memory `SkipCert`s replayed from the journal.
    pub replayed_skip_certs: Vec<SkipCert>,
    /// Volatile in-memory Tier 3 `CollapsedEpochReceipt`s replayed from the journal.
    pub replayed_epochs: Vec<CollapsedEpochReceipt>,
    /// Volatile in-memory map of `token_id -> journal_pos` enforcing `journal_once` / `exposed_once`.
    pub consumed_tokens: BTreeMap<u64, u64>,
}

impl Default for DurableNodeWal {
    fn default() -> Self {
        Self::new()
    }
}

impl DurableNodeWal {
    pub const FRAME_MAGIC: [u8; 4] = *b"OWAL";

    pub fn vote_kind_tag(kind: SimplexVoteKind) -> u8 {
        match kind {
            SimplexVoteKind::Propose => 0,
            SimplexVoteKind::Vote => 1,
            SimplexVoteKind::Skip => 2,
            SimplexVoteKind::Finalize => 3,
        }
    }

    pub fn new() -> Self {
        Self {
            journal: Vec::new(),
            outbox: BTreeSet::new(),
            byte_log: Vec::new(),
            memory_up: true,
            voted_by_view: BTreeMap::new(),
            highest_voted_view: 0,
            replayed_blocks: Vec::new(),
            replayed_fast_path: Vec::new(),
            replayed_skip_certs: Vec::new(),
            replayed_epochs: Vec::new(),
            consumed_tokens: BTreeMap::new(),
        }
    }

    fn append_raw_frame(byte_log: &mut Vec<u8>, entry: &WalEntry) {
        let payload = serde_json::to_vec(entry).expect("WalEntry serializes to JSON");
        let len_bytes = (payload.len() as u32).to_be_bytes();
        let digest = cshake256_domain(b"obend.durable.wal.frame", &len_bytes, &payload);
        byte_log.extend_from_slice(&Self::FRAME_MAGIC);
        byte_log.extend_from_slice(&len_bytes);
        byte_log.extend_from_slice(&digest);
        byte_log.extend_from_slice(&payload);
    }

    fn apply_entry_to_volatile(&mut self, pos: u64, entry: &WalEntry) -> Result<(), ExposedOnceError> {
        match entry {
            WalEntry::VoteCast(vote) => {
                self.check_can_vote_inner(vote.view, vote.kind, vote.block_hash)?;
                let key = (vote.view, Self::vote_kind_tag(vote.kind));
                self.voted_by_view.entry(key).or_insert_with(|| vote.clone());
                if vote.view > self.highest_voted_view {
                    self.highest_voted_view = vote.view;
                }
            }
            WalEntry::BlockFinalized(blk) => {
                if blk.view > self.highest_voted_view {
                    self.highest_voted_view = blk.view;
                }
                if !self.replayed_blocks.iter().any(|b| b.height == blk.height) {
                    self.replayed_blocks.push(blk.clone());
                }
            }
            WalEntry::FastPathCommitted(cert) => {
                if !self
                    .replayed_fast_path
                    .iter()
                    .any(|c| c.turn.turn_id == cert.turn.turn_id)
                {
                    self.replayed_fast_path.push(cert.clone());
                }
            }
            WalEntry::SkipCertified(sc) => {
                if sc.view > self.highest_voted_view {
                    self.highest_voted_view = sc.view;
                }
                if !self.replayed_skip_certs.iter().any(|c| c.view == sc.view) {
                    self.replayed_skip_certs.push(sc.clone());
                }
            }
            WalEntry::EpochCollapsed(receipt) => {
                if !self
                    .replayed_epochs
                    .iter()
                    .any(|r| r.epoch_id == receipt.epoch_id)
                {
                    self.replayed_epochs.push(receipt.clone());
                }
            }
            WalEntry::DispatchEffect { token_id, .. } => {
                if let Some(tok) = token_id {
                    if let Some(&existing_pos) = self.consumed_tokens.get(tok) {
                        if existing_pos != pos {
                            return Err(ExposedOnceError::TokenAlreadyConsumed {
                                token_id: *tok,
                                existing_pos,
                            });
                        }
                    } else {
                        self.consumed_tokens.insert(*tok, pos);
                    }
                }
            }
            WalEntry::OutboxExposed { pos: exp_pos } => {
                self.outbox.insert(*exp_pos);
            }
        }
        Ok(())
    }

    fn check_can_vote_inner(
        &self,
        view: u64,
        kind: SimplexVoteKind,
        block_hash: [u8; 32],
    ) -> Result<(), ExposedOnceError> {
        let key = (view, Self::vote_kind_tag(kind));
        if let Some(existing) = self.voted_by_view.get(&key) {
            if existing.block_hash != block_hash {
                return Err(ExposedOnceError::EquivocationRefused {
                    view,
                    kind,
                    existing_block_hash: existing.block_hash,
                    attempted_block_hash: block_hash,
                });
            }
        }

        // Cross-kind and finalized-block / skip-cert consistency in the same view:
        if kind == SimplexVoteKind::Skip {
            if let Some(existing) =
                self.voted_by_view
                    .get(&(view, Self::vote_kind_tag(SimplexVoteKind::Finalize)))
            {
                return Err(ExposedOnceError::EquivocationRefused {
                    view,
                    kind,
                    existing_block_hash: existing.block_hash,
                    attempted_block_hash: block_hash,
                });
            }
            if let Some(blk) = self.replayed_blocks.iter().find(|b| b.view == view) {
                return Err(ExposedOnceError::EquivocationRefused {
                    view,
                    kind,
                    existing_block_hash: blk.block_hash,
                    attempted_block_hash: block_hash,
                });
            }
        } else {
            if let Some(existing) =
                self.voted_by_view
                    .get(&(view, Self::vote_kind_tag(SimplexVoteKind::Skip)))
            {
                return Err(ExposedOnceError::EquivocationRefused {
                    view,
                    kind,
                    existing_block_hash: existing.block_hash,
                    attempted_block_hash: block_hash,
                });
            }
            if self.replayed_skip_certs.iter().any(|c| c.view == view) {
                return Err(ExposedOnceError::EquivocationRefused {
                    view,
                    kind,
                    existing_block_hash: [0u8; 32],
                    attempted_block_hash: block_hash,
                });
            }
            for other_kind in [
                SimplexVoteKind::Propose,
                SimplexVoteKind::Vote,
                SimplexVoteKind::Finalize,
            ] {
                if let Some(existing) =
                    self.voted_by_view
                        .get(&(view, Self::vote_kind_tag(other_kind)))
                {
                    if existing.block_hash != block_hash {
                        return Err(ExposedOnceError::EquivocationRefused {
                            view,
                            kind,
                            existing_block_hash: existing.block_hash,
                            attempted_block_hash: block_hash,
                        });
                    }
                }
            }
            if let Some(blk) = self.replayed_blocks.iter().find(|b| b.view == view) {
                if blk.block_hash != block_hash {
                    return Err(ExposedOnceError::EquivocationRefused {
                        view,
                        kind,
                        existing_block_hash: blk.block_hash,
                        attempted_block_hash: block_hash,
                    });
                }
            }
        }
        Ok(())
    }

    /// Check whether this validator can safely cast `(view, kind, block_hash)` without equivocating.
    pub fn check_can_vote(
        &self,
        view: u64,
        kind: SimplexVoteKind,
        block_hash: [u8; 32],
    ) -> Result<(), ExposedOnceError> {
        if !self.memory_up {
            return Err(ExposedOnceError::NodeDown);
        }
        self.check_can_vote_inner(view, kind, block_hash)
    }

    /// Append a `WalEntry` to the durable journal (`hstep .submit`), returning its `OutboxReceiptId`.
    pub fn append_entry(&mut self, entry: WalEntry) -> Result<OutboxReceiptId, ExposedOnceError> {
        if !self.memory_up {
            return Err(ExposedOnceError::NodeDown);
        }
        let pos = self.journal.len() as u64;
        self.apply_entry_to_volatile(pos, &entry)?;
        Self::append_raw_frame(&mut self.byte_log, &entry);
        self.journal.push(entry);
        Ok(OutboxReceiptId(pos))
    }

    /// Record a validator's vote in the WAL before network transmission, refusing any same-view equivocation.
    pub fn record_vote(&mut self, vote: SignedSimplexVote) -> Result<OutboxReceiptId, ExposedOnceError> {
        self.check_can_vote(vote.view, vote.kind, vote.block_hash)?;
        if let Some((idx, _)) = self.journal.iter().enumerate().find(|(_, e)| {
            matches!(
                e,
                WalEntry::VoteCast(v)
                    if v.voter_id == vote.voter_id
                        && v.view == vote.view
                        && v.kind == vote.kind
                        && v.block_hash == vote.block_hash
            )
        }) {
            return Ok(OutboxReceiptId(idx as u64));
        }
        self.append_entry(WalEntry::VoteCast(vote))
    }

    /// Submit a dispatch effect (`Obend.Run.Durable.JEvent.dispatch`) to the WAL.
    pub fn submit_dispatch(
        &mut self,
        turn: VaultTurn,
        token_id: Option<u64>,
    ) -> Result<OutboxReceiptId, ExposedOnceError> {
        self.append_entry(WalEntry::DispatchEffect { turn, token_id })
    }

    /// Expose a journaled dispatch effect at position `pos` (`Obend.Run.Durable.hstep (.expose pos)`).
    /// Succeeds at most once per `pos`, returning `Err(ExposedOnceError::AlreadyExposed(pos))` on any
    /// duplicate attempt (even across `simulate_crash()` + `recover_from_wal()`!).
    pub fn expose_effect(&mut self, pos: u64) -> Result<OutboxReceiptId, ExposedOnceError> {
        match self.journal.get(pos as usize) {
            Some(WalEntry::DispatchEffect { .. }) => {
                if self.outbox.contains(&pos) {
                    return Err(ExposedOnceError::AlreadyExposed(pos));
                }
                self.outbox.insert(pos);
                Self::append_raw_frame(&mut self.byte_log, &WalEntry::OutboxExposed { pos });
                Ok(OutboxReceiptId(pos))
            }
            _ => Err(ExposedOnceError::NotDispatch(pos)),
        }
    }

    /// Journal positions holding a `DispatchEffect` that have not yet been exposed (`Obend.Run.Durable.pending`).
    pub fn pending_effects(&self) -> Vec<u64> {
        self.journal
            .iter()
            .enumerate()
            .filter_map(|(idx, entry)| {
                let pos = idx as u64;
                if matches!(entry, WalEntry::DispatchEffect { .. }) && !self.outbox.contains(&pos) {
                    Some(pos)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Simulate a crash (`Obend.Run.Durable.hstep .crash`): wipes volatile in-memory state
    /// while preserving `journal`, `outbox`, and `byte_log` (`crash_keeps`).
    pub fn simulate_crash(&mut self) {
        self.memory_up = false;
        self.voted_by_view.clear();
        self.highest_voted_view = 0;
        self.replayed_blocks.clear();
        self.replayed_fast_path.clear();
        self.replayed_skip_certs.clear();
        self.replayed_epochs.clear();
        self.consumed_tokens.clear();
    }

    /// Replay the durable journal after one or more crashes (`Obend.Run.Durable.hstep .recover`),
    /// restoring all volatile state and highest voted views before rejoining the network.
    pub fn recover_from_wal(&mut self) -> Result<(), ExposedOnceError> {
        self.voted_by_view.clear();
        self.highest_voted_view = 0;
        self.replayed_blocks.clear();
        self.replayed_fast_path.clear();
        self.replayed_skip_certs.clear();
        self.replayed_epochs.clear();
        self.consumed_tokens.clear();

        let entries = self.journal.clone();
        for (idx, entry) in entries.iter().enumerate() {
            self.apply_entry_to_volatile(idx as u64, entry)?;
        }
        self.memory_up = true;
        Ok(())
    }

    /// Export the durable byte log for persistent storage or cold-start recovery.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.byte_log.clone()
    }

    /// Reconstruct a `DurableNodeWal` from a raw serialized byte log (`recover_from_wal`).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ExposedOnceError> {
        let mut wal = Self::new();
        let mut offset = 0usize;
        while offset < bytes.len() {
            if offset + 40 > bytes.len() {
                return Err(ExposedOnceError::CorruptWal(
                    "truncated WAL frame header".to_string(),
                ));
            }
            if &bytes[offset..offset + 4] != &Self::FRAME_MAGIC {
                return Err(ExposedOnceError::CorruptWal("invalid WAL magic".to_string()));
            }
            let mut len_bytes = [0u8; 4];
            len_bytes.copy_from_slice(&bytes[offset + 4..offset + 8]);
            let payload_len = u32::from_be_bytes(len_bytes) as usize;
            let mut expected_digest = [0u8; 32];
            expected_digest.copy_from_slice(&bytes[offset + 8..offset + 40]);
            if offset + 40 + payload_len > bytes.len() {
                return Err(ExposedOnceError::CorruptWal(
                    "truncated WAL frame payload".to_string(),
                ));
            }
            let payload = &bytes[offset + 40..offset + 40 + payload_len];
            let actual_digest =
                cshake256_domain(b"obend.durable.wal.frame", &len_bytes, payload);
            if actual_digest != expected_digest {
                return Err(ExposedOnceError::CorruptWal(
                    "WAL frame cSHAKE256 digest mismatch".to_string(),
                ));
            }
            let entry: WalEntry = serde_json::from_slice(payload)
                .map_err(|e| ExposedOnceError::CorruptWal(e.to_string()))?;
            match &entry {
                WalEntry::OutboxExposed { pos } => {
                    if !matches!(
                        wal.journal.get(*pos as usize),
                        Some(WalEntry::DispatchEffect { .. })
                    ) {
                        return Err(ExposedOnceError::NotDispatch(*pos));
                    }
                    if !wal.outbox.insert(*pos) {
                        return Err(ExposedOnceError::AlreadyExposed(*pos));
                    }
                    Self::append_raw_frame(&mut wal.byte_log, &entry);
                }
                _ => {
                    wal.append_entry(entry)?;
                }
            }
            offset += 40 + payload_len;
        }
        Ok(wal)
    }

    /// Reconstruct a `DurableNodeWal` from a byte log that may have an incomplete trailing frame
    /// due to a mid-append power failure, returning `(recovered_wal, truncated_tail_bytes)`.
    /// Rejects any mid-log corruption, invalid frame magic, or digest mismatch.
    pub fn recover_from_truncated_bytes(bytes: &[u8]) -> Result<(Self, usize), ExposedOnceError> {
        let mut offset = 0usize;
        while offset < bytes.len() {
            if offset + 40 > bytes.len() {
                let rem = &bytes[offset..];
                if (rem.len() <= 4 && Self::FRAME_MAGIC.starts_with(rem))
                    || (rem.len() > 4 && rem.starts_with(&Self::FRAME_MAGIC))
                {
                    break;
                }
                return Err(ExposedOnceError::CorruptWal(
                    "corrupt WAL frame header".to_string(),
                ));
            }
            if &bytes[offset..offset + 4] != &Self::FRAME_MAGIC {
                return Err(ExposedOnceError::CorruptWal("invalid WAL magic".to_string()));
            }
            let mut len_bytes = [0u8; 4];
            len_bytes.copy_from_slice(&bytes[offset + 4..offset + 8]);
            let payload_len = u32::from_be_bytes(len_bytes) as usize;
            if offset + 40 + payload_len > bytes.len() {
                break;
            }
            offset += 40 + payload_len;
        }
        let wal = Self::from_bytes(&bytes[..offset])?;
        Ok((wal, bytes.len() - offset))
    }
}

/// Internal state of a `NetworkedValidatorNode`.
pub struct ValidatorNodeState {
    pub node_id: usize,
    pub total_parties: usize,
    pub fault_tolerance: usize,
    pub quorum_size: usize,
    pub peer_public_keys: Vec<[u8; 32]>,
    pub peer_tcp_addrs: Vec<SocketAddr>,
    pub peer_udp_addrs: Vec<SocketAddr>,
    pub transport: TransportProtocol,

    pub current_view: u64,
    pub committed_height: u64,
    pub committed_tip_hash: [u8; 32],

    pub genesis_cells: Vec<VaultCellRecord>,
    pub vault_cells: Vec<VaultCellRecord>,
    pub current_state_root: [u8; 32],

    /// Proposals seen indexed by `(view, block_hash)`.
    pub proposals: BTreeMap<(u64, [u8; 32]), (PropCert, BlockPayload)>,
    /// All signed votes seen for equivocation detection and quorum assembly.
    pub seen_votes: Vec<SignedSimplexVote>,
    /// Views for which this node has already broadcast a `FinCert`.
    pub broadcast_fin_views: BTreeSet<u64>,
    /// Views for which this node has already broadcast a `SkipCert`.
    pub broadcast_skip_views: BTreeSet<u64>,

    /// Finalized blocks ordered by height.
    pub finalized_blocks: Vec<FinalizedBlockRecord>,
    /// Collected `SkipCert`s.
    pub skip_certs: Vec<SkipCert>,
    /// Detected Byzantine equivocation `SlashingReceipt`s.
    pub slashing_receipts: Vec<SlashingReceipt>,
    /// Slashed Byzantine validator IDs.
    pub slashed_validators: BTreeSet<usize>,

    /// Active in-flight turns on Tier 1 fast-path.
    pub inflight_turns: BTreeMap<[u8; 32], VaultTurn>,
    /// Collected Tier 1 fast-path acks per `turn_id`.
    pub fast_path_acks: BTreeMap<[u8; 32], Vec<SignedFastPathAck>>,
    /// Finalized Tier 1 fast-path certificates.
    pub fast_path_certs: Vec<FastPathCert>,
    /// Tier 1 fast-path turns committed since the previous finalized block height.
    pub pending_fast_path_turns: Vec<VaultTurn>,

    /// Finality tier tracking per `turn_id` (`FinalityGate`).
    pub turn_finality: BTreeMap<[u8; 32], FinalityTier>,
    /// Tier 3 collapsed epoch receipts.
    pub epoch_receipts: Vec<CollapsedEpochReceipt>,

    /// Durable Write-Ahead Log (`Obend.Run.Durable`).
    pub wal: DurableNodeWal,

    /// Wire metrics.
    pub wire_frames_received: usize,
    pub wire_frames_sent: usize,
    pub rejected_wire_frames: usize,
}

impl ValidatorNodeState {
    pub fn recompute_state_root(&mut self) -> [u8; 32] {
        let leaves: Vec<[u8; 32]> = self.vault_cells.iter().map(|c| c.leaf_hash()).collect();
        self.current_state_root = merkle_root_from_leaves(&leaves);
        self.current_state_root
    }

    pub fn promote_turn_tier(&mut self, turn_id: [u8; 32], target: FinalityTier) {
        let entry = self
            .turn_finality
            .entry(turn_id)
            .or_insert(FinalityTier::Speculative);
        if entry.can_promote_to(target) {
            *entry = target;
        }
    }

    /// Simulate a volatile memory crash on this validator (`Obend.Run.Durable.hstep .crash`),
    /// wiping volatile consensus & vault state while preserving `self.wal` (`journal` and `outbox`).
    pub fn simulate_crash(&mut self) {
        self.wal.simulate_crash();
        self.current_view = 1;
        self.committed_height = 0;
        self.committed_tip_hash = [0u8; 32];
        self.vault_cells = self.genesis_cells.clone();
        self.recompute_state_root();
        self.proposals.clear();
        self.seen_votes.clear();
        self.broadcast_fin_views.clear();
        self.broadcast_skip_views.clear();
        self.finalized_blocks.clear();
        self.skip_certs.clear();
        self.inflight_turns.clear();
        self.fast_path_acks.clear();
        self.fast_path_certs.clear();
        self.pending_fast_path_turns.clear();
        self.turn_finality.clear();
        self.epoch_receipts.clear();
    }

    /// Recover volatile validator state by replaying `self.wal` (`Obend.Run.Durable.hstep .recover`),
    /// restoring finalized blocks, vault cells, Merkle state root, committed height/tip, skip certs,
    /// epoch receipts, and previously cast votes so this validator never equivocates after a crash!
    pub fn recover_from_wal(&mut self) -> Result<(), ExposedOnceError> {
        self.wal.recover_from_wal()?;
        self.vault_cells = self.genesis_cells.clone();
        self.current_view = 1;
        self.committed_height = 0;
        self.committed_tip_hash = [0u8; 32];
        self.proposals.clear();
        self.seen_votes.clear();
        self.broadcast_fin_views.clear();
        self.broadcast_skip_views.clear();
        self.finalized_blocks.clear();
        self.skip_certs.clear();
        self.inflight_turns.clear();
        self.fast_path_acks.clear();
        self.fast_path_certs.clear();
        self.pending_fast_path_turns.clear();
        self.turn_finality.clear();
        self.epoch_receipts.clear();

        let entries = self.wal.journal.clone();
        for entry in entries {
            match entry {
                WalEntry::VoteCast(vote) => {
                    if !self.seen_votes.iter().any(|v| {
                        v.voter_id == vote.voter_id
                            && v.view == vote.view
                            && v.kind == vote.kind
                            && v.block_hash == vote.block_hash
                    }) {
                        self.seen_votes.push(vote.clone());
                    }
                    if vote.view > self.current_view {
                        self.current_view = vote.view;
                    }
                }
                WalEntry::FastPathCommitted(cert) => {
                    if !self
                        .fast_path_certs
                        .iter()
                        .any(|c| c.turn.turn_id == cert.turn.turn_id)
                    {
                        cert.turn.apply_to_cells(&mut self.vault_cells);
                        self.recompute_state_root();
                        self.pending_fast_path_turns.push(cert.turn.clone());
                        self.promote_turn_tier(cert.turn.turn_id, FinalityTier::AttestedFastPath);
                        self.fast_path_certs.push(cert);
                    }
                }
                WalEntry::BlockFinalized(blk) => {
                    if !self.finalized_blocks.iter().any(|b| b.height == blk.height) {
                        for fp_turn in &blk.pre_block_fast_path_turns {
                            if !self
                                .fast_path_certs
                                .iter()
                                .any(|c| c.turn.turn_id == fp_turn.turn_id)
                            {
                                fp_turn.apply_to_cells(&mut self.vault_cells);
                            }
                            self.promote_turn_tier(fp_turn.turn_id, FinalityTier::AttestedFastPath);
                        }
                        self.pending_fast_path_turns.clear();
                        Fold::apply_block_to_cells(
                            &mut self.vault_cells,
                            &blk.payload,
                            blk.clearing_cert.as_ref(),
                        );
                        for t in &blk.payload.turns {
                            self.promote_turn_tier(t.turn_id, FinalityTier::QuorumFinal);
                        }
                        self.recompute_state_root();
                        self.committed_height = blk.height;
                        self.committed_tip_hash = blk.block_hash;
                        if self.current_view <= blk.view {
                            self.current_view = blk.view + 1;
                        }
                        self.broadcast_fin_views.insert(blk.view);
                        self.finalized_blocks.push(blk);
                    }
                }
                WalEntry::SkipCertified(sc) => {
                    if !self.skip_certs.iter().any(|c| c.view == sc.view) {
                        self.skip_certs.push(sc.clone());
                    }
                    if self.current_view <= sc.view {
                        self.current_view = sc.view + 1;
                    }
                    self.broadcast_skip_views.insert(sc.view);
                }
                WalEntry::EpochCollapsed(receipt) => {
                    let mut promoted_turns = Vec::new();
                    for blk in &mut self.finalized_blocks {
                        if blk.height >= receipt.start_height && blk.height <= receipt.end_height {
                            blk.tier = FinalityTier::Collapsed;
                            for t in &blk.pre_block_fast_path_turns {
                                promoted_turns.push(t.turn_id);
                            }
                            for t in &blk.payload.turns {
                                promoted_turns.push(t.turn_id);
                            }
                        }
                    }
                    for tid in promoted_turns {
                        self.promote_turn_tier(tid, FinalityTier::Collapsed);
                    }
                    if !self
                        .epoch_receipts
                        .iter()
                        .any(|r| r.epoch_id == receipt.epoch_id)
                    {
                        self.epoch_receipts.push(receipt);
                    }
                }
                WalEntry::DispatchEffect { .. } | WalEntry::OutboxExposed { .. } => {}
            }
        }
        Ok(())
    }
}

/// A live validator daemon listening on real OS TCP and UDP loopback sockets (`127.0.0.1:0`).
pub struct NetworkedValidatorNode {
    pub node_id: usize,
    pub keypair: ValidatorKeypair,
    pub tcp_addr: SocketAddr,
    pub udp_addr: SocketAddr,
    pub state: Arc<Mutex<ValidatorNodeState>>,
    running: Arc<AtomicBool>,
    tcp_thread: Option<JoinHandle<()>>,
    udp_thread: Option<JoinHandle<()>>,
}

impl NetworkedValidatorNode {
    /// Spawn a new `NetworkedValidatorNode` bound to `127.0.0.1:0` for both TCP and UDP.
    pub fn spawn(
        node_id: usize,
        total_parties: usize,
        fault_tolerance: usize,
        keypair: ValidatorKeypair,
        peer_public_keys: Vec<[u8; 32]>,
        initial_cells: Vec<VaultCellRecord>,
        transport: TransportProtocol,
    ) -> Result<Self, NodeError> {
        let tcp_listener = TcpListener::bind("127.0.0.1:0")?;
        let tcp_addr = tcp_listener.local_addr()?;
        tcp_listener.set_nonblocking(true)?;

        let udp_socket = UdpSocket::bind("127.0.0.1:0")?;
        let udp_addr = udp_socket.local_addr()?;
        udp_socket.set_read_timeout(Some(Duration::from_millis(5)))?;

        let leaves: Vec<[u8; 32]> = initial_cells.iter().map(|c| c.leaf_hash()).collect();
        let initial_root = merkle_root_from_leaves(&leaves);
        let quorum_size = 2 * fault_tolerance + 1;

        let state = Arc::new(Mutex::new(ValidatorNodeState {
            node_id,
            total_parties,
            fault_tolerance,
            quorum_size,
            peer_public_keys,
            peer_tcp_addrs: Vec::new(),
            peer_udp_addrs: Vec::new(),
            transport,
            current_view: 1,
            committed_height: 0,
            committed_tip_hash: [0u8; 32],
            genesis_cells: initial_cells.clone(),
            vault_cells: initial_cells,
            current_state_root: initial_root,
            proposals: BTreeMap::new(),
            seen_votes: Vec::new(),
            broadcast_fin_views: BTreeSet::new(),
            broadcast_skip_views: BTreeSet::new(),
            finalized_blocks: Vec::new(),
            skip_certs: Vec::new(),
            slashing_receipts: Vec::new(),
            slashed_validators: BTreeSet::new(),
            inflight_turns: BTreeMap::new(),
            fast_path_acks: BTreeMap::new(),
            fast_path_certs: Vec::new(),
            pending_fast_path_turns: Vec::new(),
            turn_finality: BTreeMap::new(),
            epoch_receipts: Vec::new(),
            wal: DurableNodeWal::new(),
            wire_frames_received: 0,
            wire_frames_sent: 0,
            rejected_wire_frames: 0,
        }));

        let running = Arc::new(AtomicBool::new(true));

        // Spawn TCP listener thread
        let state_tcp = Arc::clone(&state);
        let running_tcp = Arc::clone(&running);
        let kp_tcp = keypair.clone();
        let tcp_thread = thread::Builder::new()
            .name(format!("obend-validator-tcp-{node_id}"))
            .spawn(move || {
                while running_tcp.load(Ordering::Acquire) {
                    match tcp_listener.accept() {
                        Ok((mut stream, _peer)) => {
                            let _ = stream.set_nonblocking(false);
                            let _ = stream.set_read_timeout(Some(Duration::from_millis(500)));
                            let mut len_buf = [0u8; 4];
                            if stream.read_exact(&mut len_buf).is_ok() {
                                let len = u32::from_be_bytes(len_buf) as usize;
                                if len > 0 && len <= 4 * 1024 * 1024 {
                                    let mut payload_buf = vec![0u8; len];
                                    if stream.read_exact(&mut payload_buf).is_ok() {
                                        Self::on_raw_wire_bytes(&state_tcp, &kp_tcp, &payload_buf);
                                    }
                                }
                            }
                        }
                        Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                            thread::sleep(Duration::from_millis(1));
                        }
                        Err(_) => {
                            thread::sleep(Duration::from_millis(1));
                        }
                    }
                }
            })?;

        // Spawn UDP listener thread
        let state_udp = Arc::clone(&state);
        let running_udp = Arc::clone(&running);
        let kp_udp = keypair.clone();
        let udp_thread = thread::Builder::new()
            .name(format!("obend-validator-udp-{node_id}"))
            .spawn(move || {
                let mut buf = vec![0u8; 65507];
                while running_udp.load(Ordering::Acquire) {
                    if let Ok((n, _peer)) = udp_socket.recv_from(&mut buf) {
                        if n > 0 {
                            Self::on_raw_wire_bytes(&state_udp, &kp_udp, &buf[..n]);
                        }
                    }
                }
            })?;

        Ok(Self {
            node_id,
            keypair,
            tcp_addr,
            udp_addr,
            state,
            running,
            tcp_thread: Some(tcp_thread),
            udp_thread: Some(udp_thread),
        })
    }

    /// Connect peer socket addresses once all nodes in the cluster have bound their ephemeral ports.
    pub fn set_peer_addresses(&self, tcp_addrs: Vec<SocketAddr>, udp_addrs: Vec<SocketAddr>) {
        let mut st = self.state.lock().unwrap();
        st.peer_tcp_addrs = tcp_addrs;
        st.peer_udp_addrs = udp_addrs;
    }

    /// Broadcast a `ConsensusNetMessage` from this node to all peers over the configured socket transport.
    pub fn broadcast(&self, msg: ConsensusNetMessage) -> Result<(), NodeError> {
        let env = WireEnvelope::create(&self.keypair, msg);
        let (transport, tcp_addrs, udp_addrs) = {
            let mut st = self.state.lock().unwrap();
            st.wire_frames_sent += st.peer_tcp_addrs.len();
            (
                st.transport,
                st.peer_tcp_addrs.clone(),
                st.peer_udp_addrs.clone(),
            )
        };
        Self::dispatch_envelope_to_peers(transport, &tcp_addrs, &udp_addrs, &env)
    }

    fn dispatch_envelope_to_peers(
        transport: TransportProtocol,
        tcp_addrs: &[SocketAddr],
        udp_addrs: &[SocketAddr],
        env: &WireEnvelope,
    ) -> Result<(), NodeError> {
        let bytes = serde_json::to_vec(env)?;
        match transport {
            TransportProtocol::Tcp => {
                let len_bytes = (bytes.len() as u32).to_be_bytes();
                for &addr in tcp_addrs {
                    if let Ok(mut stream) =
                        TcpStream::connect_timeout(&addr, Duration::from_millis(500))
                    {
                        let _ = stream.set_write_timeout(Some(Duration::from_millis(500)));
                        let _ = stream.write_all(&len_bytes);
                        let _ = stream.write_all(&bytes);
                        let _ = stream.flush();
                    }
                }
            }
            TransportProtocol::Udp => {
                if let Ok(sock) = UdpSocket::bind("127.0.0.1:0") {
                    for &addr in udp_addrs {
                        let _ = sock.send_to(&bytes, addr);
                    }
                }
            }
        }
        Ok(())
    }

    fn on_raw_wire_bytes(
        state: &Arc<Mutex<ValidatorNodeState>>,
        keypair: &ValidatorKeypair,
        raw: &[u8],
    ) {
        let Ok(env) = serde_json::from_slice::<WireEnvelope>(raw) else {
            let mut st = state.lock().unwrap();
            st.rejected_wire_frames += 1;
            return;
        };

        let (outbound, transport, tcp_addrs, udp_addrs) = {
            let mut st = state.lock().unwrap();
            if !env.verify(&st.peer_public_keys) {
                st.rejected_wire_frames += 1;
                return;
            }
            st.wire_frames_received += 1;
            let responses = Self::process_consensus_message(&mut st, keypair, env.payload);
            st.wire_frames_sent += responses.len() * st.peer_tcp_addrs.len();
            (
                responses,
                st.transport,
                st.peer_tcp_addrs.clone(),
                st.peer_udp_addrs.clone(),
            )
        };

        // Perform network I/O strictly outside the state Mutex lock
        for msg in outbound {
            let resp_env = WireEnvelope::create(keypair, msg);
            let _ = Self::dispatch_envelope_to_peers(transport, &tcp_addrs, &udp_addrs, &resp_env);
        }
    }

    fn process_consensus_message(
        st: &mut ValidatorNodeState,
        keypair: &ValidatorKeypair,
        msg: ConsensusNetMessage,
    ) -> Vec<ConsensusNetMessage> {
        let mut outbound = Vec::new();
        if !st.wal.memory_up {
            return outbound;
        }

        match msg {
            ConsensusNetMessage::Propose(prop_cert, payload) => {
                let Some(expected_pk) = st.peer_public_keys.get(prop_cert.leader_vote.voter_id) else {
                    st.rejected_wire_frames += 1;
                    return outbound;
                };
                if &prop_cert.leader_vote.public_key != expected_pk
                    || !prop_cert.leader_vote.verify_signature()
                {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                // Inspect the authenticated leader's proposal vote for potential equivocation
                if let Some(slash) = Self::record_vote_and_check_equivocation(st, &prop_cert.leader_vote) {
                    outbound.push(ConsensusNetMessage::Slashing(slash));
                    return outbound;
                }
                if st.slashed_validators.contains(&prop_cert.leader_vote.voter_id) {
                    return outbound;
                }
                if !prop_cert.verify(st.total_parties)
                    || prop_cert.view != payload.view
                    || prop_cert.height != payload.height
                    || prop_cert.turn_payload != payload.to_bytes()
                {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                for turn in &payload.turns {
                    st.promote_turn_tier(turn.turn_id, FinalityTier::Speculative);
                }
                st.proposals.insert(
                    (prop_cert.view, prop_cert.block_hash),
                    (prop_cert.clone(), payload),
                );

                // If this node is not slashed, cast a Finalize vote for this valid proposal
                // only if WAL confirms no conflicting vote was cast in `prop_cert.view`.
                if !st.slashed_validators.contains(&st.node_id) {
                    let already_voted_in_view = st.seen_votes.iter().any(|v| {
                        v.voter_id == st.node_id
                            && v.view == prop_cert.view
                            && v.kind == SimplexVoteKind::Finalize
                    });
                    if !already_voted_in_view
                        && st
                            .wal
                            .check_can_vote(
                                prop_cert.view,
                                SimplexVoteKind::Finalize,
                                prop_cert.block_hash,
                            )
                            .is_ok()
                    {
                        let fin_vote = SignedSimplexVote::new(
                            keypair,
                            prop_cert.view,
                            SimplexVoteKind::Finalize,
                            prop_cert.block_hash,
                        );
                        let _ = st.wal.record_vote(fin_vote.clone());
                        let _ = Self::record_vote_and_check_equivocation(st, &fin_vote);
                        outbound.push(ConsensusNetMessage::Vote(fin_vote));
                    }
                }

                // Check if quorum is already satisfied
                if let Some(fin_msg) =
                    Self::try_assemble_fincert_and_finalize(st, prop_cert.view, prop_cert.block_hash)
                {
                    outbound.push(fin_msg);
                }
            }

            ConsensusNetMessage::Vote(vote) => {
                if !vote.verify_signature() {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                let Some(expected_pk) = st.peer_public_keys.get(vote.voter_id) else {
                    st.rejected_wire_frames += 1;
                    return outbound;
                };
                if &vote.public_key != expected_pk {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }

                // 1. Check for accountable Byzantine equivocation
                if let Some(slash) = Self::record_vote_and_check_equivocation(st, &vote) {
                    outbound.push(ConsensusNetMessage::Slashing(slash));
                    return outbound;
                }

                if st.slashed_validators.contains(&vote.voter_id) {
                    return outbound;
                }

                match vote.kind {
                    SimplexVoteKind::Finalize => {
                        if let Some(fin_msg) =
                            Self::try_assemble_fincert_and_finalize(st, vote.view, vote.block_hash)
                        {
                            outbound.push(fin_msg);
                        }
                    }
                    SimplexVoteKind::Skip => {
                        if let Some(skip_msg) = Self::try_assemble_skipcert(st, vote.view) {
                            outbound.push(skip_msg);
                        }
                    }
                    _ => {}
                }
            }

            ConsensusNetMessage::SkipCertificate(skip_cert) => {
                let valid_peer_votes = skip_cert
                    .votes
                    .iter()
                    .filter(|v| {
                        st.peer_public_keys.get(v.voter_id) == Some(&v.public_key)
                            && !st.slashed_validators.contains(&v.voter_id)
                    })
                    .count();
                if !skip_cert.verify(st.quorum_size) || valid_peer_votes < st.quorum_size {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                if !st.skip_certs.iter().any(|c| c.view == skip_cert.view) {
                    let _ = st.wal.append_entry(WalEntry::SkipCertified(skip_cert.clone()));
                    st.skip_certs.push(skip_cert.clone());
                }
                if st.current_view <= skip_cert.view {
                    st.current_view = skip_cert.view + 1;
                }
            }

            ConsensusNetMessage::FinalizationCertificate(fin_cert, payload) => {
                let valid_peer_votes = fin_cert
                    .votes
                    .iter()
                    .filter(|v| {
                        st.peer_public_keys.get(v.voter_id) == Some(&v.public_key)
                            && !st.slashed_validators.contains(&v.voter_id)
                    })
                    .count();
                if !fin_cert.verify(st.quorum_size)
                    || valid_peer_votes < st.quorum_size
                    || payload.view != fin_cert.view
                {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                let stored_prop = st
                    .proposals
                    .get(&(fin_cert.view, fin_cert.block_hash))
                    .map(|(p, _)| p.clone());
                let parent_hash = stored_prop
                    .as_ref()
                    .map(|p| p.parent_hash)
                    .unwrap_or(st.committed_tip_hash);
                let expected_hash = cshake256_domain(
                    b"obend.simplex.block",
                    &[
                        &fin_cert.view.to_be_bytes()[..],
                        &payload.height.to_be_bytes()[..],
                        &parent_hash[..],
                    ]
                    .concat(),
                    &payload.to_bytes(),
                );
                if fin_cert.block_hash != expected_hash {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                if !st.finalized_blocks.iter().any(|b| b.height == payload.height) {
                    Self::apply_finalized_block(st, stored_prop, fin_cert, payload);
                }
            }

            ConsensusNetMessage::Slashing(receipt) => {
                let Some(expected_pk) = st.peer_public_keys.get(receipt.offender_id) else {
                    st.rejected_wire_frames += 1;
                    return outbound;
                };
                if !receipt.verify() || &receipt.vote_a.public_key != expected_pk {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                st.slashed_validators.insert(receipt.offender_id);
                st.proposals
                    .retain(|_, (p, _)| p.leader_vote.voter_id != receipt.offender_id);
                if !st
                    .slashing_receipts
                    .iter()
                    .any(|r| r.offender_id == receipt.offender_id && r.view == receipt.view)
                {
                    st.slashing_receipts.push(receipt.clone());
                    outbound.push(ConsensusNetMessage::Slashing(receipt));
                }
            }

            ConsensusNetMessage::FastPathPropose(turn) => {
                // Verify turn is disjoint from all active in-flight turns on this validator
                let disjoint = st
                    .inflight_turns
                    .values()
                    .all(|other| other.turn_id == turn.turn_id || disjoint_turns_commute(&turn, other));
                if disjoint && !turn.has_duplicate_write_slots() {
                    st.promote_turn_tier(turn.turn_id, FinalityTier::Speculative);
                    st.inflight_turns.insert(turn.turn_id, turn.clone());
                    if !st.slashed_validators.contains(&st.node_id) {
                        let ack = SignedFastPathAck::new(keypair, &turn);
                        Self::record_fast_path_ack(st, ack.clone());
                        outbound.push(ConsensusNetMessage::FastPathAck(ack));
                        if let Some(commit_msg) = Self::try_finalize_fast_path(st, &turn.turn_id) {
                            outbound.push(commit_msg);
                        }
                    }
                }
            }

            ConsensusNetMessage::FastPathAck(ack) => {
                let Some(expected_pk) = st.peer_public_keys.get(ack.voter_id) else {
                    st.rejected_wire_frames += 1;
                    return outbound;
                };
                if !ack.verify() || &ack.public_key != expected_pk {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                if !st.slashed_validators.contains(&ack.voter_id) {
                    let turn_id = ack.turn_id;
                    Self::record_fast_path_ack(st, ack);
                    if let Some(commit_msg) = Self::try_finalize_fast_path(st, &turn_id) {
                        outbound.push(commit_msg);
                    }
                }
            }

            ConsensusNetMessage::FastPathCommit(cert) => {
                let valid_peer_acks = cert
                    .acks
                    .iter()
                    .filter(|a| {
                        st.peer_public_keys.get(a.voter_id) == Some(&a.public_key)
                            && !st.slashed_validators.contains(&a.voter_id)
                    })
                    .count();
                if !cert.verify(st.quorum_size) || valid_peer_acks < st.quorum_size {
                    st.rejected_wire_frames += 1;
                    return outbound;
                }
                if !st
                    .fast_path_certs
                    .iter()
                    .any(|c| c.turn.turn_id == cert.turn.turn_id)
                {
                    cert.turn.apply_to_cells(&mut st.vault_cells);
                    st.recompute_state_root();
                    st.inflight_turns.remove(&cert.turn.turn_id);
                    st.pending_fast_path_turns.push(cert.turn.clone());
                    st.promote_turn_tier(cert.turn.turn_id, FinalityTier::AttestedFastPath);
                    let _ = st.wal.append_entry(WalEntry::FastPathCommitted(cert.clone()));
                    st.fast_path_certs.push(cert);
                }
            }
        }

        outbound
    }

    fn record_vote_and_check_equivocation(
        st: &mut ValidatorNodeState,
        vote: &SignedSimplexVote,
    ) -> Option<SlashingReceipt> {
        if let Some(existing) = st.seen_votes.iter().find(|v| {
            v.voter_id == vote.voter_id
                && v.view == vote.view
                && v.kind == vote.kind
                && v.block_hash != vote.block_hash
        }) {
            let receipt = SlashingReceipt {
                offender_id: vote.voter_id,
                view: vote.view,
                vote_a: existing.clone(),
                vote_b: vote.clone(),
            };
            if receipt.verify() {
                st.slashed_validators.insert(vote.voter_id);
                st.proposals
                    .retain(|_, (p, _)| p.leader_vote.voter_id != vote.voter_id);
                if !st
                    .slashing_receipts
                    .iter()
                    .any(|r| r.offender_id == receipt.offender_id && r.view == receipt.view)
                {
                    st.slashing_receipts.push(receipt.clone());
                }
                return Some(receipt);
            }
        }

        if vote.voter_id == st.node_id {
            let _ = st.wal.record_vote(vote.clone());
        }

        if !st.seen_votes.iter().any(|v| {
            v.voter_id == vote.voter_id
                && v.view == vote.view
                && v.kind == vote.kind
                && v.block_hash == vote.block_hash
        }) {
            st.seen_votes.push(vote.clone());
        }
        None
    }

    fn try_assemble_skipcert(
        st: &mut ValidatorNodeState,
        view: u64,
    ) -> Option<ConsensusNetMessage> {
        if st.broadcast_skip_views.contains(&view) {
            return None;
        }
        let mut skip_votes = Vec::new();
        let mut voters = BTreeSet::new();
        for v in &st.seen_votes {
            if v.view == view
                && v.kind == SimplexVoteKind::Skip
                && v.block_hash == [0u8; 32]
                && !st.slashed_validators.contains(&v.voter_id)
                && voters.insert(v.voter_id)
            {
                skip_votes.push(v.clone());
            }
        }
        if skip_votes.len() >= st.quorum_size {
            let cert = SkipCert {
                view,
                votes: skip_votes,
            };
            if cert.verify(st.quorum_size) {
                if !st.skip_certs.iter().any(|c| c.view == view) {
                    let _ = st.wal.append_entry(WalEntry::SkipCertified(cert.clone()));
                    st.skip_certs.push(cert.clone());
                }
                if st.current_view <= view {
                    st.current_view = view + 1;
                }
                if st.broadcast_skip_views.insert(view) {
                    return Some(ConsensusNetMessage::SkipCertificate(cert));
                }
            }
        }
        None
    }

    fn try_assemble_fincert_and_finalize(
        st: &mut ValidatorNodeState,
        view: u64,
        block_hash: [u8; 32],
    ) -> Option<ConsensusNetMessage> {
        if st.broadcast_fin_views.contains(&view) {
            return None;
        }
        let Some((prop_cert, payload)) = st.proposals.get(&(view, block_hash)).cloned() else {
            return None;
        };
        if st.slashed_validators.contains(&prop_cert.leader_vote.voter_id) {
            return None;
        }

        let mut fin_votes = Vec::new();
        let mut voters = BTreeSet::new();
        for v in &st.seen_votes {
            if v.view == view
                && v.kind == SimplexVoteKind::Finalize
                && v.block_hash == block_hash
                && !st.slashed_validators.contains(&v.voter_id)
                && voters.insert(v.voter_id)
            {
                fin_votes.push(v.clone());
            }
        }

        if fin_votes.len() >= st.quorum_size {
            let fin_cert = FinCert {
                view,
                block_hash,
                votes: fin_votes,
            };
            if fin_cert.verify(st.quorum_size) {
                Self::apply_finalized_block(st, Some(prop_cert), fin_cert.clone(), payload.clone());
                if st.broadcast_fin_views.insert(view) {
                    return Some(ConsensusNetMessage::FinalizationCertificate(
                        fin_cert, payload,
                    ));
                }
            }
        }
        None
    }

    fn apply_finalized_block(
        st: &mut ValidatorNodeState,
        prop_cert: Option<PropCert>,
        fin_cert: FinCert,
        payload: BlockPayload,
    ) {
        if st
            .finalized_blocks
            .iter()
            .any(|b| b.height == payload.height)
        {
            return;
        }

        let pre_block_fast_path_turns: Vec<VaultTurn> =
            st.pending_fast_path_turns.drain(..).collect();
        let pre_state_root = st.recompute_state_root();

        // Automatically solve `drex-clearing@1` batch if limit orders are present
        let mut clearing_cert = None;
        let mut clearing_kernel_verified = true;
        if !payload.drex_orders.is_empty() {
            if let Some(cert) = solve_drex_batch(
                &payload.drex_currency,
                &payload.drex_goods,
                payload.drex_epsilon,
                &payload.drex_orders,
            ) {
                let verified = {
                    let _guard = FFI_KERNEL_LOCK.lock().unwrap();
                    ObendSession::new()
                        .and_then(|mut s| cert.verify_with_kernel(&payload.drex_orders, &mut s))
                        .unwrap_or(false)
                };
                clearing_kernel_verified = verified;
                if verified {
                    clearing_cert = Some(cert);
                }
            } else {
                clearing_kernel_verified = false;
            }
        }

        // Apply turns & verified clearing digest to VaultCellRecord state
        Fold::apply_block_to_cells(&mut st.vault_cells, &payload, clearing_cert.as_ref());
        for turn in &payload.turns {
            st.inflight_turns.remove(&turn.turn_id);
            st.promote_turn_tier(turn.turn_id, FinalityTier::QuorumFinal);
        }

        let post_state_root = st.recompute_state_root();
        let multiproof = BlindedVaultMultiProof::generate(&st.vault_cells, &[IpcAuth::Read]);
        let _ = {
            let _guard = FFI_KERNEL_LOCK.lock().unwrap();
            ObendSession::new().and_then(|mut s| multiproof.verify_via_ffi(&mut s))
        };

        let parent_hash = prop_cert
            .as_ref()
            .map(|p| p.parent_hash)
            .unwrap_or(st.committed_tip_hash);

        st.committed_height = payload.height;
        st.committed_tip_hash = fin_cert.block_hash;
        if st.current_view <= payload.view {
            st.current_view = payload.view + 1;
        }

        let rec = FinalizedBlockRecord {
            height: payload.height,
            view: payload.view,
            block_hash: fin_cert.block_hash,
            parent_hash,
            prop_cert,
            fin_cert,
            payload,
            pre_block_fast_path_turns,
            clearing_cert,
            clearing_kernel_verified,
            pre_state_root,
            post_state_root,
            multiproof,
            tier: FinalityTier::QuorumFinal,
        };
        let _ = st.wal.append_entry(WalEntry::BlockFinalized(rec.clone()));
        st.finalized_blocks.push(rec);
    }

    fn record_fast_path_ack(st: &mut ValidatorNodeState, ack: SignedFastPathAck) {
        let list = st.fast_path_acks.entry(ack.turn_id).or_default();
        if !list.iter().any(|a| a.voter_id == ack.voter_id) {
            list.push(ack);
        }
    }

    fn try_finalize_fast_path(
        st: &mut ValidatorNodeState,
        turn_id: &[u8; 32],
    ) -> Option<ConsensusNetMessage> {
        if st
            .fast_path_certs
            .iter()
            .any(|c| &c.turn.turn_id == turn_id)
        {
            return None;
        }
        let turn = st.inflight_turns.get(turn_id)?.clone();
        let acks = st.fast_path_acks.get(turn_id)?.clone();
        let valid_acks: Vec<SignedFastPathAck> = acks
            .into_iter()
            .filter(|a| {
                st.peer_public_keys.get(a.voter_id) == Some(&a.public_key)
                    && !st.slashed_validators.contains(&a.voter_id)
                    && a.verify()
            })
            .collect();

        if valid_acks.len() >= st.quorum_size {
            turn.apply_to_cells(&mut st.vault_cells);
            let post_state_root = st.recompute_state_root();
            st.inflight_turns.remove(turn_id);
            st.pending_fast_path_turns.push(turn.clone());
            st.promote_turn_tier(*turn_id, FinalityTier::AttestedFastPath);

            let cert = FastPathCert {
                turn_digest: turn.digest(),
                turn,
                acks: valid_acks,
                post_state_root,
                anchor_height: st.committed_height,
                tier: FinalityTier::AttestedFastPath,
            };
            let _ = st.wal.append_entry(WalEntry::FastPathCommitted(cert.clone()));
            st.fast_path_certs.push(cert.clone());
            return Some(ConsensusNetMessage::FastPathCommit(cert));
        }
        None
    }

    /// Simulate a volatile memory crash on this validator (`Obend.Run.Durable.hstep .crash`),
    /// wiping volatile in-memory state while keeping the WAL (`journal` and `outbox`) durable.
    pub fn simulate_crash(&self) {
        self.state.lock().unwrap().simulate_crash();
    }

    /// Replay the durable WAL after a crash (`Obend.Run.Durable.hstep .recover`),
    /// restoring finalized blocks, vault state root, and highest voted view before rejoining the network.
    pub fn recover_from_wal(&self) -> Result<(), ExposedOnceError> {
        self.state.lock().unwrap().recover_from_wal()
    }

    /// Attempt to cast and persist a validator vote in `(view, kind)` for `block_hash`.
    /// Refuses double-voting (equivocation) in the same view even across a crash + `recover_from_wal()`!
    pub fn try_cast_vote(
        &self,
        view: u64,
        kind: SimplexVoteKind,
        block_hash: [u8; 32],
    ) -> Result<SignedSimplexVote, ExposedOnceError> {
        let mut st = self.state.lock().unwrap();
        st.wal.check_can_vote(view, kind, block_hash)?;
        let vote = SignedSimplexVote::new(&self.keypair, view, kind, block_hash);
        st.wal.record_vote(vote.clone())?;
        let _ = Self::record_vote_and_check_equivocation(&mut st, &vote);
        Ok(vote)
    }

    /// Submit a dispatch effect to this validator's durable WAL (`Obend.Run.Durable.hstep (.submit (.dispatch ..))`).
    pub fn submit_dispatch_effect(
        &self,
        turn: VaultTurn,
        token_id: Option<u64>,
    ) -> Result<OutboxReceiptId, ExposedOnceError> {
        self.state.lock().unwrap().wal.submit_dispatch(turn, token_id)
    }

    /// Expose a journaled dispatch effect at position `pos` (`Obend.Run.Durable.hstep (.expose pos)`).
    /// Succeeds at most once per `pos`, even across `simulate_crash()` + `recover_from_wal()`.
    pub fn expose_effect(&self, pos: u64) -> Result<OutboxReceiptId, ExposedOnceError> {
        self.state.lock().unwrap().wal.expose_effect(pos)
    }

    /// Return all journal positions holding unexposed dispatch effects (`Obend.Run.Durable.pending`).
    pub fn pending_effects(&self) -> Vec<u64> {
        self.state.lock().unwrap().wal.pending_effects()
    }

    /// Snapshot this validator's `DurableNodeWal`.
    pub fn wal_snapshot(&self) -> DurableNodeWal {
        self.state.lock().unwrap().wal.clone()
    }

    pub fn committed_height(&self) -> u64 {
        self.state.lock().unwrap().committed_height
    }

    pub fn current_view(&self) -> u64 {
        self.state.lock().unwrap().current_view
    }

    pub fn state_root(&self) -> [u8; 32] {
        self.state.lock().unwrap().current_state_root
    }

    pub fn finalized_blocks(&self) -> Vec<FinalizedBlockRecord> {
        self.state.lock().unwrap().finalized_blocks.clone()
    }

    pub fn fast_path_certs(&self) -> Vec<FastPathCert> {
        self.state.lock().unwrap().fast_path_certs.clone()
    }

    pub fn slashing_receipts(&self) -> Vec<SlashingReceipt> {
        self.state.lock().unwrap().slashing_receipts.clone()
    }

    pub fn slashed_validators(&self) -> BTreeSet<usize> {
        self.state.lock().unwrap().slashed_validators.clone()
    }

    pub fn skip_certs(&self) -> Vec<SkipCert> {
        self.state.lock().unwrap().skip_certs.clone()
    }

    pub fn epoch_receipts(&self) -> Vec<CollapsedEpochReceipt> {
        self.state.lock().unwrap().epoch_receipts.clone()
    }

    pub fn turn_tier(&self, turn_id: &[u8; 32]) -> Option<FinalityTier> {
        self.state.lock().unwrap().turn_finality.get(turn_id).copied()
    }

    pub fn wire_frames_received(&self) -> usize {
        self.state.lock().unwrap().wire_frames_received
    }

    pub fn shutdown(&mut self) {
        self.running.store(false, Ordering::Release);
        if let Some(handle) = self.tcp_thread.take() {
            let _ = handle.join();
        }
        if let Some(handle) = self.udp_thread.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for NetworkedValidatorNode {
    fn drop(&mut self) {
        self.shutdown();
    }
}

// ============================================================================
// 6. Multi-Validator `SimplexCluster` Orchestrator & 4-Tier Router
// ============================================================================

/// Outcome of submitting a `VaultTurn` through the 4-Tier Finality Router.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TurnSubmissionOutcome {
    /// Committed immediately on the Tier 1 Disjoint Fast-Path (`disjoint_turns_commute`)
    /// with a single quorum acknowledgement without advancing the `Simplex` block height.
    FastPathCommitted {
        cert: FastPathCert,
        tier: FinalityTier,
    },
    /// Routed into the Tier 2 Contended `Simplex` BFT mempool because its read/write footprint
    /// intersects an active in-flight or queued contended turn.
    RoutedToContendedSimplex {
        turn_id: [u8; 32],
        mempool_len: usize,
        tier: FinalityTier,
    },
}

/// Multi-validator networked cluster running $N$ `NetworkedValidatorNode`s over `127.0.0.1:0`
/// ephemeral loopback sockets with integrated `SandboxRunner` (`Powerbox` / `GrainConfig`).
pub struct SimplexCluster {
    pub nodes: Vec<NetworkedValidatorNode>,
    pub fault_tolerance: usize,
    pub quorum_size: usize,
    pub transport: TransportProtocol,
    pub genesis_cells: Vec<VaultCellRecord>,
    pub sandbox: Option<SandboxRunner>,

    /// Active in-flight turns tracked for footprint contention checks.
    pub active_inflight_turns: Vec<VaultTurn>,
    /// Contended `VaultTurn` mempool awaiting the next `Simplex` BFT block height.
    pub mempool_turns: Vec<VaultTurn>,
    /// Queued `drex-clearing@1` limit orders awaiting the next `Simplex` BFT block height.
    pub mempool_orders: Vec<LimitOrder>,
    pub drex_currency: String,
    pub drex_goods: String,
    pub drex_epsilon: u64,
}

impl SimplexCluster {
    /// Start a live $N$-validator cluster (e.g. $N = 4, f = 1$) over `127.0.0.1:0` TCP loopback sockets.
    pub fn new(
        num_validators: usize,
        fault_tolerance: usize,
        initial_cells: Vec<VaultCellRecord>,
    ) -> Result<Self, NodeError> {
        Self::with_transport(
            num_validators,
            fault_tolerance,
            initial_cells,
            TransportProtocol::Tcp,
        )
    }

    /// Start a live $N$-validator cluster over `127.0.0.1:0` with explicit `TransportProtocol` (`Tcp` or `Udp`).
    pub fn with_transport(
        num_validators: usize,
        fault_tolerance: usize,
        initial_cells: Vec<VaultCellRecord>,
        transport: TransportProtocol,
    ) -> Result<Self, NodeError> {
        let quorum_size = 2 * fault_tolerance + 1;
        if num_validators == 0 || num_validators < quorum_size {
            return Err(NodeError::ConsensusVerification(format!(
                "invalid BFT parameters: num_validators ({num_validators}) must be >= 2*f + 1 ({quorum_size})"
            )));
        }

        let keypairs: Vec<ValidatorKeypair> = (0..num_validators)
            .map(|id| {
                let seed = format!("obend-ws32-validator-seed-{id}");
                ValidatorKeypair::from_seed(id, seed.as_bytes())
            })
            .collect();
        let peer_public_keys: Vec<[u8; 32]> = keypairs.iter().map(|kp| kp.public_key).collect();

        let mut nodes = Vec::with_capacity(num_validators);
        for id in 0..num_validators {
            let node = NetworkedValidatorNode::spawn(
                id,
                num_validators,
                fault_tolerance,
                keypairs[id].clone(),
                peer_public_keys.clone(),
                initial_cells.clone(),
                transport,
            )?;
            nodes.push(node);
        }

        let tcp_addrs: Vec<SocketAddr> = nodes.iter().map(|n| n.tcp_addr).collect();
        let udp_addrs: Vec<SocketAddr> = nodes.iter().map(|n| n.udp_addr).collect();
        for node in &nodes {
            node.set_peer_addresses(tcp_addrs.clone(), udp_addrs.clone());
        }

        Ok(Self {
            nodes,
            fault_tolerance,
            quorum_size,
            transport,
            genesis_cells: initial_cells,
            sandbox: None,
            active_inflight_turns: Vec::new(),
            mempool_turns: Vec::new(),
            mempool_orders: Vec::new(),
            drex_currency: "USDC".to_string(),
            drex_goods: "WAFER".to_string(),
            drex_epsilon: 0,
        })
    }

    /// Attach a `SandboxRunner` (`Powerbox`, `Mandate`, `GrainConfig`) to gate all incoming turns.
    pub fn configure_sandbox(&mut self, runner: SandboxRunner) {
        self.sandbox = Some(runner);
    }

    /// Configure the `drex-clearing@1` market pair and duality gap tolerance $\epsilon$.
    pub fn set_drex_market(&mut self, currency: &str, goods: &str, epsilon: u64) {
        self.drex_currency = currency.to_string();
        self.drex_goods = goods.to_string();
        self.drex_epsilon = epsilon;
    }

    /// Submit a `drex-clearing@1` limit order into the Tier 2 `Simplex` BFT clearing mempool.
    pub fn submit_drex_order(&mut self, order: LimitOrder) {
        self.mempool_orders.push(order);
    }

    /// Stage an in-flight turn (checking `SandboxRunner` if configured) so subsequent turns
    /// are tested against it for Bernstein disjointness (`disjoint_turns_commute`).
    pub fn stage_contended_or_inflight_turn(&mut self, turn: VaultTurn) -> Result<(), NodeError> {
        if let Some(sandbox) = &mut self.sandbox {
            sandbox.validate_and_meter_turn(&turn, 100)?;
        }
        if turn.has_duplicate_write_slots() {
            return Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot {
                agent: turn.agent,
            }));
        }
        self.mempool_turns.push(turn);
        Ok(())
    }

    /// Submit a `VaultTurn` through the `SandboxRunner` (`Powerbox` / `Mandate`) and 4-Tier Finality Router:
    /// - If `SandboxRunner` is configured, capability-checks the turn against its `Mandate` first.
    /// - Inspects the turn's read/write slot footprints via `disjoint_turns_commute`:
    ///   - **Tier 1 Disjoint Fast-Path**: If disjoint from all active in-flight and queued contended turns,
    ///     commits immediately across the networked validators with a single quorum acknowledgement
    ///     without waiting for a full `Simplex` block height.
    ///   - **Tier 2 Contended `Simplex` BFT**: If its footprint conflicts with any in-flight or queued turn,
    ///     routes it into the `Simplex` BFT mempool for block-level ordering and clearing.
    pub fn submit_turn(&mut self, turn: VaultTurn) -> Result<TurnSubmissionOutcome, NodeError> {
        if let Some(sandbox) = &mut self.sandbox {
            sandbox.validate_and_meter_turn(&turn, 250)?;
        }
        if turn.has_duplicate_write_slots() {
            return Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot {
                agent: turn.agent,
            }));
        }

        let disjoint_from_inflight = self
            .active_inflight_turns
            .iter()
            .all(|other| disjoint_turns_commute(&turn, other));
        let disjoint_from_mempool = self
            .mempool_turns
            .iter()
            .all(|other| disjoint_turns_commute(&turn, other));

        if disjoint_from_inflight && disjoint_from_mempool {
            let cert = self.execute_fast_path_turn(turn)?;
            Ok(TurnSubmissionOutcome::FastPathCommitted {
                cert,
                tier: FinalityTier::AttestedFastPath,
            })
        } else {
            let turn_id = turn.turn_id;
            for node in &self.nodes {
                node.state
                    .lock()
                    .unwrap()
                    .promote_turn_tier(turn_id, FinalityTier::Speculative);
            }
            self.mempool_turns.push(turn);
            Ok(TurnSubmissionOutcome::RoutedToContendedSimplex {
                turn_id,
                mempool_len: self.mempool_turns.len(),
                tier: FinalityTier::Speculative,
            })
        }
    }

    /// Submit a batch of concurrent `VaultTurn`s, automatically partitioning mutually disjoint turns
    /// onto the Tier 1 Fast-Path and mutually contended turns into the Tier 2 `Simplex` BFT mempool.
    pub fn submit_concurrent_batch(
        &mut self,
        turns: Vec<VaultTurn>,
    ) -> Result<Vec<TurnSubmissionOutcome>, NodeError> {
        let mut outcomes = Vec::with_capacity(turns.len());
        for (i, turn) in turns.iter().enumerate() {
            if let Some(sandbox) = &mut self.sandbox {
                sandbox.validate_and_meter_turn(turn, 250)?;
            }
            if turn.has_duplicate_write_slots() {
                return Err(NodeError::Sandbox(SandboxViolation::DuplicateWriteSlot {
                    agent: turn.agent.clone(),
                }));
            }
            // Check if `turn` is disjoint from every other turn in the concurrent batch
            // as well as active in-flight and existing queued mempool turns
            let disjoint_in_batch = turns
                .iter()
                .enumerate()
                .all(|(j, other)| i == j || disjoint_turns_commute(turn, other));
            let disjoint_from_inflight = self
                .active_inflight_turns
                .iter()
                .all(|other| disjoint_turns_commute(turn, other));
            let disjoint_from_mempool = self
                .mempool_turns
                .iter()
                .all(|other| disjoint_turns_commute(turn, other));

            if disjoint_in_batch && disjoint_from_inflight && disjoint_from_mempool {
                let cert = self.execute_fast_path_turn(turn.clone())?;
                outcomes.push(TurnSubmissionOutcome::FastPathCommitted {
                    cert,
                    tier: FinalityTier::AttestedFastPath,
                });
            } else {
                let turn_id = turn.turn_id;
                for node in &self.nodes {
                    node.state
                        .lock()
                        .unwrap()
                        .promote_turn_tier(turn_id, FinalityTier::Speculative);
                }
                self.mempool_turns.push(turn.clone());
                outcomes.push(TurnSubmissionOutcome::RoutedToContendedSimplex {
                    turn_id,
                    mempool_len: self.mempool_turns.len(),
                    tier: FinalityTier::Speculative,
                });
            }
        }
        Ok(outcomes)
    }

    fn execute_fast_path_turn(&mut self, turn: VaultTurn) -> Result<FastPathCert, NodeError> {
        let turn_id = turn.turn_id;
        let honest_ids = self.honest_validator_ids();
        let proposer_id = *honest_ids.first().ok_or_else(|| {
            NodeError::ConsensusVerification("no honest validators available".to_string())
        })?;

        self.nodes[proposer_id]
            .broadcast(ConsensusNetMessage::FastPathPropose(turn.clone()))?;

        let deadline = Instant::now() + Duration::from_secs(30);
        let mut iter_count = 0usize;
        let mut rebroadcasted = false;
        loop {
            iter_count += 1;
            let mut found_cert: Option<FastPathCert> = None;
            let mut all_honest_committed = true;

            for &id in &honest_ids {
                let certs = self.nodes[id].fast_path_certs();
                if let Some(c) = certs.into_iter().find(|c| c.turn.turn_id == turn_id) {
                    if found_cert.is_none() {
                        found_cert = Some(c);
                    }
                } else {
                    all_honest_committed = false;
                }
            }

            if all_honest_committed {
                if let Some(cert) = found_cert {
                    return Ok(cert);
                }
            }

            // Re-broadcast FastPathCommit if at least one node assembled the FastPathCert
            if let Some(ref cert) = found_cert {
                if !rebroadcasted || iter_count % 25 == 0 {
                    let _ = self.nodes[proposer_id]
                        .broadcast(ConsensusNetMessage::FastPathCommit(cert.clone()));
                    rebroadcasted = true;
                }
            } else if iter_count % 25 == 0 {
                let _ = self.nodes[proposer_id]
                    .broadcast(ConsensusNetMessage::FastPathPropose(turn.clone()));
            }

            if Instant::now() >= deadline {
                return Err(NodeError::QuorumTimeout(
                    "timed out waiting for Tier 1 FastPathCert across loopback sockets".to_string(),
                ));
            }
            thread::sleep(Duration::from_millis(2));
        }
    }

    /// Execute a full networked `Simplex` BFT block round over the `127.0.0.1:0` sockets,
    /// draining contended `VaultTurn`s and `drex-clearing@1` limit orders, running `solve_drex_batch`,
    /// verifying all 13 conditions via `DrexClearingCertificate::verify_with_kernel`, and updating
    /// the `FogOfWar` Merkle root across all honest validators.
    pub fn run_simplex_block(&mut self) -> Result<FinalizedBlockRecord, NodeError> {
        let honest_ids = self.honest_validator_ids();
        let first_honest = *honest_ids.first().ok_or_else(|| {
            NodeError::ConsensusVerification("no honest validators available".to_string())
        })?;

        // If current view's leader is slashed, execute a networked SkipCert view-change first
        loop {
            let view = self.nodes[first_honest].current_view();
            let leader_id = ((view.saturating_sub(1)) as usize) % self.nodes.len();
            if self.nodes[first_honest]
                .slashed_validators()
                .contains(&leader_id)
            {
                self.run_view_skip(view)?;
            } else {
                break;
            }
        }

        let (view, next_height, parent_hash) = {
            let st = self.nodes[first_honest].state.lock().unwrap();
            (
                st.current_view,
                st.committed_height + 1,
                st.committed_tip_hash,
            )
        };
        let leader_id = ((view.saturating_sub(1)) as usize) % self.nodes.len();

        let mut turns: Vec<VaultTurn> = self.active_inflight_turns.drain(..).collect();
        turns.extend(self.mempool_turns.drain(..));
        let drex_orders: Vec<LimitOrder> = self.mempool_orders.drain(..).collect();
        let payload = BlockPayload {
            height: next_height,
            view,
            turns,
            drex_currency: self.drex_currency.clone(),
            drex_goods: self.drex_goods.clone(),
            drex_epsilon: self.drex_epsilon,
            drex_orders,
        };

        let prop_cert = PropCert::create(
            &self.nodes[leader_id].keypair,
            view,
            next_height,
            parent_hash,
            payload.to_bytes(),
        );
        self.nodes[leader_id]
            .state
            .lock()
            .unwrap()
            .wal
            .record_vote(prop_cert.leader_vote.clone())?;

        self.nodes[leader_id]
            .broadcast(ConsensusNetMessage::Propose(prop_cert.clone(), payload.clone()))?;

        let deadline = Instant::now() + Duration::from_secs(30);
        let mut iter_count = 0usize;
        let mut rebroadcasted = false;
        loop {
            iter_count += 1;
            let mut finalized_record: Option<FinalizedBlockRecord> = None;
            let mut all_honest_finalized = true;

            for &id in &honest_ids {
                let blocks = self.nodes[id].finalized_blocks();
                if let Some(b) = blocks.into_iter().find(|b| b.height == next_height) {
                    if finalized_record.is_none() {
                        finalized_record = Some(b);
                    }
                } else {
                    all_honest_finalized = false;
                }
            }

            if all_honest_finalized {
                if let Some(rec) = finalized_record {
                    return Ok(rec);
                }
            }

            if let Some(ref rec) = finalized_record {
                if !rebroadcasted || iter_count % 25 == 0 {
                    let _ = self.nodes[leader_id].broadcast(
                        ConsensusNetMessage::FinalizationCertificate(
                            rec.fin_cert.clone(),
                            rec.payload.clone(),
                        ),
                    );
                    rebroadcasted = true;
                }
            } else if iter_count % 25 == 0 {
                let _ = self.nodes[leader_id].broadcast(ConsensusNetMessage::Propose(
                    prop_cert.clone(),
                    payload.clone(),
                ));
            }

            if Instant::now() >= deadline {
                return Err(NodeError::QuorumTimeout(format!(
                    "timed out waiting for Simplex FinCert at height {next_height} view {view}"
                )));
            }
            thread::sleep(Duration::from_millis(2));
        }
    }

    /// Execute a networked `SkipCert` view-change round across honest validators for `view`.
    pub fn run_view_skip(&mut self, view: u64) -> Result<SkipCert, NodeError> {
        let honest_ids = self.honest_validator_ids();
        for &id in &honest_ids {
            let skip_vote = SignedSimplexVote::new(
                &self.nodes[id].keypair,
                view,
                SimplexVoteKind::Skip,
                [0u8; 32],
            );
            self.nodes[id]
                .state
                .lock()
                .unwrap()
                .wal
                .record_vote(skip_vote.clone())?;
            self.nodes[id].broadcast(ConsensusNetMessage::Vote(skip_vote))?;
        }

        let deadline = Instant::now() + Duration::from_secs(30);
        let mut rebroadcasted = false;
        loop {
            let mut found_skip: Option<SkipCert> = None;
            let mut all_advanced = true;
            for &id in &honest_ids {
                if let Some(sc) = self.nodes[id]
                    .skip_certs()
                    .into_iter()
                    .find(|c| c.view == view)
                {
                    if found_skip.is_none() {
                        found_skip = Some(sc);
                    }
                }
                if self.nodes[id].current_view() <= view {
                    all_advanced = false;
                }
            }
            if all_advanced {
                if let Some(sc) = found_skip {
                    return Ok(sc);
                }
            }
            if !rebroadcasted {
                if let Some(ref sc) = found_skip {
                    let first_honest = honest_ids[0];
                    let _ = self.nodes[first_honest]
                        .broadcast(ConsensusNetMessage::SkipCertificate(sc.clone()));
                    rebroadcasted = true;
                }
            }
            if Instant::now() >= deadline {
                return Err(NodeError::QuorumTimeout(format!(
                    "timed out waiting for SkipCert at view {view}"
                )));
            }
            thread::sleep(Duration::from_millis(2));
        }
    }

    /// Inject a Byzantine double-signing equivocation from `faulty_validator_id` at `view`
    /// over the real loopback sockets and wait for all honest nodes to detect the equivocation,
    /// verify and broadcast the `SlashingReceipt`, and slash `faulty_validator_id`.
    pub fn inject_byzantine_equivocation(
        &mut self,
        faulty_validator_id: usize,
        view: u64,
        block_hash_a: [u8; 32],
        block_hash_b: [u8; 32],
    ) -> Result<SlashingReceipt, NodeError> {
        if faulty_validator_id >= self.nodes.len() {
            return Err(NodeError::ConsensusVerification(format!(
                "faulty_validator_id {faulty_validator_id} out of range (num_validators = {})",
                self.nodes.len()
            )));
        }
        if block_hash_a == block_hash_b {
            return Err(NodeError::ConsensusVerification(
                "Byzantine equivocation requires two distinct block hashes".to_string(),
            ));
        }

        let kp = self.nodes[faulty_validator_id].keypair.clone();
        let vote_a = SignedSimplexVote::new(&kp, view, SimplexVoteKind::Vote, block_hash_a);
        let vote_b = SignedSimplexVote::new(&kp, view, SimplexVoteKind::Vote, block_hash_b);

        self.nodes[faulty_validator_id].broadcast(ConsensusNetMessage::Vote(vote_a))?;
        self.nodes[faulty_validator_id].broadcast(ConsensusNetMessage::Vote(vote_b))?;

        let honest_ids: Vec<usize> = (0..self.nodes.len())
            .filter(|&id| id != faulty_validator_id)
            .collect();

        let deadline = Instant::now() + Duration::from_secs(30);
        let mut rebroadcasted = false;
        loop {
            let mut found_receipt: Option<SlashingReceipt> = None;
            let mut all_detected = true;

            for &id in &honest_ids {
                let receipts = self.nodes[id].slashing_receipts();
                if let Some(r) = receipts
                    .into_iter()
                    .find(|r| r.offender_id == faulty_validator_id && r.view == view)
                {
                    if found_receipt.is_none() {
                        found_receipt = Some(r);
                    }
                } else {
                    all_detected = false;
                }
            }

            if all_detected {
                if let Some(receipt) = found_receipt {
                    return Ok(receipt);
                }
            }

            if !rebroadcasted {
                if let Some(ref receipt) = found_receipt {
                    let _ = self.nodes[honest_ids[0]]
                        .broadcast(ConsensusNetMessage::Slashing(receipt.clone()));
                    rebroadcasted = true;
                }
            }

            if Instant::now() >= deadline {
                return Err(NodeError::QuorumTimeout(
                    "timed out waiting for SlashingReceipt propagation across honest nodes"
                        .to_string(),
                ));
            }
            thread::sleep(Duration::from_millis(2));
        }
    }

    /// Execute Tier 3 `Fold.collapse` epoch checkpointing across `[start_height..=end_height]`,
    /// compressing the finalized multi-height chain into a single `CollapsedEpochReceipt`
    /// and promoting all turns in the epoch to `FinalityTier::Collapsed`.
    pub fn collapse_epoch(
        &mut self,
        epoch_id: u64,
        start_height: u64,
        end_height: u64,
    ) -> Result<CollapsedEpochReceipt, NodeError> {
        if start_height == 0 || start_height > end_height {
            return Err(NodeError::ConsensusVerification(format!(
                "invalid epoch height range [{start_height}..={end_height}]"
            )));
        }

        let honest_ids = self.honest_validator_ids();
        let ref_node = *honest_ids.first().ok_or_else(|| {
            NodeError::ConsensusVerification("no honest validators available".to_string())
        })?;

        let blocks: Vec<FinalizedBlockRecord> = self.nodes[ref_node]
            .finalized_blocks()
            .into_iter()
            .filter(|b| b.height >= start_height && b.height <= end_height)
            .collect();

        let expected_count = (end_height - start_height + 1) as usize;
        if blocks.len() != expected_count {
            return Err(NodeError::ConsensusVerification(format!(
                "incomplete finalized blocks in requested epoch range [{start_height}..={end_height}]: found {}, expected {expected_count}",
                blocks.len()
            )));
        }

        // Reconstruct the vault state right before `start_height` in exact chronological order
        let mut initial_cells = self.genesis_cells.clone();
        for prior_blk in self.nodes[ref_node]
            .finalized_blocks()
            .into_iter()
            .filter(|b| b.height < start_height)
        {
            for fp_turn in &prior_blk.pre_block_fast_path_turns {
                fp_turn.apply_to_cells(&mut initial_cells);
            }
            Fold::apply_block_to_cells(
                &mut initial_cells,
                &prior_blk.payload,
                prior_blk.clearing_cert.as_ref(),
            );
        }
        for fp_turn in &blocks[0].pre_block_fast_path_turns {
            fp_turn.apply_to_cells(&mut initial_cells);
        }

        let mut session = {
            let _guard = FFI_KERNEL_LOCK.lock().unwrap();
            ObendSession::new()?
        };
        let receipt = Fold::collapse(epoch_id, &initial_cells, &blocks, &mut session)?;

        // Promote all blocks and turns (including settled Tier 1 fast-path turns) in [start_height..=end_height]
        // to FinalityTier::Collapsed on all honest nodes
        for &id in &honest_ids {
            let mut st = self.nodes[id].state.lock().unwrap();
            let mut promoted_turns = Vec::new();
            for blk in &mut st.finalized_blocks {
                if blk.height >= start_height && blk.height <= end_height {
                    blk.tier = FinalityTier::Collapsed;
                    for t in &blk.pre_block_fast_path_turns {
                        promoted_turns.push(t.turn_id);
                    }
                    for t in &blk.payload.turns {
                        promoted_turns.push(t.turn_id);
                    }
                }
            }
            for tid in promoted_turns {
                st.promote_turn_tier(tid, FinalityTier::Collapsed);
            }
            st.epoch_receipts.push(receipt.clone());
            let _ = st
                .wal
                .append_entry(WalEntry::EpochCollapsed(receipt.clone()));
        }

        Ok(receipt)
    }

    pub fn honest_validator_ids(&self) -> Vec<usize> {
        let mut slashed = BTreeSet::new();
        for node in &self.nodes {
            for id in node.slashed_validators() {
                slashed.insert(id);
            }
        }
        (0..self.nodes.len())
            .filter(|id| !slashed.contains(id))
            .collect()
    }
}

#[cfg(test)]
mod wal_tests {
    use super::*;

    fn sample_turn(seed: u8, slot: u64, val: &[u8]) -> VaultTurn {
        VaultTurn::new([seed; 32], "agent-wal", vec![slot], vec![(slot, val.to_vec())])
    }

    #[test]
    fn wal_expose_once_and_pending_decreases_across_restarts() {
        let mut wal = DurableNodeWal::new();
        let kp = ValidatorKeypair::from_seed(0, b"wal-test-validator-0");

        // Position 0: a validator vote (not a dispatch effect)
        let vote = SignedSimplexVote::new(&kp, 1, SimplexVoteKind::Finalize, [0xAA; 32]);
        let vote_pos = wal.record_vote(vote).expect("record_vote should succeed");
        assert_eq!(vote_pos, OutboxReceiptId(0));

        // Position 1 & 2: two dispatch effects with linear token IDs
        let r1 = wal
            .submit_dispatch(sample_turn(1, 10, b"alpha"), Some(1001))
            .expect("first dispatch should succeed");
        let r2 = wal
            .submit_dispatch(sample_turn(2, 20, b"beta"), Some(1002))
            .expect("second dispatch should succeed");
        assert_eq!(r1, OutboxReceiptId(1));
        assert_eq!(r2, OutboxReceiptId(2));

        // Duplicate linear token_id must be refused (`journal_once`)
        let dup_tok = wal.submit_dispatch(sample_turn(3, 30, b"gamma"), Some(1001));
        assert_eq!(
            dup_tok,
            Err(ExposedOnceError::TokenAlreadyConsumed {
                token_id: 1001,
                existing_pos: 1,
            })
        );

        // `pending_effects` initially holds [1, 2]
        assert_eq!(wal.pending_effects(), vec![1, 2]);

        // Exposing non-dispatch entry at pos 0 fails with NotDispatch(0)
        assert_eq!(wal.expose_effect(0), Err(ExposedOnceError::NotDispatch(0)));
        assert_eq!(
            wal.expose_effect(99),
            Err(ExposedOnceError::NotDispatch(99))
        );

        // Exposing pos 1 succeeds and strictly decreases pending (`pending_decreases_on_expose`)
        assert_eq!(wal.expose_effect(1), Ok(OutboxReceiptId(1)));
        assert_eq!(wal.pending_effects(), vec![2]);
        assert!(wal.outbox.contains(&1));

        // Duplicate exposure before crash is refused (`expose_once`)
        assert_eq!(
            wal.expose_effect(1),
            Err(ExposedOnceError::AlreadyExposed(1))
        );

        // Simulate crash: volatile memory is down, submissions require recovery first (`hstep .submit` -> `.down`)
        wal.simulate_crash();
        assert!(!wal.memory_up);
        assert_eq!(
            wal.submit_dispatch(sample_turn(4, 40, b"down"), None),
            Err(ExposedOnceError::NodeDown)
        );
        assert_eq!(
            wal.expose_effect(1),
            Err(ExposedOnceError::AlreadyExposed(1))
        );

        // Recover from WAL and verify outbox durability across crash + recovery
        wal.recover_from_wal().expect("WAL recovery should succeed");
        assert!(wal.memory_up);
        assert_eq!(wal.pending_effects(), vec![2]);
        assert_eq!(
            wal.expose_effect(1),
            Err(ExposedOnceError::AlreadyExposed(1))
        );

        // Still-unexposed effect at pos 2 can be exposed exactly once after recovery
        assert_eq!(wal.expose_effect(2), Ok(OutboxReceiptId(2)));
        assert!(wal.pending_effects().is_empty());
        assert_eq!(
            wal.expose_effect(2),
            Err(ExposedOnceError::AlreadyExposed(2))
        );
    }

    #[test]
    fn wal_multi_crash_recover_idempotent_and_byte_log_roundtrip() {
        let mut wal_single = DurableNodeWal::new();
        let kp = ValidatorKeypair::from_seed(1, b"wal-idempotent-seed");

        wal_single
            .record_vote(SignedSimplexVote::new(
                &kp,
                3,
                SimplexVoteKind::Propose,
                [0x11; 32],
            ))
            .unwrap();
        let receipt = wal_single
            .submit_dispatch(sample_turn(7, 42, b"payload"), Some(77))
            .unwrap();
        wal_single.expose_effect(receipt.0).unwrap();
        wal_single
            .submit_dispatch(sample_turn(8, 43, b"pending"), Some(88))
            .unwrap();

        let mut wal_multi = wal_single.clone();

        // Single crash + recover
        wal_single.simulate_crash();
        wal_single.recover_from_wal().unwrap();

        // k = 5 consecutive crashes followed by a single recover (`crash_recover_idempotent`)
        for _ in 0..5 {
            wal_multi.simulate_crash();
        }
        wal_multi.recover_from_wal().unwrap();

        assert_eq!(wal_single, wal_multi);
        assert_eq!(wal_single.pending_effects(), vec![2]);
        assert_eq!(wal_single.highest_voted_view, 3);

        // Cold-start reconstruction from raw framed bytes
        let bytes = wal_multi.to_bytes();
        let decoded = DurableNodeWal::from_bytes(&bytes).expect("from_bytes should succeed");
        assert_eq!(decoded.journal, wal_single.journal);
        assert_eq!(decoded.outbox, wal_single.outbox);
        assert_eq!(decoded.voted_by_view, wal_single.voted_by_view);
        assert_eq!(decoded.consumed_tokens, wal_single.consumed_tokens);

        // Tampering with a byte in the WAL frame payload is caught by cSHAKE256 digest check
        let mut corrupted = bytes.clone();
        let last_idx = corrupted.len() - 1;
        corrupted[last_idx] ^= 0xFF;
        assert!(matches!(
            DurableNodeWal::from_bytes(&corrupted),
            Err(ExposedOnceError::CorruptWal(_))
        ));

        // Torn / truncated trailing frame recovery (`recover_from_truncated_bytes`)
        let mut torn_tail = bytes.clone();
        torn_tail.extend_from_slice(b"OWAL\x00\x00\x00\x20partial-unflushed-tail");
        assert!(matches!(
            DurableNodeWal::from_bytes(&torn_tail),
            Err(ExposedOnceError::CorruptWal(_))
        ));
        let (recovered_torn, truncated_len) = DurableNodeWal::recover_from_truncated_bytes(&torn_tail)
            .expect("recover_from_truncated_bytes should discard incomplete trailing frame");
        assert_eq!(truncated_len, 30);
        assert_eq!(recovered_torn.journal, wal_single.journal);
        assert_eq!(recovered_torn.outbox, wal_single.outbox);

        // Duplicate `OutboxExposed { pos }` in serialized byte log is rejected by `from_bytes`
        let mut dup_expose_bytes = bytes.clone();
        let dup_entry = WalEntry::OutboxExposed { pos: receipt.0 };
        DurableNodeWal::append_raw_frame(&mut dup_expose_bytes, &dup_entry);
        assert_eq!(
            DurableNodeWal::from_bytes(&dup_expose_bytes),
            Err(ExposedOnceError::AlreadyExposed(receipt.0))
        );
    }

    #[test]
    fn wal_prevents_post_crash_validator_equivocation() {
        let mut wal = DurableNodeWal::new();
        let kp = ValidatorKeypair::from_seed(2, b"equivocation-guard-seed");
        let block_a = [0xA1; 32];
        let block_b = [0xB2; 32];

        let vote_a = SignedSimplexVote::new(&kp, 4, SimplexVoteKind::Finalize, block_a);
        wal.record_vote(vote_a.clone())
            .expect("initial vote should be journaled");
        assert_eq!(wal.highest_voted_view, 4);

        // Crash and recover from WAL
        wal.simulate_crash();
        assert_eq!(wal.highest_voted_view, 0);
        assert!(wal.voted_by_view.is_empty());

        wal.recover_from_wal()
            .expect("recover_from_wal should restore voted views");
        assert_eq!(wal.highest_voted_view, 4);

        // Attempting to vote for `block_b != block_a` in the same view (4) & kind (Finalize)
        // after recovery MUST be refused!
        let vote_b = SignedSimplexVote::new(&kp, 4, SimplexVoteKind::Finalize, block_b);
        let err = wal
            .record_vote(vote_b)
            .expect_err("post-recovery double-vote must be refused");
        assert_eq!(
            err,
            ExposedOnceError::EquivocationRefused {
                view: 4,
                kind: SimplexVoteKind::Finalize,
                existing_block_hash: block_a,
                attempted_block_hash: block_b,
            }
        );

        // Cross-kind equivocation in view 4: Propose(block_b) or Skip after Finalize(block_a) MUST be refused!
        let cross_propose = SignedSimplexVote::new(&kp, 4, SimplexVoteKind::Propose, block_b);
        assert_eq!(
            wal.record_vote(cross_propose),
            Err(ExposedOnceError::EquivocationRefused {
                view: 4,
                kind: SimplexVoteKind::Propose,
                existing_block_hash: block_a,
                attempted_block_hash: block_b,
            })
        );
        let skip_after_finalize = SignedSimplexVote::new(&kp, 4, SimplexVoteKind::Skip, [0u8; 32]);
        assert_eq!(
            wal.record_vote(skip_after_finalize),
            Err(ExposedOnceError::EquivocationRefused {
                view: 4,
                kind: SimplexVoteKind::Skip,
                existing_block_hash: block_a,
                attempted_block_hash: [0u8; 32],
            })
        );

        // Re-affirming the exact same vote `block_a` in view 4 is idempotent, and voting in view 5 succeeds
        assert!(wal.check_can_vote(4, SimplexVoteKind::Finalize, block_a).is_ok());
        let vote_v5 = SignedSimplexVote::new(&kp, 5, SimplexVoteKind::Propose, block_a);
        wal.record_vote(vote_v5)
            .expect("voting Propose(block_a) in a higher view 5 should succeed");
        assert_eq!(wal.highest_voted_view, 5);

        // Crash + recover at view 5, then verify Finalize(block_b) in view 5 is refused because Propose(block_a) was cast
        wal.simulate_crash();
        wal.recover_from_wal().unwrap();
        let finalize_conflict_v5 =
            SignedSimplexVote::new(&kp, 5, SimplexVoteKind::Finalize, block_b);
        assert_eq!(
            wal.record_vote(finalize_conflict_v5),
            Err(ExposedOnceError::EquivocationRefused {
                view: 5,
                kind: SimplexVoteKind::Finalize,
                existing_block_hash: block_a,
                attempted_block_hash: block_b,
            })
        );
        // Whereas Finalize(block_a) in view 5 (matching Propose(block_a)) is allowed
        let finalize_same_v5 = SignedSimplexVote::new(&kp, 5, SimplexVoteKind::Finalize, block_a);
        wal.record_vote(finalize_same_v5)
            .expect("Finalize for the same proposed block in view 5 must succeed");

        // View 6: cast Skip, crash + recover, then verify Finalize(block_a) in view 6 is refused
        let skip_v6 = SignedSimplexVote::new(&kp, 6, SimplexVoteKind::Skip, [0u8; 32]);
        wal.record_vote(skip_v6).unwrap();
        wal.simulate_crash();
        wal.recover_from_wal().unwrap();
        let finalize_after_skip =
            SignedSimplexVote::new(&kp, 6, SimplexVoteKind::Finalize, block_a);
        assert_eq!(
            wal.record_vote(finalize_after_skip),
            Err(ExposedOnceError::EquivocationRefused {
                view: 6,
                kind: SimplexVoteKind::Finalize,
                existing_block_hash: [0u8; 32],
                attempted_block_hash: block_a,
            })
        );
    }

    #[test]
    fn cluster_validator_crash_and_wal_recovery_restores_state_outbox_and_epoch_collapse() {
        let genesis = vec![
            VaultCellRecord {
                id: 1,
                required: vec![IpcAuth::Read],
                salt: [0x10; 32],
                content: b"genesis-cell-1".to_vec(),
            },
            VaultCellRecord {
                id: 2,
                required: vec![IpcAuth::Read],
                salt: [0x20; 32],
                content: b"genesis-cell-2".to_vec(),
            },
        ];

        let mut cluster =
            SimplexCluster::new(4, 1, genesis).expect("4-node cluster should spawn");

        // Submit a contended turn and finalize block 1
        let turn1 = VaultTurn::new([0x31; 32], "agent-a", vec![1], vec![(1, b"v1".to_vec())]);
        let turn2 = VaultTurn::new([0x32; 32], "agent-a", vec![1], vec![(1, b"v2".to_vec())]);
        cluster.submit_concurrent_batch(vec![turn1, turn2]).unwrap();
        let blk1 = cluster
            .run_simplex_block()
            .expect("block 1 should finalize");
        assert_eq!(blk1.height, 1);

        // Submit a second block and collapse epoch 1 across heights [1..=2]
        let turn3 = VaultTurn::new([0x33; 32], "agent-b", vec![2], vec![(2, b"v3".to_vec())]);
        cluster.submit_concurrent_batch(vec![turn3]).unwrap();
        let blk2 = cluster
            .run_simplex_block()
            .expect("block 2 should finalize");
        assert_eq!(blk2.height, 2);

        let epoch_receipt = cluster
            .collapse_epoch(1, 1, 2)
            .expect("epoch collapse [1..=2] should succeed");
        assert_eq!(cluster.nodes[0].epoch_receipts().len(), 1);

        // Submit two dispatch effects on node 0 and expose the first
        let r_exposed = cluster.nodes[0]
            .submit_dispatch_effect(sample_turn(0x41, 1, b"effect-1"), Some(501))
            .unwrap();
        let r_pending = cluster.nodes[0]
            .submit_dispatch_effect(sample_turn(0x42, 2, b"effect-2"), Some(502))
            .unwrap();
        assert_eq!(
            cluster.nodes[0].expose_effect(r_exposed.0),
            Ok(r_exposed)
        );

        let pre_crash_root = cluster.nodes[0].state_root();
        let pre_crash_height = cluster.nodes[0].committed_height();
        assert_eq!(pre_crash_height, 2);

        // Crash node 0 multiple times in a row, then recover from WAL
        cluster.nodes[0].simulate_crash();
        cluster.nodes[0].simulate_crash();
        cluster.nodes[0].simulate_crash();
        assert_eq!(cluster.nodes[0].committed_height(), 0);
        assert!(cluster.nodes[0].finalized_blocks().is_empty());
        assert!(cluster.nodes[0].epoch_receipts().is_empty());

        cluster.nodes[0]
            .recover_from_wal()
            .expect("node 0 should recover from WAL");

        assert_eq!(cluster.nodes[0].committed_height(), pre_crash_height);
        assert_eq!(cluster.nodes[0].state_root(), pre_crash_root);
        assert_eq!(cluster.nodes[0].finalized_blocks().len(), 2);
        assert_eq!(cluster.nodes[0].epoch_receipts(), vec![epoch_receipt]);
        for blk in cluster.nodes[0].finalized_blocks() {
            assert_eq!(blk.tier, FinalityTier::Collapsed);
        }
        assert_eq!(cluster.nodes[0].pending_effects(), vec![r_pending.0]);

        // Duplicate exposure of `r_exposed` after node recovery is still refused
        assert_eq!(
            cluster.nodes[0].expose_effect(r_exposed.0),
            Err(ExposedOnceError::AlreadyExposed(r_exposed.0))
        );
        // Unexposed effect `r_pending` can still be exposed once
        assert_eq!(
            cluster.nodes[0].expose_effect(r_pending.0),
            Ok(r_pending)
        );

        // Node 0 refuses to equivocate in view 1 (where `blk1` was finalized) for both Finalize and Skip
        let conflicting_hash = [0xEE; 32];
        let equiv_attempt =
            cluster.nodes[0].try_cast_vote(blk1.view, SimplexVoteKind::Finalize, conflicting_hash);
        assert_eq!(
            equiv_attempt,
            Err(ExposedOnceError::EquivocationRefused {
                view: blk1.view,
                kind: SimplexVoteKind::Finalize,
                existing_block_hash: blk1.block_hash,
                attempted_block_hash: conflicting_hash,
            })
        );
        let skip_equiv_attempt =
            cluster.nodes[0].try_cast_vote(blk1.view, SimplexVoteKind::Skip, [0u8; 32]);
        assert_eq!(
            skip_equiv_attempt,
            Err(ExposedOnceError::EquivocationRefused {
                view: blk1.view,
                kind: SimplexVoteKind::Skip,
                existing_block_hash: blk1.block_hash,
                attempted_block_hash: [0u8; 32],
            })
        );
    }
}
