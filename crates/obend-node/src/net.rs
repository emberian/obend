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

#[derive(Debug, thiserror::Error)]
pub enum NodeError {
    #[error("sandbox confinement violation: {0}")]
    Sandbox(#[from] SandboxViolation),
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
                if !st.slashed_validators.contains(&st.node_id) {
                    let already_voted_in_view = st.seen_votes.iter().any(|v| {
                        v.voter_id == st.node_id
                            && v.view == prop_cert.view
                            && v.kind == SimplexVoteKind::Finalize
                    });
                    if !already_voted_in_view {
                        let fin_vote = SignedSimplexVote::new(
                            keypair,
                            prop_cert.view,
                            SimplexVoteKind::Finalize,
                            prop_cert.block_hash,
                        );
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

        st.finalized_blocks.push(FinalizedBlockRecord {
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
        });
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
            st.fast_path_certs.push(cert.clone());
            return Some(ConsensusNetMessage::FastPathCommit(cert));
        }
        None
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
