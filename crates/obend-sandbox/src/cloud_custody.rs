//! Prepaid confined sessions and archive-first custody. Authentication and kernel-proof
//! verification are explicit host-supplied interfaces; hashes never stand in for signatures.
use crate::grain::{
    digest_slot_entries, GrainCapabilities, GrainExecutionReceipt, GrainExecutor, GrainProgram, GrainTermination,
    ReproducibilityTier,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

pub type CustodyDigest = [u8; 32];
type Digest = CustodyDigest;

// Keccak-f[1600], SP 800-185 cSHAKE256 with N empty and a nonempty customization.
fn keccak(s: &mut [u64; 25]) {
    const RC: [u64; 24] = [
        1,
        0x8082,
        0x800000000000808a,
        0x8000000080008000,
        0x808b,
        0x80000001,
        0x8000000080008081,
        0x8000000000008009,
        0x8a,
        0x88,
        0x80008009,
        0x8000000a,
        0x8000808b,
        0x800000000000008b,
        0x8000000000008089,
        0x8000000000008003,
        0x8000000000008002,
        0x8000000000000080,
        0x800a,
        0x800000008000000a,
        0x8000000080008081,
        0x8000000000008080,
        0x80000001,
        0x8000000080008008,
    ];
    const ROT: [u32; 25] =
        [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];
    for rc in RC {
        let c: [u64; 5] = std::array::from_fn(|x| (0..5).fold(0, |a, y| a ^ s[x + 5 * y]));
        for x in 0..5 {
            for y in 0..5 {
                s[x + 5 * y] ^= c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            }
        }
        let mut b = [0; 25];
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = s[x + 5 * y].rotate_left(ROT[x + 5 * y]);
            }
        }
        for x in 0..5 {
            for y in 0..5 {
                s[x + 5 * y] = b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }
        s[0] ^= rc;
    }
}
fn left_encode(n: usize) -> Vec<u8> {
    let bytes = n.to_be_bytes();
    let first = bytes.iter().position(|b| *b != 0).unwrap_or(bytes.len() - 1);
    let mut out = vec![(bytes.len() - first) as u8];
    out.extend_from_slice(&bytes[first..]);
    out
}
fn cshake(domain: &[u8], input: &[u8]) -> Digest {
    let mut bytes = left_encode(136);
    bytes.extend(left_encode(0));
    bytes.extend(left_encode(domain.len() * 8));
    bytes.extend(domain);
    bytes.resize(bytes.len().div_ceil(136) * 136, 0);
    bytes.extend(input);
    bytes.push(4);
    bytes.resize(bytes.len().div_ceil(136) * 136, 0);
    *bytes.last_mut().expect("padded sponge") |= 128;
    let mut s = [0u64; 25];
    for block in bytes.chunks_exact(136) {
        for (i, b) in block.iter().enumerate() {
            s[i / 8] ^= (*b as u64) << (8 * (i % 8));
        }
        keccak(&mut s);
    }
    std::array::from_fn(|i| (s[i / 8] >> (8 * (i % 8))) as u8)
}
fn nat(mut n: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        out.push(b | if n == 0 { 0 } else { 128 });
        if n == 0 {
            return out;
        }
    }
}
fn fields(xs: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for x in xs {
        out.extend(nat(x.len() as u64));
        out.extend(x);
    }
    out
}
fn hash(domain: &str, xs: &[Vec<u8>]) -> Digest {
    cshake(domain.as_bytes(), &fields(xs))
}
fn merkle_root(xs: &[Vec<u8>]) -> Digest {
    let mut tail = hash("OBEND.CUSTODY.MERKLE.EMPTY/v1", &[]);
    for x in xs.iter().rev() {
        tail = hash("OBEND.CUSTODY.MERKLE.NODE/v1", &[vec![1], x.clone(), tail.to_vec()]);
    }
    hash("OBEND.CUSTODY.MERKLE.ROOT/v1", &[nat(xs.len() as u64), tail.to_vec()])
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PrepaidLease {
    lease_id: u64,
    start_period: u64,
    next_due: u64,
    rent: u64,
    initial_budget: u64,
    remaining: u64,
    drawn: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeaseError {
    Replay,
    OffSchedule,
    OverDraw,
    InsufficientBudget,
    Overflow,
    InvalidState,
}
impl PrepaidLease {
    pub fn new(lease_id: u64, start_period: u64, rent: u64, budget: u64) -> Self {
        Self {
            lease_id,
            start_period,
            next_due: start_period,
            rent,
            initial_budget: budget,
            remaining: budget,
            drawn: 0,
        }
    }
    pub fn lease_id(&self) -> u64 {
        self.lease_id
    }
    pub fn next_due(&self) -> u64 {
        self.next_due
    }
    pub fn remaining(&self) -> u64 {
        self.remaining
    }
    pub fn drawn(&self) -> u64 {
        self.drawn
    }
    pub fn initial_budget(&self) -> u64 {
        self.initial_budget
    }
    pub fn valid(&self) -> bool {
        self.remaining.checked_add(self.drawn) == Some(self.initial_budget)
            && self.next_due.checked_sub(self.start_period).and_then(|n| n.checked_mul(self.rent)) == Some(self.drawn)
    }
    pub fn state_root(&self) -> Digest {
        merkle_root(
            &[
                self.lease_id,
                self.start_period,
                self.next_due,
                self.rent,
                self.initial_budget,
                self.remaining,
                self.drawn,
            ]
            .map(nat),
        )
    }
    pub fn discharge_period(&mut self, period: u64, requested: u64) -> Result<Digest, LeaseError> {
        if !self.valid() {
            return Err(LeaseError::InvalidState);
        }
        if period < self.next_due {
            return Err(LeaseError::Replay);
        }
        if period > self.next_due {
            return Err(LeaseError::OffSchedule);
        }
        if requested != self.rent {
            return Err(LeaseError::OverDraw);
        }
        if self.remaining < self.rent {
            return Err(LeaseError::InsufficientBudget);
        }
        let next = self.next_due.checked_add(1).ok_or(LeaseError::Overflow)?;
        let drawn = self.drawn.checked_add(self.rent).ok_or(LeaseError::Overflow)?;
        self.next_due = next;
        self.remaining -= self.rent;
        self.drawn = drawn;
        Ok(self.state_root())
    }
}

#[derive(Clone, Debug)]
pub struct ConfinedForkSpec {
    pub lease_id: u64,
    pub budget: u64,
    pub egress_doors: BTreeSet<String>,
    pub caps: BTreeSet<u64>,
    pub grain_capabilities: GrainCapabilities,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForkError {
    DuplicateIdentity,
    AmplifiedEgress,
    AmplifiedCapability,
    BudgetOverdraw,
    InvalidParent,
    NamespaceCollision,
}
#[derive(Debug)]
pub struct ConfinedGrainSession {
    lease: PrepaidLease,
    mind_root: Digest,
    egress_doors: BTreeSet<String>,
    caps: BTreeSet<u64>,
    grain_capabilities: GrainCapabilities,
    memory: BTreeMap<Vec<u8>, Vec<u8>>,
    checkpoint_root: Digest,
    receipt_head: Digest,
    genesis: ForkGenesis,
    turn_receipts: Vec<Digest>,
    issued: BTreeSet<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForkGenesis {
    pub parent_checkpoint: Digest,
    pub child_id: u64,
    pub mind_root: Digest,
    pub lease_root: Digest,
    pub authority_root: Digest,
}
impl ForkGenesis {
    pub fn commitment(&self) -> Digest {
        hash(
            "OBEND.CUSTODY.FORK/v1",
            &[
                self.parent_checkpoint.to_vec(),
                nat(self.child_id),
                self.mind_root.to_vec(),
                self.lease_root.to_vec(),
                self.authority_root.to_vec(),
            ],
        )
    }
    pub fn verify(&self, parent: Digest, head: Digest) -> bool {
        self.parent_checkpoint == parent && self.commitment() == head
    }
}
fn caps_subset(c: &GrainCapabilities, p: &GrainCapabilities) -> bool {
    let reads: BTreeSet<_> = p.allowed_read_slots.iter().collect();
    let writes: BTreeSet<_> = p.allowed_emit_slots.iter().collect();
    c.allowed_read_slots.iter().all(|k| reads.contains(k))
        && c.allowed_emit_slots.iter().all(|k| writes.contains(k))
        && (!c.allow_hash_digest || p.allow_hash_digest)
}
fn authority_root(doors: &BTreeSet<String>, caps: &BTreeSet<u64>, gc: &GrainCapabilities) -> Digest {
    // Runtime hostcall rights extend the formal custom-capability namespace explicitly.
    hash(
        "OBEND.CUSTODY.AUTHORITY/v1",
        &[
            fields(&doors.iter().map(|s| s.as_bytes().to_vec()).collect::<Vec<_>>()),
            fields(&caps.iter().copied().map(nat).collect::<Vec<_>>()),
            fields(&gc.allowed_read_slots.iter().copied().map(nat).collect::<Vec<_>>()),
            fields(&gc.allowed_emit_slots.iter().copied().map(nat).collect::<Vec<_>>()),
            vec![u8::from(gc.allow_hash_digest)],
        ],
    )
}
impl ConfinedGrainSession {
    pub fn new(
        lease: PrepaidLease,
        doors: BTreeSet<String>,
        caps: BTreeSet<u64>,
        gc: GrainCapabilities,
    ) -> Result<Self, ForkError> {
        if !lease.valid() {
            return Err(ForkError::InvalidParent);
        }
        let mind_root = hash("OBEND.CUSTODY.MIND/v1", &[nat(lease.lease_id), vec![]]);
        let genesis = ForkGenesis {
            parent_checkpoint: [0; 32],
            child_id: lease.lease_id,
            mind_root,
            lease_root: lease.state_root(),
            authority_root: authority_root(&doors, &caps, &gc),
        };
        let head = genesis.commitment();
        let mut s = Self {
            lease,
            mind_root,
            egress_doors: doors,
            caps,
            grain_capabilities: gc,
            memory: BTreeMap::new(),
            checkpoint_root: head,
            receipt_head: head,
            genesis,
            turn_receipts: Vec::new(),
            issued: BTreeSet::new(),
        };
        s.checkpoint_root = s.state_root();
        Ok(s)
    }
    fn state_root(&self) -> Digest {
        hash(
            "OBEND.CUSTODY.SESSION/v1",
            &[
                nat(self.lease.lease_id),
                self.lease.state_root().to_vec(),
                self.mind_root.to_vec(),
                authority_root(&self.egress_doors, &self.caps, &self.grain_capabilities).to_vec(),
                self.receipt_head.to_vec(),
            ],
        )
    }
    pub fn lease(&self) -> &PrepaidLease {
        &self.lease
    }
    pub fn mind_root(&self) -> Digest {
        self.mind_root
    }
    pub fn checkpoint_root(&self) -> Digest {
        self.checkpoint_root
    }
    pub fn receipt_head(&self) -> Digest {
        self.receipt_head
    }
    pub fn genesis(&self) -> &ForkGenesis {
        &self.genesis
    }
    pub fn read_memory(&self, key: &[u8]) -> Option<&[u8]> {
        self.memory.get(key).map(Vec::as_slice)
    }
    pub fn write_memory(&mut self, key: Vec<u8>, value: Vec<u8>) {
        self.memory.insert(key, value);
        let root = compute_var_data_root(&self.memory);
        self.mind_root = hash("OBEND.CUSTODY.MIND/v1", &[nat(self.lease.lease_id), root.to_vec()]);
        self.checkpoint_root = self.state_root();
    }
    pub fn execute(
        &mut self,
        program: &GrainProgram,
        inputs: &[(u64, Vec<u8>)],
        budget: crate::grain::GrainBudget,
    ) -> GrainExecutionReceipt {
        let executor = GrainExecutor::new(budget, self.grain_capabilities.clone());
        let receipt = executor.execute(program, inputs);
        let payload = execution_payload(&receipt, turn_request_digest(program, inputs, &executor));
        self.receipt_head = hash("OBEND.CUSTODY.RECEIPT/v1", &[self.receipt_head.to_vec(), payload.to_vec()]);
        self.turn_receipts.push(payload);
        for (slot, bytes) in &receipt.emitted_slots {
            self.memory.insert(slot.to_be_bytes().to_vec(), bytes.clone());
        }
        self.mind_root =
            hash("OBEND.CUSTODY.MIND/v1", &[nat(self.lease.lease_id), compute_var_data_root(&self.memory).to_vec()]);
        self.checkpoint_root = self.state_root();
        receipt
    }
    pub fn verify_receipt_chain(&self, parent: Digest) -> bool {
        self.genesis.parent_checkpoint == parent
            && self.genesis.authority_root == authority_root(&self.egress_doors, &self.caps, &self.grain_capabilities)
            && self.turn_receipts.iter().fold(self.genesis.commitment(), |head, r| {
                hash("OBEND.CUSTODY.RECEIPT/v1", &[head.to_vec(), r.to_vec()])
            }) == self.receipt_head
    }
    /// Checks everything before mutation. Repeated calls cannot reuse an issued child identity.
    /// The caller owns the global lease-id allocation; ancestry-specific namespaces also bind the fork point.
    pub fn fork_two(&mut self, a: ConfinedForkSpec, b: ConfinedForkSpec) -> Result<(Self, Self), ForkError> {
        if !self.lease.valid() {
            return Err(ForkError::InvalidParent);
        }
        if a.lease_id == b.lease_id
            || a.lease_id == self.lease.lease_id
            || b.lease_id == self.lease.lease_id
            || self.issued.contains(&a.lease_id)
            || self.issued.contains(&b.lease_id)
        {
            return Err(ForkError::DuplicateIdentity);
        }
        for c in [&a, &b] {
            if !c.egress_doors.is_subset(&self.egress_doors) {
                return Err(ForkError::AmplifiedEgress);
            }
            if !c.caps.is_subset(&self.caps) || !caps_subset(&c.grain_capabilities, &self.grain_capabilities) {
                return Err(ForkError::AmplifiedCapability);
            }
        }
        let sum = a.budget.checked_add(b.budget).ok_or(ForkError::BudgetOverdraw)?;
        if sum > self.lease.remaining {
            return Err(ForkError::BudgetOverdraw);
        }
        let make = |s: ConfinedForkSpec| {
            let lease = PrepaidLease::new(s.lease_id, self.lease.next_due, self.lease.rent, s.budget);
            let mind_root = hash("OBEND.CUSTODY.MIND/v1", &[nat(s.lease_id), self.mind_root.to_vec()]);
            let genesis = ForkGenesis {
                parent_checkpoint: self.checkpoint_root,
                child_id: s.lease_id,
                mind_root,
                lease_root: lease.state_root(),
                authority_root: authority_root(&s.egress_doors, &s.caps, &s.grain_capabilities),
            };
            let head = genesis.commitment();
            let mut c = Self {
                lease,
                mind_root,
                egress_doors: s.egress_doors,
                caps: s.caps,
                grain_capabilities: s.grain_capabilities,
                memory: self.memory.clone(),
                checkpoint_root: head,
                receipt_head: head,
                genesis,
                turn_receipts: Vec::new(),
                issued: BTreeSet::new(),
            };
            c.checkpoint_root = c.state_root();
            c
        };
        let (a, b) = (make(a), make(b));
        if a.mind_root == b.mind_root {
            return Err(ForkError::NamespaceCollision);
        }
        self.issued.insert(a.lease.lease_id);
        self.issued.insert(b.lease.lease_id);
        self.lease.remaining -= sum;
        self.lease.initial_budget -= sum;
        self.checkpoint_root = self.state_root();
        Ok((a, b))
    }
}

/// Canonical byte paths sorted by BTreeMap; content and paths are separately length-framed.
pub fn compute_var_data_root(entries: &BTreeMap<Vec<u8>, Vec<u8>>) -> Digest {
    merkle_root(
        &entries
            .iter()
            .map(|(path, bytes)| fields(&[path.clone(), hash("OBEND.CUSTODY.CONTENT/v1", &[bytes.clone()]).to_vec()]))
            .collect::<Vec<_>>(),
    )
}

/// Implement with a pinned public-key signature scheme. The host must not accept arbitrary
/// publisher keys supplied by an archive. Kernel promotion requires a separate proof check.
pub trait CustodyAuthenticator {
    fn sign(&self, message: &[u8]) -> Vec<u8>;
    fn verify(&self, signer: &Digest, message: &[u8], signature: &[u8]) -> bool;
    fn verify_kernel_receipt(&self, _receipt: &GrainExecutionReceipt, _proof: &[u8]) -> bool {
        false
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignedGrainPackage {
    pub publisher: Digest,
    pub bytes: Vec<u8>,
    pub program_digest: Digest,
    pub signature: Vec<u8>,
}
impl SignedGrainPackage {
    pub fn digest(&self) -> Digest {
        hash("OBEND.CUSTODY.PACKAGE/v1", &[self.publisher.to_vec(), self.bytes.clone(), self.program_digest.to_vec()])
    }
    pub fn verify(&self, trusted: Digest, auth: &impl CustodyAuthenticator) -> bool {
        self.publisher == trusted && auth.verify(&trusted, &self.digest(), &self.signature)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GrainCustodyAnchor {
    pub generation: u64,
    pub package_digest: Digest,
    pub var_data_root: Digest,
    pub receipt_head: Digest,
    pub lease_root: Digest,
    pub ingress_root: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CustodyPoisonReason {
    VarData,
    Package,
    Divergence,
    Rollback,
    BrokenReceipt,
    Lease,
    Ingress,
    Malformed,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrainCustodyStatus {
    Empty,
    Ready,
    RecoveryRequired,
    Poisoned(CustodyPoisonReason),
}
#[derive(Debug)]
pub enum CustodyError {
    Io(std::io::Error),
    Format(serde_json::Error),
    Refused(CustodyPoisonReason),
    NotReady,
    Lease(LeaseError),
    Authentication,
    RequestMismatch,
    MissingKernelProof,
    Locked,
    Overflow,
}
impl From<std::io::Error> for CustodyError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<serde_json::Error> for CustodyError {
    fn from(e: serde_json::Error) -> Self {
        Self::Format(e)
    }
}
impl From<LeaseError> for CustodyError {
    fn from(e: LeaseError) -> Self {
        Self::Lease(e)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AriadneTicket {
    pub seq_no: u64,
    pub req_digest: Digest,
    pub mmr_root: Digest,
    pub signer: Digest,
    pub signature: Vec<u8>,
}
impl AriadneTicket {
    fn message(&self) -> Digest {
        hash("OBEND.CUSTODY.TICKET/v1", &[nat(self.seq_no), self.req_digest.to_vec(), self.mmr_root.to_vec()])
    }
    pub fn verify(&self, trusted: Digest, auth: &impl CustodyAuthenticator) -> bool {
        self.signer == trusted && auth.verify(&trusted, &self.message(), &self.signature)
    }
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct Peak {
    height: u32,
    root: Digest,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AriadneIngressLog {
    leaves: Vec<Digest>,
    peaks: Vec<Peak>,
}
impl AriadneIngressLog {
    pub fn len(&self) -> usize {
        self.leaves.len()
    }
    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }
    pub fn root(&self) -> Digest {
        hash(
            "OBEND.CUSTODY.MMR.ROOT/v1",
            &[
                nat(self.leaves.len() as u64),
                fields(&self.peaks.iter().rev().map(|p| p.root.to_vec()).collect::<Vec<_>>()),
            ],
        )
    }
    fn push(&mut self, req: Digest) {
        let mut peak = Peak {
            height: 0,
            root: hash("OBEND.CUSTODY.MOUNTAIN/v1", &[vec![0], nat(self.leaves.len() as u64), req.to_vec()]),
        };
        while self.peaks.last().is_some_and(|p| p.height == peak.height) {
            let left = self.peaks.pop().expect("equal-height peak");
            peak.root = hash("OBEND.CUSTODY.MOUNTAIN/v1", &[vec![1], left.root.to_vec(), peak.root.to_vec()]);
            peak.height += 1;
        }
        self.peaks.push(peak);
        self.leaves.push(req);
    }
    pub fn commit(&mut self, req: Digest, signer: Digest, auth: &impl CustodyAuthenticator) -> AriadneTicket {
        let seq_no = self.len() as u64;
        self.push(req);
        let mut t = AriadneTicket { seq_no, req_digest: req, mmr_root: self.root(), signer, signature: vec![] };
        t.signature = auth.sign(&t.message());
        t
    }
    fn rebuilt(&self) -> Self {
        let mut l = Self::default();
        for r in &self.leaves {
            l.push(*r);
        }
        l
    }
    /// A full audit verifies the ticket prefix, the later MMR root, and every sequential
    /// execution opening. A shorter trace cannot silently claim completion past this ticket.
    pub fn verify_non_omission(
        &self,
        t: &AriadneTicket,
        trusted: Digest,
        auth: &impl CustodyAuthenticator,
        trace: &[(u64, Digest)],
        advertised_root: Digest,
    ) -> bool {
        let Ok(k) = usize::try_from(t.seq_no) else {
            return false;
        };
        if !t.verify(trusted, auth)
            || self.leaves.get(k) != Some(&t.req_digest)
            || self.rebuilt() != *self
            || self.root() != advertised_root
        {
            return false;
        }
        let mut prefix = Self::default();
        for r in self.leaves.iter().take(k + 1) {
            prefix.push(*r);
        }
        if prefix.root() != t.mmr_root || trace.len() <= k || trace.len() > self.len() {
            return false;
        }
        trace.iter().enumerate().all(|(i, (seq, r))| *seq == i as u64 && self.leaves[i] == *r)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SettlementRecord {
    lease_id: u64,
    period: u64,
    before: PrepaidLease,
    after: PrepaidLease,
    receipt: Digest,
}
impl SettlementRecord {
    fn new(before: PrepaidLease, period: u64) -> Result<Self, LeaseError> {
        let mut after = before.clone();
        after.discharge_period(period, after.rent)?;
        let receipt = hash(
            "OBEND.CUSTODY.SETTLE/v1",
            &[nat(before.lease_id), nat(period), before.state_root().to_vec(), after.state_root().to_vec()],
        );
        Ok(Self { lease_id: before.lease_id, period, before, after, receipt })
    }
    fn valid(&self) -> bool {
        Self::new(self.before.clone(), self.period).as_ref() == Ok(self)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Archive {
    package: SignedGrainPackage,
    #[serde(serialize_with = "serialize_var", deserialize_with = "deserialize_var")]
    var: BTreeMap<Vec<u8>, Vec<u8>>,
    lease: PrepaidLease,
    anchor: GrainCustodyAnchor,
    previous: Option<GrainCustodyAnchor>,
    transition: Digest,
    transition_signature: Vec<u8>,
    executions: Vec<(u64, Digest, Digest)>,
    settlements: Vec<SettlementRecord>,
    ingress: AriadneIngressLog,
}
// Canonical sorted rows keep byte paths lossless and reject duplicate keys during decode.
fn serialize_var<S: serde::Serializer>(var: &BTreeMap<Vec<u8>, Vec<u8>>, s: S) -> Result<S::Ok, S::Error> {
    var.iter().collect::<Vec<_>>().serialize(s)
}
fn deserialize_var<'de, D: serde::Deserializer<'de>>(d: D) -> Result<BTreeMap<Vec<u8>, Vec<u8>>, D::Error> {
    let rows = Vec::<(Vec<u8>, Vec<u8>)>::deserialize(d)?;
    if !rows.windows(2).all(|p| p[0].0 < p[1].0) {
        return Err(serde::de::Error::custom("noncanonical var paths"));
    }
    Ok(rows.into_iter().collect())
}
impl Archive {
    fn transition_digest(&self) -> Digest {
        let mut anchor = self.anchor.clone();
        anchor.receipt_head = [0; 32];
        // Struct field order is fixed; maps are encoded as canonical sorted rows.
        hash(
            "OBEND.CUSTODY.TRANSITION/v1",
            &[
                serde_json::to_vec(&self.previous).expect("anchor serialization"),
                serde_json::to_vec(&anchor).expect("anchor serialization"),
                serde_json::to_vec(&self.executions).expect("execution serialization"),
                serde_json::to_vec(&self.settlements).expect("settlement serialization"),
            ],
        )
    }
}

const MAX_RECORD_BYTES: u64 = 16 * 1024 * 1024;
fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<Option<T>, CustodyError> {
    let mut file = match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e.into()),
    };
    if !file.metadata()?.is_file() || file.metadata()?.len() > MAX_RECORD_BYTES {
        return Err(CustodyError::Refused(CustodyPoisonReason::Malformed));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file).take(MAX_RECORD_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_RECORD_BYTES {
        return Err(CustodyError::Refused(CustodyPoisonReason::Malformed));
    }
    Ok(Some(serde_json::from_slice(&bytes)?))
}
fn durable_write<T: Serialize>(dir: &Path, name: &str, value: &T) -> Result<(), CustodyError> {
    let bytes = serde_json::to_vec(value)?;
    if bytes.len() as u64 > MAX_RECORD_BYTES {
        return Err(CustodyError::Refused(CustodyPoisonReason::Malformed));
    }
    let tmp = dir.join(format!(".{name}.pending"));
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&tmp)?;
    if !file.metadata()?.is_file() || file.metadata()?.nlink() != 1 {
        return Err(CustodyError::Refused(CustodyPoisonReason::Malformed));
    }
    file.set_len(0)?;
    file.write_all(&bytes)?;
    file.sync_all()?;
    fs::rename(tmp, dir.join(name))?;
    File::open(dir)?.sync_all()?;
    Ok(())
}

/// A locked single-writer archive. The retained anchor should also be kept by the client:
/// a hostile host can erase both local files, which no local reopen algorithm can detect.
pub struct GrainCustodyHost {
    dir: PathBuf,
    _lock: File,
    trusted: Digest,
    archive: Option<Archive>,
    anchor: Option<GrainCustodyAnchor>,
    ingress: AriadneIngressLog,
    status: GrainCustodyStatus,
}
impl GrainCustodyHost {
    pub fn open(
        path: impl AsRef<Path>,
        trusted: Digest,
        auth: &impl CustodyAuthenticator,
    ) -> Result<Self, CustodyError> {
        fs::create_dir_all(path.as_ref())?;
        if fs::symlink_metadata(path.as_ref())?.file_type().is_symlink() {
            return Err(CustodyError::Refused(CustodyPoisonReason::Malformed));
        }
        let dir = path.as_ref().to_path_buf();
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(dir.join("lock"))?;
        // SAFETY: the owned descriptor remains open for the lifetime of this host.
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(CustodyError::Locked);
        }
        let archive = read_json::<Archive>(&dir.join("archive.json"))?;
        let anchor = read_json(&dir.join("anchor.json"))?;
        let ingress = read_json(&dir.join("ingress.json"))?.unwrap_or_default();
        let mut host = Self { dir, _lock: lock, trusted, archive, anchor, ingress, status: GrainCustodyStatus::Empty };
        host.status = host.classify(auth);
        Ok(host)
    }
    pub fn open_at(
        path: impl AsRef<Path>,
        trusted: Digest,
        retained: GrainCustodyAnchor,
        auth: &impl CustodyAuthenticator,
    ) -> Result<Self, CustodyError> {
        let mut h = Self::open(path, trusted, auth)?;
        h.anchor = Some(retained);
        h.status = h.classify(auth);
        Ok(h)
    }
    pub fn status(&self) -> &GrainCustodyStatus {
        &self.status
    }
    pub fn anchor(&self) -> Option<&GrainCustodyAnchor> {
        self.anchor.as_ref()
    }
    pub fn lease(&self) -> Option<&PrepaidLease> {
        self.archive.as_ref().map(|a| &a.lease)
    }
    pub fn ingress(&self) -> &AriadneIngressLog {
        &self.ingress
    }
    fn classify(&self, auth: &impl CustodyAuthenticator) -> GrainCustodyStatus {
        use CustodyPoisonReason as P;
        use GrainCustodyStatus as S;
        let Some(a) = &self.archive else {
            return if self.anchor.is_none() && self.ingress.is_empty() {
                S::Empty
            } else {
                S::Poisoned(P::Divergence)
            };
        };
        if !a.package.verify(self.trusted, auth) || a.package.digest() != a.anchor.package_digest {
            return S::Poisoned(P::Package);
        }
        if compute_var_data_root(&a.var) != a.anchor.var_data_root {
            return S::Poisoned(P::VarData);
        }
        if !a.lease.valid() || a.lease.state_root() != a.anchor.lease_root {
            return S::Poisoned(P::Lease);
        }
        if self.ingress.rebuilt() != self.ingress
            || a.ingress.rebuilt() != a.ingress
            || a.ingress.root() != a.anchor.ingress_root
            || !self.ingress.leaves.starts_with(&a.ingress.leaves)
        {
            return S::Poisoned(P::Ingress);
        }
        if !a.executions.iter().enumerate().all(|(i, (k, r, _))| *k == i as u64 && a.ingress.leaves.get(i) == Some(r)) {
            return S::Poisoned(P::Ingress);
        }
        if !a.settlements.iter().all(SettlementRecord::valid)
            || !a.settlements.windows(2).all(|w| w[0].after == w[1].before)
            || a.settlements.last().is_some_and(|s| s.after != a.lease)
        {
            return S::Poisoned(P::Lease);
        }
        if a.transition != a.transition_digest()
            || a.anchor.receipt_head != a.transition
            || !auth.verify(&self.trusted, &a.transition, &a.transition_signature)
        {
            return S::Poisoned(P::BrokenReceipt);
        }
        match &self.anchor {
            Some(base) if a.anchor.generation < base.generation => S::Poisoned(P::Rollback),
            Some(base) if a.anchor == *base => S::Ready,
            Some(base)
                if base.generation.checked_add(1) == Some(a.anchor.generation)
                    && a.previous.as_ref() == Some(base)
                    && base.package_digest == a.anchor.package_digest =>
            {
                S::RecoveryRequired
            }
            None if a.anchor.generation == 0 && a.previous.is_none() => S::RecoveryRequired,
            _ => S::Poisoned(P::Divergence),
        }
    }
    pub fn reopen(&mut self, auth: &impl CustodyAuthenticator) -> Result<GrainCustodyStatus, CustodyError> {
        self.archive = read_json::<Archive>(&self.dir.join("archive.json"))?;
        self.ingress = read_json(&self.dir.join("ingress.json"))?.unwrap_or_default();
        self.status = self.classify(auth);
        Ok(self.status.clone())
    }
    fn persist_archive(&mut self, mut a: Archive, auth: &impl CustodyAuthenticator) -> Result<(), CustodyError> {
        a.anchor.var_data_root = compute_var_data_root(&a.var);
        a.anchor.lease_root = a.lease.state_root();
        a.ingress = self.ingress.clone();
        a.anchor.ingress_root = a.ingress.root();
        a.transition = a.transition_digest();
        a.anchor.receipt_head = a.transition;
        a.transition_signature = auth.sign(&a.transition);
        if !auth.verify(&self.trusted, &a.transition, &a.transition_signature) {
            return Err(CustodyError::Authentication);
        }
        self.status = GrainCustodyStatus::Poisoned(CustodyPoisonReason::Malformed);
        durable_write(&self.dir, "archive.json", &a)?;
        self.archive = Some(a);
        self.status = GrainCustodyStatus::RecoveryRequired;
        Ok(())
    }
    pub fn install(
        &mut self,
        package: SignedGrainPackage,
        lease: PrepaidLease,
        auth: &impl CustodyAuthenticator,
    ) -> Result<(), CustodyError> {
        if self.status != GrainCustodyStatus::Empty {
            return Err(CustodyError::NotReady);
        }
        if !package.verify(self.trusted, auth) || !lease.valid() {
            return Err(CustodyError::Authentication);
        }
        let anchor = GrainCustodyAnchor {
            generation: 0,
            package_digest: package.digest(),
            var_data_root: [0; 32],
            receipt_head: [0; 32],
            lease_root: lease.state_root(),
            ingress_root: self.ingress.root(),
        };
        self.persist_archive(
            Archive {
                package,
                lease,
                var: BTreeMap::new(),
                anchor,
                previous: None,
                transition: [0; 32],
                transition_signature: vec![],
                executions: vec![],
                settlements: vec![],
                ingress: self.ingress.clone(),
            },
            auth,
        )?;
        self.recover_one_ahead(auth)
    }
    pub fn recover_one_ahead(&mut self, auth: &impl CustodyAuthenticator) -> Result<(), CustodyError> {
        self.reopen(auth)?;
        if self.status != GrainCustodyStatus::RecoveryRequired {
            return Err(CustodyError::NotReady);
        }
        let anchor = self.archive.as_ref().ok_or(CustodyError::NotReady)?.anchor.clone();
        durable_write(&self.dir, "anchor.json", &anchor)?;
        self.anchor = Some(anchor);
        self.status = GrainCustodyStatus::Ready;
        Ok(())
    }
    fn next_archive(&self) -> Result<Archive, CustodyError> {
        if self.status != GrainCustodyStatus::Ready {
            return Err(CustodyError::NotReady);
        }
        let mut a = self.archive.clone().ok_or(CustodyError::NotReady)?;
        a.previous = Some(a.anchor.clone());
        a.anchor.generation = a.anchor.generation.checked_add(1).ok_or(CustodyError::Overflow)?;
        Ok(a)
    }
    pub fn checkpoint(
        &mut self,
        var: BTreeMap<Vec<u8>, Vec<u8>>,
        auth: &impl CustodyAuthenticator,
    ) -> Result<(), CustodyError> {
        let mut a = self.next_archive()?;
        a.var = var;
        self.persist_archive(a, auth)
    }
    /// The durable pending record is a before/after pair. Replay applies the after image
    /// exactly once, and returns the original receipt even when the anchor write crashed.
    pub fn settle_or_replay(&mut self, period: u64, auth: &impl CustodyAuthenticator) -> Result<Digest, CustodyError> {
        self.reopen(auth)?;
        if self.status == GrainCustodyStatus::RecoveryRequired {
            self.recover_one_ahead(auth)?;
        }
        if self.status != GrainCustodyStatus::Ready {
            return Err(CustodyError::NotReady);
        }
        let current = self.archive.as_ref().ok_or(CustodyError::NotReady)?;
        if let Some(r) = current.settlements.iter().find(|r| r.lease_id == current.lease.lease_id && r.period == period)
        {
            return Ok(r.receipt);
        }
        let pending = read_json::<SettlementRecord>(&self.dir.join("settlement.json"))?;
        let record = match pending {
            Some(r) if r.after == current.lease => SettlementRecord::new(current.lease.clone(), period)?,
            Some(r) if r.before == current.lease && r.period == period && r.valid() => r,
            Some(_) => return Err(CustodyError::Refused(CustodyPoisonReason::Lease)),
            None => SettlementRecord::new(current.lease.clone(), period)?,
        };
        durable_write(&self.dir, "settlement.json", &record)?;
        self.apply_settlement(record, auth)
    }
    fn apply_settlement(
        &mut self,
        record: SettlementRecord,
        auth: &impl CustodyAuthenticator,
    ) -> Result<Digest, CustodyError> {
        let mut a = self.next_archive()?;
        if !record.valid() || a.lease != record.before {
            return Err(CustodyError::Refused(CustodyPoisonReason::Lease));
        }
        a.lease = record.after.clone();
        let receipt = record.receipt;
        a.settlements.push(record);
        self.persist_archive(a, auth)?;
        self.recover_one_ahead(auth)?;
        Ok(receipt)
    }
    pub fn commit_ingress(
        &mut self,
        req: Digest,
        client: Digest,
        signature: &[u8],
        auth: &impl CustodyAuthenticator,
    ) -> Result<AriadneTicket, CustodyError> {
        if self.status != GrainCustodyStatus::Ready {
            return Err(CustodyError::NotReady);
        }
        if !auth.verify(&client, &req, signature) {
            return Err(CustodyError::Authentication);
        }
        let mut log = self.ingress.clone();
        let t = log.commit(req, self.trusted, auth);
        if !t.verify(self.trusted, auth) {
            return Err(CustodyError::Authentication);
        }
        self.status = GrainCustodyStatus::Poisoned(CustodyPoisonReason::Ingress);
        durable_write(&self.dir, "ingress.json", &log)?;
        self.ingress = log;
        self.status = GrainCustodyStatus::Ready;
        Ok(t)
    }
    pub fn execute_turn(
        &mut self,
        ticket: &AriadneTicket,
        program: &GrainProgram,
        inputs: &[(u64, Vec<u8>)],
        executor: &GrainExecutor,
        proof: &[u8],
        auth: &impl CustodyAuthenticator,
    ) -> Result<GrainExecutionReceipt, CustodyError> {
        let mut a = self.next_archive()?;
        let req = turn_request_digest(program, inputs, executor);
        if program.digest() != a.package.program_digest
            || !ticket.verify(self.trusted, auth)
            || ticket.req_digest != req
            || ticket.seq_no != a.executions.len() as u64
            || self.ingress.leaves.get(a.executions.len()) != Some(&req)
        {
            return Err(CustodyError::RequestMismatch);
        }
        let mut prefix = AriadneIngressLog::default();
        for r in self.ingress.leaves.iter().take(a.executions.len() + 1) {
            prefix.push(*r);
        }
        if prefix.root() != ticket.mmr_root || !executor.tier.is_deterministic() {
            return Err(CustodyError::RequestMismatch);
        }
        let receipt = executor.execute(program, inputs);
        if executor.tier == ReproducibilityTier::R4KernelProved && !auth.verify_kernel_receipt(&receipt, proof) {
            return Err(CustodyError::MissingKernelProof);
        }
        // Custody binds the complete receipt, including termination and machine outputs,
        // beyond the narrower legacy execution-receipt commitment.
        let full = execution_payload(&receipt, ticket.message());
        for (slot, bytes) in &receipt.emitted_slots {
            a.var.insert(format!("slot/{slot}").into_bytes(), bytes.clone());
        }
        a.executions.push((ticket.seq_no, req, full));
        self.persist_archive(a, auth)?;
        self.recover_one_ahead(auth)?;
        Ok(receipt)
    }
}
fn execution_payload(r: &GrainExecutionReceipt, ticket: Digest) -> Digest {
    let termination = match r.termination {
        GrainTermination::Halted => 0,
        GrainTermination::OutOfFuel => 1,
        GrainTermination::MemoryLimitExceeded => 2,
        GrainTermination::CapabilityDenied => 3,
    };
    let stack = match r.stack_top {
        None => vec![0],
        Some(v) => [vec![1], v.to_be_bytes().to_vec()].concat(),
    };
    hash(
        "OBEND.CUSTODY.EXECUTION/v1",
        &[
            r.program_digest.to_vec(),
            r.input_digest.to_vec(),
            r.output_digest.to_vec(),
            nat(r.fuel_consumed),
            nat(r.peak_memory_bytes as u64),
            vec![r.tier.tag_byte(), termination],
            r.commitment.to_vec(),
            digest_slot_entries(b"OBEND.CUSTODY.EMITTED/v1", &r.emitted_slots).to_vec(),
            stack,
            r.registers.iter().flat_map(|x| x.to_be_bytes()).collect(),
            r.last_hash_digest.to_vec(),
            ticket.to_vec(),
        ],
    )
}
/// Binds the exact executor policy and resource envelope as well as program and inputs.
pub fn turn_request_digest(p: &GrainProgram, inputs: &[(u64, Vec<u8>)], e: &GrainExecutor) -> Digest {
    hash(
        "OBEND.CUSTODY.REQUEST/v1",
        &[
            p.digest().to_vec(),
            digest_slot_entries(b"OBEND-GRAIN-INPUTS-V1:", inputs).to_vec(),
            nat(e.budget.max_fuel),
            nat(e.budget.max_memory_bytes as u64),
            nat(e.budget.max_output_bytes as u64),
            fields(&e.capabilities.allowed_read_slots.iter().copied().map(nat).collect::<Vec<_>>()),
            fields(&e.capabilities.allowed_emit_slots.iter().copied().map(nat).collect::<Vec<_>>()),
            vec![u8::from(e.capabilities.allow_hash_digest), e.tier.tag_byte()],
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grain::{sha256, GrainBudget, GrainOp};
    use std::sync::atomic::{AtomicU64, Ordering};
    // This fixture exercises authentication plumbing only; production supplies a public-key backend.
    struct Auth;
    impl CustodyAuthenticator for Auth {
        fn sign(&self, m: &[u8]) -> Vec<u8> {
            sha256(&[b"test-only-key:".as_slice(), m].concat()).to_vec()
        }
        fn verify(&self, k: &Digest, m: &[u8], s: &[u8]) -> bool {
            *k == [7; 32] && s == self.sign(m)
        }
    }
    struct Temp(PathBuf);
    impl Temp {
        fn new() -> Self {
            static N: AtomicU64 = AtomicU64::new(0);
            let p = std::env::temp_dir().join(format!(
                "obend-custody-{}-{}",
                std::process::id(),
                N.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&p).unwrap();
            Self(p)
        }
    }
    impl Drop for Temp {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    fn test_program() -> GrainProgram {
        GrainProgram::new("emit", vec![GrainOp::EmitSlot { slot_id: 1, data: b"result".to_vec() }, GrainOp::Halt])
    }
    fn package() -> SignedGrainPackage {
        let mut p = SignedGrainPackage {
            publisher: [7; 32],
            bytes: b"immutable package".to_vec(),
            program_digest: test_program().digest(),
            signature: vec![],
        };
        p.signature = Auth.sign(&p.digest());
        p
    }
    fn host(t: &Temp) -> GrainCustodyHost {
        let mut h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.status(), &GrainCustodyStatus::Empty);
        h.install(package(), PrepaidLease::new(1, 0, 10, 100), &Auth).unwrap();
        h
    }
    fn parent() -> ConfinedGrainSession {
        ConfinedGrainSession::new(
            PrepaidLease::new(1, 0, 10, 100),
            ["api:443".into()].into(),
            [1, 2].into(),
            GrainCapabilities::allow_all(&[1, 2]),
        )
        .unwrap()
    }
    fn spec(id: u64, budget: u64) -> ConfinedForkSpec {
        ConfinedForkSpec {
            lease_id: id,
            budget,
            egress_doors: BTreeSet::new(),
            caps: [1].into(),
            grain_capabilities: GrainCapabilities::strict(vec![1], vec![], false),
        }
    }
    fn mutate(t: &Temp, f: impl FnOnce(&mut Archive)) {
        let mut a = read_json::<Archive>(&t.0.join("archive.json")).unwrap().unwrap();
        f(&mut a);
        durable_write(&t.0, "archive.json", &a).unwrap();
    }
    #[test]
    fn lean_commitment_vectors() {
        assert_eq!(
            PrepaidLease::new(1, 0, 10, 100).state_root(),
            [
                10, 109, 57, 143, 13, 113, 96, 249, 210, 40, 202, 84, 43, 89, 143, 81, 156, 102, 184, 77, 112, 182, 82,
                234, 220, 103, 77, 21, 228, 173, 25, 61
            ]
        );
        assert_eq!(
            compute_var_data_root(&[(vec![120], b"abc".to_vec())].into()),
            [
                240, 65, 64, 145, 126, 136, 96, 128, 102, 23, 43, 57, 253, 74, 196, 95, 211, 8, 126, 209, 72, 102, 18,
                184, 210, 8, 75, 23, 249, 237, 46, 115
            ]
        );
        let mut log = AriadneIngressLog::default();
        log.push([1; 32]);
        log.push([2; 32]);
        assert_eq!(
            log.root(),
            [
                24, 37, 34, 139, 251, 190, 210, 234, 68, 118, 155, 54, 247, 38, 17, 58, 106, 124, 159, 74, 156, 254,
                161, 54, 245, 207, 119, 70, 114, 106, 236, 117
            ]
        );
    }
    #[test]
    fn cshake_nist_vector() {
        let got = cshake(b"Email Signature", &[0, 1, 2, 3]);
        let expected = [
            0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d, 0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c, 0x48, 0xb8, 0xe4,
            0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69, 0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0, 0xed, 0xd1,
        ];
        assert_eq!(got, expected);
    }
    #[test]
    fn lease_lifecycle_and_refusals() {
        let mut l = PrepaidLease::new(1, 4, 10, 30);
        let before = l.clone();
        assert_eq!(l.discharge_period(3, 10), Err(LeaseError::Replay));
        assert_eq!(l.discharge_period(5, 10), Err(LeaseError::OffSchedule));
        assert_eq!(l.discharge_period(4, 11), Err(LeaseError::OverDraw));
        assert_eq!(l, before);
        for p in 4..7 {
            l.discharge_period(p, 10).unwrap();
            assert!(l.valid());
        }
        assert_eq!((l.remaining(), l.drawn()), (0, 30));
        assert_eq!(l.discharge_period(7, 10), Err(LeaseError::InsufficientBudget));
        assert_eq!(l.discharge_period(6, 10), Err(LeaseError::Replay));
    }
    #[test]
    fn lease_overflow_atomic() {
        let mut l = PrepaidLease::new(1, u64::MAX, 0, 10);
        let old = l.clone();
        assert_eq!(l.discharge_period(u64::MAX, 0), Err(LeaseError::Overflow));
        assert_eq!(l, old);
    }
    #[test]
    fn lease_every_field_bound() {
        let l = PrepaidLease::new(1, 4, 10, 100);
        let base = l.state_root();
        for i in 0..7 {
            let mut x = l.clone();
            match i {
                0 => x.lease_id += 1,
                1 => x.start_period += 1,
                2 => x.next_due += 1,
                3 => x.rent += 1,
                4 => x.initial_budget += 1,
                5 => x.remaining += 1,
                _ => x.drawn += 1,
            };
            assert_ne!(x.state_root(), base);
        }
    }
    #[test]
    fn fork_isolated_attenuated_conserved_and_anchored() {
        let mut p = parent();
        p.write_memory(b"x".to_vec(), b"old".to_vec());
        let root = p.checkpoint_root();
        let (mut a, b) = p.fork_two(spec(2, 30), spec(3, 20)).unwrap();
        assert_eq!(p.lease.remaining() + a.lease.remaining() + b.lease.remaining(), 100);
        assert!(p.lease.valid());
        assert_ne!(a.mind_root(), b.mind_root());
        assert!(a.genesis().verify(root, a.receipt_head()));
        assert!(b.genesis().verify(root, b.receipt_head()));
        assert!(!a.genesis().verify([0; 32], a.receipt_head()));
        a.write_memory(b"x".to_vec(), b"new".to_vec());
        assert_eq!(b.read_memory(b"x"), Some(b"old".as_slice()));
        assert_eq!(p.read_memory(b"x"), Some(b"old".as_slice()));
        let (aa, ab) = a.fork_two(spec(4, 10), spec(5, 10)).unwrap();
        assert_eq!(
            p.lease.remaining()
                + a.lease.remaining()
                + b.lease.remaining()
                + aa.lease.remaining()
                + ab.lease.remaining(),
            100
        );
    }
    #[test]
    fn fork_duplicate_ids_refused() {
        let mut p = parent();
        assert!(matches!(p.fork_two(spec(2, 1), spec(2, 1)), Err(ForkError::DuplicateIdentity)));
        assert_eq!(p.lease.remaining(), 100);
    }
    #[test]
    fn fork_reissued_ids_refused() {
        let mut p = parent();
        p.fork_two(spec(2, 1), spec(3, 1)).unwrap();
        assert!(matches!(p.fork_two(spec(2, 1), spec(4, 1)), Err(ForkError::DuplicateIdentity)));
    }
    #[test]
    fn fork_egress_amplification_refused() {
        let mut p = parent();
        let mut a = spec(2, 1);
        a.egress_doors.insert("evil:443".into());
        assert!(matches!(p.fork_two(a, spec(3, 1)), Err(ForkError::AmplifiedEgress)));
    }
    #[test]
    fn fork_caps_amplification_refused() {
        let mut p = parent();
        let mut a = spec(2, 1);
        a.caps.insert(999);
        assert!(matches!(p.fork_two(a, spec(3, 1)), Err(ForkError::AmplifiedCapability)));
    }
    #[test]
    fn fork_grain_caps_amplification_refused() {
        let mut p = parent();
        let mut a = spec(2, 1);
        a.grain_capabilities.allowed_emit_slots.push(999);
        assert!(matches!(p.fork_two(a, spec(3, 1)), Err(ForkError::AmplifiedCapability)));
    }
    #[test]
    fn fork_budget_overflow_refused() {
        let mut p = parent();
        assert!(matches!(p.fork_two(spec(2, u64::MAX), spec(3, 1)), Err(ForkError::BudgetOverdraw)));
        assert!(matches!(p.fork_two(spec(2, 51), spec(3, 50)), Err(ForkError::BudgetOverdraw)));
        assert_eq!(p.lease.remaining(), 100);
    }
    #[test]
    fn ready_reopen_real_r2_r3_execution() {
        let t = Temp::new();
        let mut h = host(&t);
        let p = test_program();
        for tier in [ReproducibilityTier::R2DeterministicGrain, ReproducibilityTier::R3ReceiptAttested] {
            let e = GrainExecutor::new(GrainBudget::default(), GrainCapabilities::allow_all(&[1])).with_tier(tier);
            let r = turn_request_digest(&p, &[], &e);
            let ticket = h.commit_ingress(r, [7; 32], &Auth.sign(&r), &Auth).unwrap();
            let receipt = h.execute_turn(&ticket, &p, &[], &e, &[], &Auth).unwrap();
            assert!(receipt.verify_commitment());
            assert_eq!(receipt.tier, tier);
        }
        drop(h);
        let h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.status(), &GrainCustodyStatus::Ready);
    }
    #[test]
    fn r4_needs_kernel_proof() {
        let t = Temp::new();
        let mut h = host(&t);
        let p = test_program();
        let e = GrainExecutor::new(GrainBudget::default(), GrainCapabilities::allow_all(&[]))
            .with_tier(ReproducibilityTier::R4KernelProved);
        let r = turn_request_digest(&p, &[], &e);
        let ticket = h.commit_ingress(r, [7; 32], &Auth.sign(&r), &Auth).unwrap();
        assert!(matches!(h.execute_turn(&ticket, &p, &[], &e, &[], &Auth), Err(CustodyError::MissingKernelProof)));
    }
    #[test]
    fn var_tampering_poisoned() {
        let t = Temp::new();
        let mut h = host(&t);
        mutate(&t, |a| {
            a.var.insert(b"x".to_vec(), vec![1]);
        });
        assert_eq!(h.reopen(&Auth).unwrap(), GrainCustodyStatus::Poisoned(CustodyPoisonReason::VarData));
    }
    #[test]
    fn package_tampering_poisoned() {
        let t = Temp::new();
        let mut h = host(&t);
        mutate(&t, |a| a.package.bytes.push(1));
        assert_eq!(h.reopen(&Auth).unwrap(), GrainCustodyStatus::Poisoned(CustodyPoisonReason::Package));
    }
    #[test]
    fn one_ahead_recovery() {
        let t = Temp::new();
        let mut h = host(&t);
        h.checkpoint([(b"x".to_vec(), vec![1])].into(), &Auth).unwrap();
        drop(h);
        let mut h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.status(), &GrainCustodyStatus::RecoveryRequired);
        h.recover_one_ahead(&Auth).unwrap();
        assert_eq!(h.status(), &GrainCustodyStatus::Ready);
    }
    #[test]
    fn two_ahead_refused() {
        let t = Temp::new();
        let mut h = host(&t);
        mutate(&t, |a| {
            a.previous = Some(a.anchor.clone());
            a.anchor.generation += 2;
            a.transition = a.transition_digest();
            a.anchor.receipt_head = a.transition;
            a.transition_signature = Auth.sign(&a.transition);
        });
        assert_eq!(h.reopen(&Auth).unwrap(), GrainCustodyStatus::Poisoned(CustodyPoisonReason::Divergence));
    }
    #[test]
    fn settlement_crash_replay_once() {
        let t = Temp::new();
        let h = host(&t);
        let r = SettlementRecord::new(h.lease().unwrap().clone(), 0).unwrap();
        durable_write(&t.0, "settlement.json", &r).unwrap();
        drop(h);
        let mut h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.settle_or_replay(0, &Auth).unwrap(), r.receipt);
        drop(h);
        let mut h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.settle_or_replay(0, &Auth).unwrap(), r.receipt);
        assert_eq!(h.lease().unwrap().remaining(), 90);
        h.settle_or_replay(1, &Auth).unwrap();
        assert_eq!(h.lease().unwrap().remaining(), 80);
    }
    #[test]
    fn settlement_archive_ahead_replay_once() {
        let t = Temp::new();
        let mut h = host(&t);
        let r = SettlementRecord::new(h.lease().unwrap().clone(), 0).unwrap();
        durable_write(&t.0, "settlement.json", &r).unwrap();
        let mut a = h.next_archive().unwrap();
        a.lease = r.after.clone();
        a.settlements.push(r.clone());
        h.persist_archive(a, &Auth).unwrap();
        drop(h);
        let mut h = GrainCustodyHost::open(&t.0, [7; 32], &Auth).unwrap();
        assert_eq!(h.settle_or_replay(0, &Auth).unwrap(), r.receipt);
        assert_eq!(h.lease().unwrap().remaining(), 90);
    }
    #[test]
    fn ingress_omission_substitution_and_prefix_rewrite_refused() {
        let mut log = AriadneIngressLog::default();
        let t = log.commit([1; 32], [7; 32], &Auth);
        log.commit([2; 32], [7; 32], &Auth);
        let trace = vec![(0, [1; 32]), (1, [2; 32])];
        assert!(log.verify_non_omission(&t, [7; 32], &Auth, &trace, log.root()));
        assert!(!log.verify_non_omission(&t, [7; 32], &Auth, &trace[1..], log.root()));
        assert!(!log.verify_non_omission(&t, [7; 32], &Auth, &[(0, [9; 32]), (1, [2; 32])], log.root()));
        log.leaves[0] = [9; 32];
        assert!(!log.verify_non_omission(&t, [7; 32], &Auth, &trace, log.root()));
    }
    #[test]
    fn executor_policy_substitution_refused() {
        let t = Temp::new();
        let mut h = host(&t);
        let p = test_program();
        let mut e = GrainExecutor::new(GrainBudget::default(), GrainCapabilities::allow_all(&[]));
        let r = turn_request_digest(&p, &[], &e);
        let ticket = h.commit_ingress(r, [7; 32], &Auth.sign(&r), &Auth).unwrap();
        e.budget.max_fuel += 1;
        assert!(matches!(h.execute_turn(&ticket, &p, &[], &e, &[], &Auth), Err(CustodyError::RequestMismatch)));
    }
    #[test]
    fn unsigned_program_swap_refused() {
        let t = Temp::new();
        let mut h = host(&t);
        let p = GrainProgram::new("swapped", vec![GrainOp::Halt]);
        let e = GrainExecutor::new(GrainBudget::default(), GrainCapabilities::allow_all(&[]));
        let r = turn_request_digest(&p, &[], &e);
        let ticket = h.commit_ingress(r, [7; 32], &Auth.sign(&r), &Auth).unwrap();
        assert!(matches!(h.execute_turn(&ticket, &p, &[], &e, &[], &Auth), Err(CustodyError::RequestMismatch)));
    }
    #[test]
    fn retained_anchor_detects_local_rollback() {
        let t = Temp::new();
        let mut h = host(&t);
        let old = read_json::<Archive>(&t.0.join("archive.json")).unwrap().unwrap();
        h.checkpoint([(vec![1], vec![2])].into(), &Auth).unwrap();
        h.recover_one_ahead(&Auth).unwrap();
        let retained = h.anchor().unwrap().clone();
        drop(h);
        durable_write(&t.0, "archive.json", &old).unwrap();
        durable_write(&t.0, "anchor.json", &old.anchor).unwrap();
        let h = GrainCustodyHost::open_at(&t.0, [7; 32], retained, &Auth).unwrap();
        assert_eq!(h.status(), &GrainCustodyStatus::Poisoned(CustodyPoisonReason::Rollback));
    }
    #[test]
    fn child_receipt_chain_survives_turns_and_detects_forgery() {
        let mut p = parent();
        let root = p.checkpoint_root();
        let (mut a, b) = p.fork_two(spec(2, 20), spec(3, 20)).unwrap();
        let r = a.execute(&test_program(), &[], GrainBudget::default());
        assert_eq!(r.termination, GrainTermination::CapabilityDenied);
        assert!(a.verify_receipt_chain(root));
        assert!(b.verify_receipt_chain(root));
        assert!(!a.verify_receipt_chain([9; 32]));
        a.turn_receipts[0] = [9; 32];
        assert!(!a.verify_receipt_chain(root));
    }
    #[test]
    fn exclusive_writer_lock() {
        let t = Temp::new();
        let _h = host(&t);
        assert!(matches!(GrainCustodyHost::open(&t.0, [7; 32], &Auth), Err(CustodyError::Locked)));
    }
}
