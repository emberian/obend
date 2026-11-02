//! DreggNet `Grain` R0–R4 Deterministic Execution & Metering Ladder.
//!
//! Implements the deterministic stack/register bytecode & `.obend` cell-step evaluator
//! with strict per-instruction fuel charging, bounded linear memory pages, capability-checked
//! hostcall slots (`ReadSlot`, `EmitSlot`, `HashDigest`), and cryptographic execution receipts.

/// Standard linear memory page size (4 KiB) for `Grain` bytecode execution.
pub const GRAIN_PAGE_SIZE: usize = 4096;

/// Standard FIPS 180-4 SHA-256 round constants.
const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Compute exact FIPS 180-4 SHA-256 32-byte digest.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];

    let bit_len = (data.len() as u64) * 8;
    let mut padded = data.to_vec();
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0x00);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let mut a = h[0];
        let mut b = h[1];
        let mut c = h[2];
        let mut d = h[3];
        let mut e = h[4];
        let mut f = h[5];
        let mut g = h[6];
        let mut hh = h[7];

        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// DreggNet `Grain` R0–R4 Reproducibility & Metering Tier Ladder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReproducibilityTier {
    /// R0: Unmetered / unverified host process execution.
    R0Unverified,
    /// R1: OS-sandboxed & resource-metered child process (`bwrap` / `sandbox-exec`).
    R1MeteredProcess,
    /// R2: Deterministic fuel-metered `Grain` bytecode & `.obend` cell-step evaluation.
    R2DeterministicGrain,
    /// R3: Cryptographically receipt-attested deterministic execution.
    R3ReceiptAttested,
    /// R4: Lean 4 kernel-proved transition receipt (`ObendSession` verified).
    R4KernelProved,
}

impl ReproducibilityTier {
    pub fn tag_byte(&self) -> u8 {
        match self {
            Self::R0Unverified => 0,
            Self::R1MeteredProcess => 1,
            Self::R2DeterministicGrain => 2,
            Self::R3ReceiptAttested => 3,
            Self::R4KernelProved => 4,
        }
    }

    pub fn label(&self) -> &'static str {
        match self {
            Self::R0Unverified => "R0:Unverified",
            Self::R1MeteredProcess => "R1:MeteredProcess",
            Self::R2DeterministicGrain => "R2:DeterministicGrain",
            Self::R3ReceiptAttested => "R3:ReceiptAttested",
            Self::R4KernelProved => "R4:KernelProved",
        }
    }

    pub fn is_deterministic(&self) -> bool {
        *self >= Self::R2DeterministicGrain
    }
}

/// Strict execution resource bounds for a `Grain` evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GrainBudget {
    pub max_fuel: u64,
    pub max_memory_bytes: usize,
    pub max_output_bytes: usize,
}

impl GrainBudget {
    pub fn new(max_fuel: u64, max_memory_bytes: usize, max_output_bytes: usize) -> Self {
        Self {
            max_fuel,
            max_memory_bytes,
            max_output_bytes,
        }
    }
}

impl Default for GrainBudget {
    fn default() -> Self {
        Self {
            max_fuel: 10_000,
            max_memory_bytes: 64 * 1024,
            max_output_bytes: 16 * 1024,
        }
    }
}

/// Deterministic termination status of a `Grain` evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrainTermination {
    Halted,
    OutOfFuel,
    MemoryLimitExceeded,
    CapabilityDenied,
}

impl GrainTermination {
    pub fn is_halted(&self) -> bool {
        matches!(self, Self::Halted)
    }
}

/// Compact deterministic stack/register bytecode & `.obend` cell-step instruction set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrainOp {
    /// No-op (1 fuel).
    Nop,
    /// Push a 64-bit signed immediate onto the operand stack (1 fuel).
    PushImm(i64),
    /// Pop the top of the operand stack into register `reg` (`0..16`) (1 fuel).
    StoreReg(u8),
    /// Push register `reg` (`0..16`) onto the operand stack (1 fuel).
    LoadReg(u8),
    /// Pop `b` then `a`, push `a.wrapping_add(b)` (1 fuel).
    Add,
    /// Pop `b` then `a`, push `a.wrapping_sub(b)` (1 fuel).
    Sub,
    /// Pop `b` then `a`, push `a.wrapping_mul(b)` (2 fuel).
    Mul,
    /// Pop `b` then `a`, push `a ^ b` (1 fuel).
    Xor,
    /// Allocate or grow bounded linear memory by `pages` (`pages * GRAIN_PAGE_SIZE` bytes).
    AllocPages(usize),
    /// Write `data` into bounded linear memory at `offset`.
    StoreLinear { offset: usize, data: Vec<u8> },
    /// Read `len` bytes from bounded linear memory at `offset` and push their folded `i64` value.
    LoadLinear { offset: usize, len: usize },
    /// Capability-checked hostcall: read input slot `slot_id` into linear memory and push byte length.
    ReadSlot(u64),
    /// Capability-checked hostcall: emit output payload to slot `slot_id`.
    EmitSlot { slot_id: u64, data: Vec<u8> },
    /// Capability-checked hostcall: compute SHA-256 digest over current memory and emitted slots.
    HashDigest,
    /// Evaluate an `.obend` cell-step expression and emit the resulting cell bytes to `slot_id`.
    EvalCellStep { slot_id: u64, expression: String },
    /// Conditional relative forward jump by `offset` instructions if top of stack is non-zero.
    JumpIfNonZero(usize),
    /// Deterministic halt (1 fuel).
    Halt,
}

impl GrainOp {
    /// Strict per-instruction fuel cost.
    pub fn fuel_cost(&self) -> u64 {
        match self {
            Self::Nop
            | Self::PushImm(_)
            | Self::StoreReg(_)
            | Self::LoadReg(_)
            | Self::Add
            | Self::Sub
            | Self::Xor
            | Self::JumpIfNonZero(_)
            | Self::Halt => 1,
            Self::Mul => 2,
            Self::AllocPages(pages) => 2u64.saturating_add((*pages as u64).min(16).saturating_mul(4)),
            Self::StoreLinear { data, .. } => 2u64.saturating_add((data.len() as u64) / 32),
            Self::LoadLinear { len, .. } => 2u64.saturating_add((*len as u64) / 32),
            Self::ReadSlot(_) => 5,
            Self::EmitSlot { data, .. } => 5u64.saturating_add((data.len() as u64) / 32),
            Self::HashDigest => 10,
            Self::EvalCellStep { expression, .. } => {
                8u64.saturating_add((expression.len() as u64) / 16)
            }
        }
    }

    /// Encode instruction into canonical bytes for program digest calculation.
    pub fn encode_canonical(&self, out: &mut Vec<u8>) {
        match self {
            Self::Nop => out.push(0x00),
            Self::PushImm(v) => {
                out.push(0x01);
                out.extend_from_slice(&v.to_be_bytes());
            }
            Self::StoreReg(r) => {
                out.push(0x02);
                out.push(*r);
            }
            Self::LoadReg(r) => {
                out.push(0x03);
                out.push(*r);
            }
            Self::Add => out.push(0x04),
            Self::Sub => out.push(0x05),
            Self::Mul => out.push(0x06),
            Self::Xor => out.push(0x07),
            Self::AllocPages(p) => {
                out.push(0x08);
                out.extend_from_slice(&(*p as u64).to_be_bytes());
            }
            Self::StoreLinear { offset, data } => {
                out.push(0x09);
                out.extend_from_slice(&(*offset as u64).to_be_bytes());
                out.extend_from_slice(&(data.len() as u64).to_be_bytes());
                out.extend_from_slice(data);
            }
            Self::LoadLinear { offset, len } => {
                out.push(0x0A);
                out.extend_from_slice(&(*offset as u64).to_be_bytes());
                out.extend_from_slice(&(*len as u64).to_be_bytes());
            }
            Self::ReadSlot(slot) => {
                out.push(0x0B);
                out.extend_from_slice(&slot.to_be_bytes());
            }
            Self::EmitSlot { slot_id, data } => {
                out.push(0x0C);
                out.extend_from_slice(&slot_id.to_be_bytes());
                out.extend_from_slice(&(data.len() as u64).to_be_bytes());
                out.extend_from_slice(data);
            }
            Self::HashDigest => out.push(0x0D),
            Self::EvalCellStep {
                slot_id,
                expression,
            } => {
                out.push(0x0E);
                out.extend_from_slice(&slot_id.to_be_bytes());
                let bytes = expression.as_bytes();
                out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
                out.extend_from_slice(bytes);
            }
            Self::JumpIfNonZero(offset) => {
                out.push(0x0F);
                out.extend_from_slice(&(*offset as u64).to_be_bytes());
            }
            Self::Halt => out.push(0xFF),
        }
    }
}

/// Deterministic `Grain` bytecode program and `.obend` cell-step representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainProgram {
    pub name: String,
    pub ops: Vec<GrainOp>,
}

impl GrainProgram {
    pub fn new(name: impl Into<String>, ops: Vec<GrainOp>) -> Self {
        Self {
            name: name.into(),
            ops,
        }
    }

    /// Parse an `.obend` cell-step script into a deterministic `GrainProgram`.
    ///
    /// Supported directives (one per line or semicolon-separated):
    /// - `nop`
    /// - `push <i64>`
    /// - `store_reg <u8>`
    /// - `load_reg <u8>`
    /// - `add` | `sub` | `mul` | `xor`
    /// - `alloc_pages <usize>`
    /// - `read_slot <u64>`
    /// - `emit_slot <u64> <utf8_payload>`
    /// - `hash_digest`
    /// - `cell_step <u64> <expression>`
    /// - `jnz <usize>`
    /// - `halt`
    pub fn from_obend_cell(name: impl Into<String>, source: &str) -> Result<Self, String> {
        let mut ops = Vec::new();
        for (line_idx, raw_stmt) in source.split(['\n', ';']).enumerate() {
            let stmt = raw_stmt.trim();
            if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("--") {
                continue;
            }
            let stmt = stmt
                .strip_prefix('(')
                .and_then(|s| s.strip_suffix(')'))
                .map(str::trim)
                .unwrap_or(stmt);

            let mut parts = stmt.splitn(3, char::is_whitespace);
            let Some(cmd) = parts.next() else {
                continue;
            };
            let arg1 = parts.next().map(str::trim);
            let arg2 = parts.next().map(str::trim);

            let op = match cmd {
                "nop" => GrainOp::Nop,
                "push" => {
                    let v = arg1
                        .ok_or_else(|| format!("line {}: push requires immediate", line_idx + 1))?
                        .parse::<i64>()
                        .map_err(|e| format!("line {}: invalid i64: {e}", line_idx + 1))?;
                    GrainOp::PushImm(v)
                }
                "store_reg" | "store-reg" => {
                    let r = arg1
                        .ok_or_else(|| format!("line {}: store_reg requires reg", line_idx + 1))?
                        .parse::<u8>()
                        .map_err(|e| format!("line {}: invalid reg: {e}", line_idx + 1))?;
                    GrainOp::StoreReg(r)
                }
                "load_reg" | "load-reg" => {
                    let r = arg1
                        .ok_or_else(|| format!("line {}: load_reg requires reg", line_idx + 1))?
                        .parse::<u8>()
                        .map_err(|e| format!("line {}: invalid reg: {e}", line_idx + 1))?;
                    GrainOp::LoadReg(r)
                }
                "add" => GrainOp::Add,
                "sub" => GrainOp::Sub,
                "mul" => GrainOp::Mul,
                "xor" => GrainOp::Xor,
                "alloc_pages" | "alloc-pages" => {
                    let p = arg1
                        .ok_or_else(|| {
                            format!("line {}: alloc_pages requires count", line_idx + 1)
                        })?
                        .parse::<usize>()
                        .map_err(|e| format!("line {}: invalid page count: {e}", line_idx + 1))?;
                    GrainOp::AllocPages(p)
                }
                "read_slot" | "read-slot" => {
                    let slot = arg1
                        .ok_or_else(|| format!("line {}: read_slot requires slot", line_idx + 1))?
                        .parse::<u64>()
                        .map_err(|e| format!("line {}: invalid slot id: {e}", line_idx + 1))?;
                    GrainOp::ReadSlot(slot)
                }
                "emit_slot" | "emit-slot" => {
                    let slot = arg1
                        .ok_or_else(|| format!("line {}: emit_slot requires slot", line_idx + 1))?
                        .parse::<u64>()
                        .map_err(|e| format!("line {}: invalid slot id: {e}", line_idx + 1))?;
                    let payload = arg2.unwrap_or("").as_bytes().to_vec();
                    GrainOp::EmitSlot {
                        slot_id: slot,
                        data: payload,
                    }
                }
                "hash_digest" | "hash-digest" | "hash" => GrainOp::HashDigest,
                "cell_step" | "cell-step" | "cell" => {
                    let slot = arg1
                        .ok_or_else(|| format!("line {}: cell_step requires slot", line_idx + 1))?
                        .parse::<u64>()
                        .map_err(|e| format!("line {}: invalid slot id: {e}", line_idx + 1))?;
                    let expr = arg2.unwrap_or("0").to_string();
                    GrainOp::EvalCellStep {
                        slot_id: slot,
                        expression: expr,
                    }
                }
                "jnz" => {
                    let off = arg1
                        .ok_or_else(|| format!("line {}: jnz requires offset", line_idx + 1))?
                        .parse::<usize>()
                        .map_err(|e| format!("line {}: invalid offset: {e}", line_idx + 1))?;
                    GrainOp::JumpIfNonZero(off)
                }
                "halt" => GrainOp::Halt,
                other => {
                    return Err(format!(
                        "line {}: unknown .obend grain op '{other}'",
                        line_idx + 1
                    ));
                }
            };
            ops.push(op);
        }
        Ok(Self {
            name: name.into(),
            ops,
        })
    }

    /// Compute the deterministic SHA-256 digest over program name and bytecode instructions.
    pub fn digest(&self) -> [u8; 32] {
        let mut buf = Vec::new();
        buf.extend_from_slice(b"OBEND-GRAIN-PROGRAM-V1:");
        let name_bytes = self.name.as_bytes();
        buf.extend_from_slice(&(name_bytes.len() as u64).to_be_bytes());
        buf.extend_from_slice(name_bytes);
        buf.extend_from_slice(&(self.ops.len() as u64).to_be_bytes());
        for op in &self.ops {
            op.encode_canonical(&mut buf);
        }
        sha256(&buf)
    }
}

/// Capability policy governing hostcall slot access during `Grain` execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainCapabilities {
    pub allowed_read_slots: Vec<u64>,
    pub allowed_emit_slots: Vec<u64>,
    pub allow_hash_digest: bool,
}

impl GrainCapabilities {
    pub fn strict(
        allowed_read_slots: Vec<u64>,
        allowed_emit_slots: Vec<u64>,
        allow_hash_digest: bool,
    ) -> Self {
        Self {
            allowed_read_slots,
            allowed_emit_slots,
            allow_hash_digest,
        }
    }

    pub fn allow_all(slots: &[u64]) -> Self {
        Self {
            allowed_read_slots: slots.to_vec(),
            allowed_emit_slots: slots.to_vec(),
            allow_hash_digest: true,
        }
    }

    pub fn can_read_slot(&self, slot_id: u64) -> bool {
        self.allowed_read_slots.contains(&slot_id)
    }

    pub fn can_emit_slot(&self, slot_id: u64) -> bool {
        self.allowed_emit_slots.contains(&slot_id)
    }
}

impl Default for GrainCapabilities {
    fn default() -> Self {
        Self {
            allowed_read_slots: Vec::new(),
            allowed_emit_slots: Vec::new(),
            allow_hash_digest: true,
        }
    }
}

/// Cryptographic commitment receipt over a deterministic `Grain` execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainExecutionReceipt {
    pub program_digest: [u8; 32],
    pub input_digest: [u8; 32],
    pub output_digest: [u8; 32],
    pub fuel_consumed: u64,
    pub peak_memory_bytes: usize,
    pub tier: ReproducibilityTier,
    pub termination: GrainTermination,
    pub commitment: [u8; 32],
    pub emitted_slots: Vec<(u64, Vec<u8>)>,
    pub stack_top: Option<i64>,
    pub registers: [i64; 16],
    pub last_hash_digest: [u8; 32],
}

impl GrainExecutionReceipt {
    /// Compute the SHA-256 commitment over `(program_digest, input_digest, output_digest, fuel_consumed, peak_memory_bytes, tier)`.
    pub fn compute_commitment(
        program_digest: &[u8; 32],
        input_digest: &[u8; 32],
        output_digest: &[u8; 32],
        fuel_consumed: u64,
        peak_memory_bytes: usize,
        tier: ReproducibilityTier,
    ) -> [u8; 32] {
        let mut buf = Vec::with_capacity(32 * 3 + 8 + 8 + 1 + 28);
        buf.extend_from_slice(b"OBEND-GRAIN-RECEIPT-COMMIT:");
        buf.extend_from_slice(program_digest);
        buf.extend_from_slice(input_digest);
        buf.extend_from_slice(output_digest);
        buf.extend_from_slice(&fuel_consumed.to_be_bytes());
        buf.extend_from_slice(&(peak_memory_bytes as u64).to_be_bytes());
        buf.push(tier.tag_byte());
        sha256(&buf)
    }

    /// Verify that `self.commitment` matches the canonical SHA-256 commitment over the receipt fields.
    pub fn verify_commitment(&self) -> bool {
        let expected = Self::compute_commitment(
            &self.program_digest,
            &self.input_digest,
            &self.output_digest,
            self.fuel_consumed,
            self.peak_memory_bytes,
            self.tier,
        );
        self.commitment == expected
    }

    /// Promote a halted deterministic grain receipt to `R3ReceiptAttested` or `R4KernelProved` and refresh commitment.
    pub fn promote_tier(&mut self, new_tier: ReproducibilityTier) -> bool {
        if !self.termination.is_halted() || new_tier < self.tier {
            return false;
        }
        self.tier = new_tier;
        self.commitment = Self::compute_commitment(
            &self.program_digest,
            &self.input_digest,
            &self.output_digest,
            self.fuel_consumed,
            self.peak_memory_bytes,
            self.tier,
        );
        true
    }
}

/// Compute canonical SHA-256 digest over `(slot_id, bytes)` pairs.
pub fn digest_slot_entries(domain: &[u8], entries: &[(u64, Vec<u8>)]) -> [u8; 32] {
    let mut buf = Vec::new();
    buf.extend_from_slice(domain);
    buf.extend_from_slice(&(entries.len() as u64).to_be_bytes());
    for (slot_id, data) in entries {
        buf.extend_from_slice(&slot_id.to_be_bytes());
        buf.extend_from_slice(&(data.len() as u64).to_be_bytes());
        buf.extend_from_slice(data);
    }
    sha256(&buf)
}

/// Deterministic `Grain` R2–R4 Fuel Executor.
#[derive(Clone, Debug)]
pub struct GrainExecutor {
    pub budget: GrainBudget,
    pub capabilities: GrainCapabilities,
    pub tier: ReproducibilityTier,
}

impl GrainExecutor {
    pub fn new(budget: GrainBudget, capabilities: GrainCapabilities) -> Self {
        Self {
            budget,
            capabilities,
            tier: ReproducibilityTier::R2DeterministicGrain,
        }
    }

    pub fn with_tier(mut self, tier: ReproducibilityTier) -> Self {
        self.tier = tier;
        self
    }

    /// Execute a `GrainProgram` deterministically against `input_slots` under strict fuel, memory, and capability bounds.
    pub fn execute(
        &self,
        program: &GrainProgram,
        input_slots: &[(u64, Vec<u8>)],
    ) -> GrainExecutionReceipt {
        let program_digest = program.digest();
        let input_digest = digest_slot_entries(b"OBEND-GRAIN-INPUTS-V1:", input_slots);

        let mut stack: Vec<i64> = Vec::new();
        let mut registers = [0i64; 16];
        let mut linear_memory: Vec<u8> = Vec::new();
        let mut emitted_slots: Vec<(u64, Vec<u8>)> = Vec::new();
        let mut emitted_bytes_total: usize = 0;
        let mut fuel_consumed: u64 = 0;
        let mut peak_memory_bytes: usize = 0;
        let mut last_hash_digest = [0u8; 32];
        let mut termination = GrainTermination::Halted;

        let mut pc: usize = 0;
        while pc < program.ops.len() {
            let op = &program.ops[pc];
            let cost = op.fuel_cost();
            match fuel_consumed.checked_add(cost) {
                Some(next_fuel) if next_fuel <= self.budget.max_fuel => {
                    fuel_consumed = next_fuel;
                }
                _ => {
                    fuel_consumed = self.budget.max_fuel;
                    termination = GrainTermination::OutOfFuel;
                    break;
                }
            }

            match op {
                GrainOp::Nop => {
                    pc += 1;
                }
                GrainOp::PushImm(val) => {
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    let total_mem = linear_memory.len().saturating_add(stack_bytes);
                    if total_mem > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    stack.push(*val);
                    peak_memory_bytes = peak_memory_bytes.max(total_mem);
                    pc += 1;
                }
                GrainOp::StoreReg(reg) => {
                    let idx = (*reg as usize) & 0x0F;
                    registers[idx] = stack.pop().unwrap_or(0);
                    pc += 1;
                }
                GrainOp::LoadReg(reg) => {
                    let idx = (*reg as usize) & 0x0F;
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    let total_mem = linear_memory.len().saturating_add(stack_bytes);
                    if total_mem > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    stack.push(registers[idx]);
                    peak_memory_bytes = peak_memory_bytes.max(total_mem);
                    pc += 1;
                }
                GrainOp::Add => {
                    let b = stack.pop().unwrap_or(0);
                    let a = stack.pop().unwrap_or(0);
                    stack.push(a.wrapping_add(b));
                    pc += 1;
                }
                GrainOp::Sub => {
                    let b = stack.pop().unwrap_or(0);
                    let a = stack.pop().unwrap_or(0);
                    stack.push(a.wrapping_sub(b));
                    pc += 1;
                }
                GrainOp::Mul => {
                    let b = stack.pop().unwrap_or(0);
                    let a = stack.pop().unwrap_or(0);
                    stack.push(a.wrapping_mul(b));
                    pc += 1;
                }
                GrainOp::Xor => {
                    let b = stack.pop().unwrap_or(0);
                    let a = stack.pop().unwrap_or(0);
                    stack.push(a ^ b);
                    pc += 1;
                }
                GrainOp::AllocPages(pages) => {
                    let Some(add_bytes) = pages.checked_mul(GRAIN_PAGE_SIZE) else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    let Some(new_len) = linear_memory.len().checked_add(add_bytes) else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    let stack_bytes = stack.len() * std::mem::size_of::<i64>();
                    if new_len.saturating_add(stack_bytes) > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    linear_memory.resize(new_len, 0u8);
                    peak_memory_bytes =
                        peak_memory_bytes.max(linear_memory.len().saturating_add(stack_bytes));
                    pc += 1;
                }
                GrainOp::StoreLinear { offset, data } => {
                    let Some(end) = offset.checked_add(data.len()) else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    let stack_bytes = stack.len() * std::mem::size_of::<i64>();
                    let required = end.max(linear_memory.len());
                    if required.saturating_add(stack_bytes) > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    if end > linear_memory.len() {
                        linear_memory.resize(end, 0u8);
                    }
                    linear_memory[*offset..end].copy_from_slice(data);
                    peak_memory_bytes =
                        peak_memory_bytes.max(linear_memory.len().saturating_add(stack_bytes));
                    pc += 1;
                }
                GrainOp::LoadLinear { offset, len } => {
                    let Some(end) = offset.checked_add(*len) else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    let required = end.max(linear_memory.len());
                    if required.saturating_add(stack_bytes) > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    if end > linear_memory.len() {
                        linear_memory.resize(end, 0u8);
                    }
                    let mut acc = 0i64;
                    for &b in &linear_memory[*offset..end] {
                        acc = acc.rotate_left(8) ^ (b as i64);
                    }
                    stack.push(acc);
                    peak_memory_bytes =
                        peak_memory_bytes.max(linear_memory.len().saturating_add(stack_bytes));
                    pc += 1;
                }
                GrainOp::ReadSlot(slot_id) => {
                    if !self.capabilities.can_read_slot(*slot_id) {
                        termination = GrainTermination::CapabilityDenied;
                        break;
                    }
                    let payload = input_slots
                        .iter()
                        .find(|(id, _)| id == slot_id)
                        .map(|(_, bytes)| bytes.as_slice())
                        .unwrap_or(&[]);

                    let Some(new_len) = linear_memory.len().checked_add(payload.len()) else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    if new_len.saturating_add(stack_bytes) > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    linear_memory.extend_from_slice(payload);
                    let mut folded = payload.len() as i64;
                    for &b in payload {
                        folded = folded.wrapping_mul(257).wrapping_add(b as i64);
                    }
                    stack.push(folded);
                    registers[0] = payload.len() as i64;
                    peak_memory_bytes =
                        peak_memory_bytes.max(linear_memory.len().saturating_add(stack_bytes));
                    pc += 1;
                }
                GrainOp::EmitSlot { slot_id, data } => {
                    if !self.capabilities.can_emit_slot(*slot_id) {
                        termination = GrainTermination::CapabilityDenied;
                        break;
                    }
                    let Some(next_output_bytes) = emitted_bytes_total.checked_add(data.len())
                    else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    if next_output_bytes > self.budget.max_output_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    let stack_bytes = stack.len() * std::mem::size_of::<i64>();
                    let total_mem = linear_memory
                        .len()
                        .saturating_add(stack_bytes)
                        .saturating_add(next_output_bytes);
                    if total_mem > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    emitted_bytes_total = next_output_bytes;
                    emitted_slots.push((*slot_id, data.clone()));
                    peak_memory_bytes = peak_memory_bytes.max(total_mem);
                    pc += 1;
                }
                GrainOp::HashDigest => {
                    if !self.capabilities.allow_hash_digest {
                        termination = GrainTermination::CapabilityDenied;
                        break;
                    }
                    let mut hash_input = Vec::new();
                    hash_input.extend_from_slice(b"OBEND-GRAIN-HOSTHASH:");
                    hash_input.extend_from_slice(&linear_memory);
                    for (slot_id, bytes) in &emitted_slots {
                        hash_input.extend_from_slice(&slot_id.to_be_bytes());
                        hash_input.extend_from_slice(bytes);
                    }
                    let digest = sha256(&hash_input);
                    last_hash_digest = digest;
                    let low64 = i64::from_be_bytes([
                        digest[0], digest[1], digest[2], digest[3], digest[4], digest[5],
                        digest[6], digest[7],
                    ]);
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    let total_mem = linear_memory.len().saturating_add(stack_bytes);
                    if total_mem > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    stack.push(low64);
                    peak_memory_bytes = peak_memory_bytes.max(total_mem);
                    pc += 1;
                }
                GrainOp::EvalCellStep {
                    slot_id,
                    expression,
                } => {
                    if !self.capabilities.can_emit_slot(*slot_id) {
                        termination = GrainTermination::CapabilityDenied;
                        break;
                    }
                    let cell_val =
                        Self::eval_cell_expression(expression, &stack, &registers, input_slots);
                    let cell_bytes = format!("cell:{}:{}:{}", slot_id, expression.trim(), cell_val)
                        .into_bytes();
                    let Some(next_output_bytes) =
                        emitted_bytes_total.checked_add(cell_bytes.len())
                    else {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    };
                    if next_output_bytes > self.budget.max_output_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    let stack_bytes = (stack.len() + 1) * std::mem::size_of::<i64>();
                    let total_mem = linear_memory
                        .len()
                        .saturating_add(stack_bytes)
                        .saturating_add(next_output_bytes);
                    if total_mem > self.budget.max_memory_bytes {
                        termination = GrainTermination::MemoryLimitExceeded;
                        break;
                    }
                    emitted_bytes_total = next_output_bytes;
                    emitted_slots.push((*slot_id, cell_bytes));
                    stack.push(cell_val);
                    peak_memory_bytes = peak_memory_bytes.max(total_mem);
                    pc += 1;
                }
                GrainOp::JumpIfNonZero(offset) => {
                    let cond = stack.pop().unwrap_or(0);
                    if cond != 0 && *offset > 0 {
                        pc = pc.saturating_add(*offset);
                    } else {
                        pc += 1;
                    }
                }
                GrainOp::Halt => {
                    termination = GrainTermination::Halted;
                    break;
                }
            }
        }

        let mut output_buf = Vec::new();
        output_buf.extend_from_slice(& digest_slot_entries(b"OBEND-GRAIN-OUTPUTS-V1:", &emitted_slots));
        output_buf.extend_from_slice(&stack.last().copied().unwrap_or(0).to_be_bytes());
        for r in &registers {
            output_buf.extend_from_slice(&r.to_be_bytes());
        }
        output_buf.extend_from_slice(&last_hash_digest);
        output_buf.push(match termination {
            GrainTermination::Halted => 0,
            GrainTermination::OutOfFuel => 1,
            GrainTermination::MemoryLimitExceeded => 2,
            GrainTermination::CapabilityDenied => 3,
        });
        let output_digest = sha256(&output_buf);

        let commitment = GrainExecutionReceipt::compute_commitment(
            &program_digest,
            &input_digest,
            &output_digest,
            fuel_consumed,
            peak_memory_bytes,
            self.tier,
        );

        GrainExecutionReceipt {
            program_digest,
            input_digest,
            output_digest,
            fuel_consumed,
            peak_memory_bytes,
            tier: self.tier,
            termination,
            commitment,
            emitted_slots,
            stack_top: stack.last().copied(),
            registers,
            last_hash_digest,
        }
    }

    fn eval_cell_expression(
        expr: &str,
        stack: &[i64],
        registers: &[i64; 16],
        inputs: &[(u64, Vec<u8>)],
    ) -> i64 {
        let mut acc = stack.last().copied().unwrap_or(0);
        for token in expr.split_whitespace() {
            if let Ok(imm) = token.parse::<i64>() {
                acc = acc.wrapping_add(imm);
            } else if let Some(reg_str) = token.strip_prefix('r') {
                if let Ok(idx) = reg_str.parse::<usize>() {
                    acc = acc.wrapping_add(registers[idx & 0x0F]);
                }
            } else if let Some(slot_str) = token.strip_prefix("slot:") {
                if let Ok(slot_id) = slot_str.parse::<u64>() {
                    if let Some((_, bytes)) = inputs.iter().find(|(id, _)| *id == slot_id) {
                        acc = acc.wrapping_add(bytes.len() as i64);
                    }
                }
            } else {
                for b in token.bytes() {
                    acc = acc.wrapping_mul(31).wrapping_add(b as i64);
                }
            }
        }
        acc
    }
}

// =========================================================================
// Policy-to-Grain Automata Confinement Compiler & VM (`Obend.Lower.PolicyToGrain`)
// =========================================================================

/// Deterministic Table-DFA transcript policy matching `Obend.Judge.TableDfa` (`AutomataConfinement.lean`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyTableDfa {
    pub start: usize,
    pub accepting: Vec<usize>,
    pub transitions: Vec<((usize, String), usize)>,
    pub state_defaults: Vec<(usize, usize)>,
    pub default_sink: usize,
}

impl PolicyTableDfa {
    /// Step from state `q` on token `tok` matching `TableDfa.step` / `grainStepToken`.
    pub fn step(&self, q: usize, tok: &str) -> usize {
        grain_step_token(
            &self.transitions,
            &self.state_defaults,
            self.default_sink,
            q,
            tok,
        )
    }

    /// Classify a token stream starting from state `q` matching `dfaClassifyFrom`.
    pub fn classify_from<S: AsRef<str>>(&self, mut q: usize, tokens: &[S]) -> usize {
        for tok in tokens {
            q = self.step(q, tok.as_ref());
        }
        q
    }

    /// Classify a token stream starting from `self.start` matching `dfaClassify`.
    pub fn classify<S: AsRef<str>>(&self, tokens: &[S]) -> usize {
        self.classify_from(self.start, tokens)
    }

    /// Check whether `self` accepts `tokens` matching `dfaAccepts`.
    pub fn accepts<S: AsRef<str>>(&self, tokens: &[S]) -> bool {
        let final_state = self.classify(tokens);
        self.accepting.contains(&final_state)
    }

    /// Canonical injection-confinement DFA matching `Obend.Judge.confinementDfa`.
    pub fn confinement_dfa() -> Self {
        Self {
            start: 0,
            accepting: vec![0],
            transitions: vec![
                ((0, "{{".to_string()), 1),
                ((0, "}}".to_string()), 1),
                ((0, "<|system|>".to_string()), 1),
                ((0, "<|assistant|>".to_string()), 1),
                ((0, "<|user|>".to_string()), 1),
            ],
            state_defaults: vec![(0, 0), (1, 1)],
            default_sink: 1,
        }
    }
}

/// Deterministic register/stack `Grain` bytecode instructions for transcript policy evaluation
/// matching `Obend.Lower.GrainInstr` (`PolicyToGrain.lean`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyGrainInstr {
    /// Initialize `state_reg := start_state` and `fuel_reg := fuel_budget`.
    InitState {
        start_state: usize,
        fuel_budget: usize,
    },
    /// Load the DFA transition table `(transitions, state_defaults, default_sink)` into VM registers.
    LoadTable {
        transitions: Vec<((usize, String), usize)>,
        state_defaults: Vec<(usize, usize)>,
        default_sink: usize,
    },
    /// Scan the input token stream through the loaded transition table.
    ScanTokens { max_tokens: usize },
    /// Check whether `state_reg` is in `accept_states` and push the boolean verdict onto the stack.
    CheckAccept { accept_states: Vec<usize> },
    /// Halt execution and expose the top of the verdict stack.
    Halt,
}

/// Explicit linear fuel budget `2 * max_tokens + 4` matching `Obend.Lower.grainPolicyFuelBudget`.
#[inline]
pub fn grain_policy_fuel_budget(max_tokens: usize) -> usize {
    2 * max_tokens + 4
}

/// Compile a `PolicyTableDfa` transcript policy with token budget `max_tokens` into a
/// `Vec<PolicyGrainInstr>` bytecode program matching `Obend.Lower.compilePolicyToGrainProg`.
pub fn compile_policy_to_grain_prog(
    policy: &PolicyTableDfa,
    max_tokens: usize,
) -> Vec<PolicyGrainInstr> {
    vec![
        PolicyGrainInstr::InitState {
            start_state: policy.start,
            fuel_budget: grain_policy_fuel_budget(max_tokens),
        },
        PolicyGrainInstr::LoadTable {
            transitions: policy.transitions.clone(),
            state_defaults: policy.state_defaults.clone(),
            default_sink: policy.default_sink,
        },
        PolicyGrainInstr::ScanTokens { max_tokens },
        PolicyGrainInstr::CheckAccept {
            accept_states: policy.accepting.clone(),
        },
        PolicyGrainInstr::Halt,
    ]
}

/// Deterministic state of the `Grain` policy VM matching `Obend.Lower.GrainVmState`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PolicyGrainVmState {
    pub state_reg: usize,
    pub fuel_reg: usize,
    pub transitions_reg: Vec<((usize, String), usize)>,
    pub state_defaults_reg: Vec<(usize, usize)>,
    pub default_sink_reg: usize,
    pub verdict_stack: Vec<bool>,
    pub halted: bool,
}

/// Single-token transition step on the VM's table registers matching `Obend.Lower.grainStepToken`.
pub fn grain_step_token(
    transitions: &[((usize, String), usize)],
    state_defaults: &[(usize, usize)],
    default_sink: usize,
    q: usize,
    tok: &str,
) -> usize {
    if let Some((_, next)) = transitions
        .iter()
        .find(|((s, t), _)| *s == q && t.as_str() == tok)
    {
        *next
    } else if let Some((_, def_next)) = state_defaults.iter().find(|(s, _)| *s == q) {
        *def_next
    } else {
        default_sink
    }
}

/// Deterministic token scan loop over the VM's table registers matching `Obend.Lower.grainScanLoop`.
pub fn grain_scan_loop<S: AsRef<str>>(
    transitions: &[((usize, String), usize)],
    state_defaults: &[(usize, usize)],
    default_sink: usize,
    mut q: usize,
    tokens: &[S],
) -> usize {
    for tok in tokens {
        q = grain_step_token(transitions, state_defaults, default_sink, q, tok.as_ref());
    }
    q
}

/// Execute one `PolicyGrainInstr` against `vm` and `tokens` matching `Obend.Lower.stepGrainInstr`.
pub fn step_policy_grain_instr<S: AsRef<str>>(
    mut vm: PolicyGrainVmState,
    tokens: &[S],
    instr: &PolicyGrainInstr,
) -> Option<PolicyGrainVmState> {
    match instr {
        PolicyGrainInstr::InitState {
            start_state,
            fuel_budget,
        } => {
            if *fuel_budget < 4 {
                None
            } else {
                vm.state_reg = *start_state;
                vm.fuel_reg = *fuel_budget;
                Some(vm)
            }
        }
        PolicyGrainInstr::LoadTable {
            transitions,
            state_defaults,
            default_sink,
        } => {
            if vm.fuel_reg == 0 {
                None
            } else {
                vm.transitions_reg = transitions.clone();
                vm.state_defaults_reg = state_defaults.clone();
                vm.default_sink_reg = *default_sink;
                vm.fuel_reg -= 1;
                Some(vm)
            }
        }
        PolicyGrainInstr::ScanTokens { max_tokens } => {
            let scan_cost = 2 * tokens.len().min(*max_tokens) + 1;
            if vm.fuel_reg < scan_cost {
                None
            } else {
                vm.state_reg = grain_scan_loop(
                    &vm.transitions_reg,
                    &vm.state_defaults_reg,
                    vm.default_sink_reg,
                    vm.state_reg,
                    tokens,
                );
                vm.fuel_reg -= scan_cost;
                Some(vm)
            }
        }
        PolicyGrainInstr::CheckAccept { accept_states } => {
            if vm.fuel_reg == 0 {
                None
            } else {
                let accepted = accept_states.contains(&vm.state_reg);
                vm.verdict_stack.insert(0, accepted);
                vm.fuel_reg -= 1;
                Some(vm)
            }
        }
        PolicyGrainInstr::Halt => {
            if vm.fuel_reg == 0 {
                None
            } else {
                vm.halted = true;
                vm.fuel_reg -= 1;
                Some(vm)
            }
        }
    }
}

/// Execute a sequence of `PolicyGrainInstr` instructions matching `Obend.Lower.runGrainInstrs`.
pub fn run_policy_grain_instrs<S: AsRef<str>>(
    mut vm: PolicyGrainVmState,
    tokens: &[S],
    prog: &[PolicyGrainInstr],
) -> Option<PolicyGrainVmState> {
    for instr in prog {
        if vm.halted {
            return Some(vm);
        }
        vm = step_policy_grain_instr(vm, tokens, instr)?;
    }
    Some(vm)
}

/// Evaluate a `PolicyGrainInstr` bytecode program on `tokens`, returning `Some(verdict)` on clean halt
/// matching `Obend.Lower.evalGrainProg` (`compilePolicyToGrainProg_sound`).
pub fn eval_policy_grain_prog<S: AsRef<str>>(
    prog: &[PolicyGrainInstr],
    tokens: &[S],
) -> Option<bool> {
    let vm = run_policy_grain_instrs(PolicyGrainVmState::default(), tokens, prog)?;
    if vm.halted {
        vm.verdict_stack.first().copied()
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_grain_deterministic_execution_and_receipt_commitment() {
        let prog = GrainProgram::new(
            "arith_and_emit",
            vec![
                GrainOp::ReadSlot(1),
                GrainOp::PushImm(40),
                GrainOp::PushImm(2),
                GrainOp::Add,
                GrainOp::StoreReg(3),
                GrainOp::LoadReg(3),
                GrainOp::EmitSlot {
                    slot_id: 2,
                    data: b"answer-42".to_vec(),
                },
                GrainOp::HashDigest,
                GrainOp::Halt,
            ],
        );

        let budget = GrainBudget::new(500, 16 * 1024, 4096);
        let caps = GrainCapabilities::strict(vec![1], vec![2], true);
        let exec = GrainExecutor::new(budget, caps);
        let inputs = vec![(1u64, b"genesis-input-slot-1".to_vec())];

        let r1 = exec.execute(&prog, &inputs);
        let r2 = exec.execute(&prog, &inputs);

        assert_eq!(r1, r2);
        assert_eq!(r1.termination, GrainTermination::Halted);
        assert_eq!(r1.tier, ReproducibilityTier::R2DeterministicGrain);
        assert_eq!(r1.registers[3], 42);
        assert_eq!(r1.emitted_slots, vec![(2u64, b"answer-42".to_vec())]);
        assert!(r1.fuel_consumed > 0 && r1.fuel_consumed <= budget.max_fuel);
        assert!(r1.peak_memory_bytes > 0 && r1.peak_memory_bytes <= budget.max_memory_bytes);
        assert!(r1.verify_commitment());

        // Tier promotion R2 -> R3 -> R4 updates commitment deterministically
        let mut attested = r1.clone();
        assert!(attested.promote_tier(ReproducibilityTier::R3ReceiptAttested));
        assert_eq!(attested.tier, ReproducibilityTier::R3ReceiptAttested);
        assert_ne!(attested.commitment, r1.commitment);
        assert!(attested.verify_commitment());

        assert!(attested.promote_tier(ReproducibilityTier::R4KernelProved));
        assert_eq!(attested.tier, ReproducibilityTier::R4KernelProved);
        assert!(attested.verify_commitment());
    }

    #[test]
    fn test_grain_out_of_fuel_enforcement() {
        let prog = GrainProgram::new(
            "fuel_exhaustion",
            vec![
                GrainOp::PushImm(10),
                GrainOp::PushImm(20),
                GrainOp::Mul,
                GrainOp::HashDigest,
                GrainOp::Halt,
            ],
        );
        // Total fuel needed is 1 + 1 + 2 + 10 + 1 = 15; cap budget at 3
        let budget = GrainBudget::new(3, 8192, 1024);
        let caps = GrainCapabilities::allow_all(&[]);
        let exec = GrainExecutor::new(budget, caps);

        let receipt = exec.execute(&prog, &[]);
        assert_eq!(receipt.termination, GrainTermination::OutOfFuel);
        assert_eq!(receipt.fuel_consumed, 3);
        assert!(receipt.verify_commitment());
        // Cannot promote a non-halted receipt
        let mut copy = receipt.clone();
        assert!(!copy.promote_tier(ReproducibilityTier::R3ReceiptAttested));
    }

    #[test]
    fn test_grain_memory_and_output_limit_enforcement() {
        // 1. Linear page allocation exceeding max_memory_bytes
        let alloc_prog = GrainProgram::new(
            "oom_pages",
            vec![GrainOp::AllocPages(4), GrainOp::Halt],
        );
        let budget = GrainBudget::new(1000, GRAIN_PAGE_SIZE * 2, 1024);
        let exec = GrainExecutor::new(budget, GrainCapabilities::allow_all(&[1]));
        let r_oom = exec.execute(&alloc_prog, &[]);
        assert_eq!(r_oom.termination, GrainTermination::MemoryLimitExceeded);
        assert!(r_oom.verify_commitment());

        // 2. Output emission exceeding max_output_bytes
        let emit_prog = GrainProgram::new(
            "oversized_emit",
            vec![
                GrainOp::EmitSlot {
                    slot_id: 1,
                    data: vec![0xAA; 128],
                },
                GrainOp::Halt,
            ],
        );
        let tight_out_budget = GrainBudget::new(1000, 16 * 1024, 64);
        let exec_out = GrainExecutor::new(tight_out_budget, GrainCapabilities::allow_all(&[1]));
        let r_out = exec_out.execute(&emit_prog, &[]);
        assert_eq!(r_out.termination, GrainTermination::MemoryLimitExceeded);
        assert!(r_out.emitted_slots.is_empty());
    }

    #[test]
    fn test_grain_capability_denied_on_unauthorized_slots_and_hash() {
        let caps = GrainCapabilities::strict(vec![1], vec![2], false);
        let budget = GrainBudget::default();
        let exec = GrainExecutor::new(budget, caps);

        // Unauthorized ReadSlot(99)
        let bad_read = GrainProgram::new("bad_read", vec![GrainOp::ReadSlot(99), GrainOp::Halt]);
        assert_eq!(
            exec.execute(&bad_read, &[]).termination,
            GrainTermination::CapabilityDenied
        );

        // Unauthorized EmitSlot(99)
        let bad_emit = GrainProgram::new(
            "bad_emit",
            vec![
                GrainOp::EmitSlot {
                    slot_id: 99,
                    data: vec![1, 2, 3],
                },
                GrainOp::Halt,
            ],
        );
        assert_eq!(
            exec.execute(&bad_emit, &[]).termination,
            GrainTermination::CapabilityDenied
        );

        // Unauthorized HashDigest when allow_hash_digest == false
        let bad_hash = GrainProgram::new("bad_hash", vec![GrainOp::HashDigest, GrainOp::Halt]);
        assert_eq!(
            exec.execute(&bad_hash, &[]).termination,
            GrainTermination::CapabilityDenied
        );
    }

    #[test]
    fn test_obend_cell_step_script_parser_and_evaluator() {
        let script = r#"
            # Sample .obend cell-step script
            read_slot 1
            push 100
            store_reg 1
            load_reg 1
            push 23
            add
            cell_step 2 r1 slot:1 7
            emit_slot 2 committed-cell-v1
            hash_digest
            halt
        "#;
        let prog = GrainProgram::from_obend_cell("cell_step_demo", script)
            .expect("parse .obend cell script");
        let exec = GrainExecutor::new(
            GrainBudget::default(),
            GrainCapabilities::strict(vec![1], vec![2], true),
        );
        let receipt = exec.execute(&prog, &[(1, b"abcde".to_vec())]);
        assert_eq!(receipt.termination, GrainTermination::Halted);
        assert_eq!(receipt.emitted_slots.len(), 2);
        assert_eq!(receipt.emitted_slots[1], (2, b"committed-cell-v1".to_vec()));
        assert!(receipt.verify_commitment());
    }

    #[test]
    fn test_grain_edge_cases_empty_overflow_and_parse_errors() {
        // 1. Empty program on zero-fuel budget halts cleanly with 0 fuel and 0 memory
        let empty_prog = GrainProgram::new("empty", vec![]);
        let zero_exec = GrainExecutor::new(GrainBudget::new(0, 0, 0), GrainCapabilities::default());
        let r_empty = zero_exec.execute(&empty_prog, &[]);
        assert_eq!(r_empty.termination, GrainTermination::Halted);
        assert_eq!(r_empty.fuel_consumed, 0);
        assert_eq!(r_empty.peak_memory_bytes, 0);
        assert_eq!(r_empty.stack_top, None);
        assert!(r_empty.verify_commitment());

        // 2. Non-empty program on zero-fuel budget terminates with OutOfFuel immediately
        let one_op = GrainProgram::new("one_op", vec![GrainOp::Nop]);
        let r_zero_fuel = zero_exec.execute(&one_op, &[]);
        assert_eq!(r_zero_fuel.termination, GrainTermination::OutOfFuel);
        assert_eq!(r_zero_fuel.fuel_consumed, 0);

        // 3. Overflow boundary values on AllocPages(usize::MAX) and StoreLinear(usize::MAX)
        let exec = GrainExecutor::new(
            GrainBudget::new(100_000, 64 * 1024, 4096),
            GrainCapabilities::default(),
        );
        let overflow_pages =
            GrainProgram::new("overflow_pages", vec![GrainOp::AllocPages(usize::MAX)]);
        assert_eq!(
            exec.execute(&overflow_pages, &[]).termination,
            GrainTermination::MemoryLimitExceeded
        );
        let overflow_store = GrainProgram::new(
            "overflow_store",
            vec![GrainOp::StoreLinear {
                offset: usize::MAX,
                data: vec![1, 2],
            }],
        );
        assert_eq!(
            exec.execute(&overflow_store, &[]).termination,
            GrainTermination::MemoryLimitExceeded
        );

        // 4. Malformed .obend script error paths
        assert!(GrainProgram::from_obend_cell("bad_op", "unknown_instruction 1").is_err());
        assert!(GrainProgram::from_obend_cell("missing_imm", "push").is_err());
        assert!(GrainProgram::from_obend_cell("bad_imm", "push not_a_number").is_err());
    }

    #[test]
    fn test_policy_to_grain_compiler_and_vm_soundness() {
        let policy = PolicyTableDfa {
            start: 0,
            accepting: vec![2],
            transitions: vec![
                ((0, "HDR".to_string()), 1),
                ((1, "SLOT:api_key".to_string()), 2),
            ],
            state_defaults: vec![],
            default_sink: 99,
        };
        let prog = compile_policy_to_grain_prog(&policy, 4);
        assert_eq!(prog.len(), 5);

        let accept_tokens = vec!["HDR".to_string(), "SLOT:api_key".to_string()];
        let reject_tokens = vec!["HDR".to_string(), "INJECTED".to_string()];

        assert_eq!(
            eval_policy_grain_prog(&prog, &accept_tokens),
            Some(policy.accepts(&accept_tokens))
        );
        assert_eq!(eval_policy_grain_prog(&prog, &accept_tokens), Some(true));

        assert_eq!(
            eval_policy_grain_prog(&prog, &reject_tokens),
            Some(policy.accepts(&reject_tokens))
        );
        assert_eq!(eval_policy_grain_prog(&prog, &reject_tokens), Some(false));

        // Confinement DFA test
        let conf_dfa = PolicyTableDfa::confinement_dfa();
        let conf_prog = compile_policy_to_grain_prog(&conf_dfa, 8);
        assert_eq!(
            eval_policy_grain_prog(&conf_prog, &["hello", "world"]),
            Some(true)
        );
        assert_eq!(
            eval_policy_grain_prog(&conf_prog, &["hello", "{{", "world"]),
            Some(false)
        );

        // Insufficient fuel (< 4) in InitState returns None
        let bad_prog = vec![
            PolicyGrainInstr::InitState {
                start_state: 0,
                fuel_budget: 3,
            },
            PolicyGrainInstr::Halt,
        ];
        assert_eq!(eval_policy_grain_prog(&bad_prog, &accept_tokens), None);
    }
}

