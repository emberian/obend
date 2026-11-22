#![forbid(unsafe_code)]
//! Deterministic Fuel- & Memory-Metered Core WebAssembly Sandbox (`CAP-23` Remediation).
//!
//! Replaces `breadstuffs/dregg-sandbox/src/lib.rs:364-375` (which instantiated `wasmi` with
//! zero fuel cap, zero memory limiter, and zero wall-clock timeout, allowing `(loop (br 0))` to
//! wedge host worker threads indefinitely) with a pure-Rust, zero-`unsafe`, empty-linker
//! WebAssembly 1.0 binary (`\0asm\x01\0\0\0`) validator and fuel-metered interpreter.

use std::fmt;
use std::time::{Duration, Instant};

use crate::grain::{ReproducibilityTier, sha256};

/// Standard WebAssembly linear memory page size (`64 KiB`).
pub const WASM_PAGE_SIZE: usize = 65_536;

/// Sandbox capability grade (`dregg-sandbox` `CapTier`), ordered weakest to strongest.
/// Unserved tiers fail closed (`WasmRunError::TierNotServed`) rather than silently downgrading.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum WasmCapTier {
    Sandboxed,
    JitSandboxed,
    Caged,
    MicroVm,
    Gpu,
}

impl WasmCapTier {
    pub fn is_served(self) -> bool {
        matches!(self, Self::Sandboxed)
    }
}

/// Structural egress posture for a workload run at [`WasmCapTier`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EgressPosture {
    /// Empty host linker: any module declaring imports is rejected at load time.
    DenyByConstruction,
    NoEngineNoEgress,
}

pub fn wasm_egress_posture(tier: WasmCapTier) -> EgressPosture {
    match tier {
        WasmCapTier::Sandboxed => EgressPosture::DenyByConstruction,
        _ => EgressPosture::NoEngineNoEgress,
    }
}

/// Strict execution resource budget for a confined WebAssembly module (`CAP-23` fix).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmExecutionBudget {
    pub max_fuel: u64,
    pub max_memory_bytes: usize,
    pub max_stack_values: usize,
    pub max_call_depth: usize,
    pub max_wall_time: Option<Duration>,
}

impl Default for WasmExecutionBudget {
    fn default() -> Self {
        Self {
            max_fuel: 100_000,
            max_memory_bytes: 16 * WASM_PAGE_SIZE, // 1 MiB default
            max_stack_values: 4096,
            max_call_depth: 64,
            max_wall_time: Some(Duration::from_secs(2)),
        }
    }
}

impl WasmExecutionBudget {
    pub fn new(max_fuel: u64, max_memory_bytes: usize) -> Self {
        Self {
            max_fuel,
            max_memory_bytes,
            ..Self::default()
        }
    }

    pub fn validate(&self) -> Result<(), WasmRunError> {
        if self.max_fuel == 0 {
            return Err(WasmRunError::InvalidBudget(
                "max_fuel must be > 0 (unbounded/zero fuel prohibited by CAP-23)".into(),
            ));
        }
        if self.max_memory_bytes == 0 {
            return Err(WasmRunError::InvalidBudget(
                "max_memory_bytes must be > 0".into(),
            ));
        }
        if self.max_stack_values == 0 || self.max_call_depth == 0 {
            return Err(WasmRunError::InvalidBudget(
                "max_stack_values and max_call_depth must be > 0".into(),
            ));
        }
        Ok(())
    }
}

/// Core-Wasm numeric value (`i32` / `i64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmVal {
    I32(i32),
    I64(i64),
}

impl WasmVal {
    fn ty(self) -> ValType {
        match self {
            Self::I32(_) => ValType::I32,
            Self::I64(_) => ValType::I64,
        }
    }

    fn encode_canonical(self, out: &mut Vec<u8>) {
        match self {
            Self::I32(v) => {
                out.push(0x7F);
                out.extend_from_slice(&v.to_le_bytes());
            }
            Self::I64(v) => {
                out.push(0x7E);
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
    }
}

impl fmt::Display for WasmVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I32(v) => write!(f, "{v}"),
            Self::I64(v) => write!(f, "{v}"),
        }
    }
}

/// Errors produced by the fuel-metered WebAssembly sandbox.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmRunError {
    InvalidBudget(String),
    TierNotServed { tier: WasmCapTier, detail: String },
    InvalidModule(String),
    /// Empty-linker enforcement: any import (`env.*`, `wasi_*`, etc.) fails closed at load time!
    HostImportDenied { module: String, name: String },
    MissingExport(String),
    SignatureMismatch(String),
    OutOfFuel { max_fuel: u64, consumed: u64 },
    MemoryLimitExceeded { requested_bytes: usize, max_bytes: usize },
    StackOverflow,
    CallDepthExceeded { max_depth: usize },
    WallTimeoutExceeded { limit_ms: u64 },
    Trap(String),
}

impl fmt::Display for WasmRunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBudget(m) => write!(f, "invalid wasm budget: {m}"),
            Self::TierNotServed { tier, detail } => {
                write!(f, "wasm cap-tier {tier:?} not served: {detail}")
            }
            Self::InvalidModule(m) => write!(f, "invalid wasm module: {m}"),
            Self::HostImportDenied { module, name } => write!(
                f,
                "wasm host import `{module}.{name}` denied by empty-linker policy"
            ),
            Self::MissingExport(name) => write!(f, "wasm export `{name}` not found"),
            Self::SignatureMismatch(m) => write!(f, "wasm entrypoint signature mismatch: {m}"),
            Self::OutOfFuel { max_fuel, consumed } => {
                write!(f, "wasm execution exhausted fuel budget ({consumed}/{max_fuel})")
            }
            Self::MemoryLimitExceeded {
                requested_bytes,
                max_bytes,
            } => write!(
                f,
                "wasm memory request ({requested_bytes} B) exceeds budget ({max_bytes} B)"
            ),
            Self::StackOverflow => write!(f, "wasm operand stack limit exceeded"),
            Self::CallDepthExceeded { max_depth } => {
                write!(f, "wasm call depth exceeded max_call_depth ({max_depth})")
            }
            Self::WallTimeoutExceeded { limit_ms } => {
                write!(f, "wasm execution exceeded wall timeout ({limit_ms} ms)")
            }
            Self::Trap(m) => write!(f, "wasm trap: {m}"),
        }
    }
}

impl std::error::Error for WasmRunError {}

/// Deterministic execution receipt for a fuel-metered WebAssembly run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmExecutionReceipt {
    pub module_digest: [u8; 32],
    pub entrypoint: String,
    pub results: Vec<WasmVal>,
    pub fuel_consumed: u64,
    pub peak_memory_bytes: usize,
    pub tier: ReproducibilityTier,
    pub egress: EgressPosture,
    pub commitment: [u8; 32],
}

impl WasmExecutionReceipt {
    pub fn verify_commitment(&self, args: &[WasmVal]) -> bool {
        self.commitment
            == compute_wasm_commitment(
                &self.module_digest,
                &self.entrypoint,
                args,
                &self.results,
                self.fuel_consumed,
                self.peak_memory_bytes,
                self.tier,
            )
    }
}

fn compute_wasm_commitment(
    module_digest: &[u8; 32],
    entrypoint: &str,
    args: &[WasmVal],
    results: &[WasmVal],
    fuel_consumed: u64,
    peak_memory_bytes: usize,
    tier: ReproducibilityTier,
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(160);
    buf.extend_from_slice(b"OBEND-WASM-EXEC-RECEIPT-V1:");
    buf.extend_from_slice(module_digest);
    buf.extend_from_slice(&(entrypoint.len() as u64).to_be_bytes());
    buf.extend_from_slice(entrypoint.as_bytes());
    buf.extend_from_slice(&(args.len() as u64).to_be_bytes());
    for a in args {
        a.encode_canonical(&mut buf);
    }
    buf.extend_from_slice(&(results.len() as u64).to_be_bytes());
    for r in results {
        r.encode_canonical(&mut buf);
    }
    buf.extend_from_slice(&fuel_consumed.to_be_bytes());
    buf.extend_from_slice(&(peak_memory_bytes as u64).to_be_bytes());
    buf.push(tier.tag_byte());
    sha256(&buf)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValType {
    I32,
    I64,
}

#[derive(Debug, Clone)]
struct FuncType {
    params: Vec<ValType>,
    results: Vec<ValType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockKind {
    Func,
    Block,
    Loop,
    If,
}

#[derive(Debug, Clone)]
enum Insn {
    Unreachable,
    Nop,
    Block { arity: usize, end_pc: usize },
    Loop { start_pc: usize },
    If { arity: usize, else_pc: Option<usize>, end_pc: usize },
    Else { end_pc: usize },
    End,
    Br(u32),
    BrIf(u32),
    Return,
    Call(u32),
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    I32Load { offset: u32 },
    I64Load { offset: u32 },
    I32Store { offset: u32 },
    I64Store { offset: u32 },
    MemorySize,
    MemoryGrow,
    I32Const(i32),
    I64Const(i64),
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I64Add,
    I64Sub,
    I64Mul,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrU,
}

impl Insn {
    fn fuel_cost(&self) -> u64 {
        match self {
            Self::I32Mul | Self::I64Mul => 2,
            Self::I32DivS | Self::I32DivU | Self::I32RemS | Self::I32RemU => 3,
            Self::I32Load { .. }
            | Self::I64Load { .. }
            | Self::I32Store { .. }
            | Self::I64Store { .. } => 3,
            Self::Call(_) => 4,
            Self::MemoryGrow => 8,
            _ => 1,
        }
    }
}

#[derive(Debug, Clone)]
struct CompiledFunc {
    ty_idx: usize,
    extra_locals: Vec<ValType>,
    insns: Vec<Insn>,
}

#[derive(Debug, Clone)]
struct ParsedModule {
    types: Vec<FuncType>,
    funcs: Vec<CompiledFunc>,
    mem_initial_pages: usize,
    mem_max_pages: Option<usize>,
    globals: Vec<(ValType, bool, WasmVal)>,
    exports: Vec<(String, u8, u32)>,
    data_segments: Vec<(usize, Vec<u8>)>,
}

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn read_byte(&mut self) -> Result<u8, WasmRunError> {
        let b = *self
            .bytes
            .get(self.pos)
            .ok_or_else(|| WasmRunError::InvalidModule("unexpected EOF".into()))?;
        self.pos += 1;
        Ok(b)
    }

    fn read_slice(&mut self, n: usize) -> Result<&'a [u8], WasmRunError> {
        let end = self
            .pos
            .checked_add(n)
            .ok_or_else(|| WasmRunError::InvalidModule("slice overflow".into()))?;
        let s = self
            .bytes
            .get(self.pos..end)
            .ok_or_else(|| WasmRunError::InvalidModule("truncated section".into()))?;
        self.pos = end;
        Ok(s)
    }

    fn read_u32_leb(&mut self) -> Result<u32, WasmRunError> {
        let mut result = 0u32;
        for shift in (0..35).step_by(7) {
            let b = self.read_byte()?;
            if shift == 28 && (b & 0xF0) != 0 {
                return Err(WasmRunError::InvalidModule("u32 LEB128 overflow".into()));
            }
            result |= u32::from(b & 0x7F) << shift;
            if (b & 0x80) == 0 {
                return Ok(result);
            }
        }
        Err(WasmRunError::InvalidModule("unterminated u32 LEB128".into()))
    }

    fn read_i32_leb(&mut self) -> Result<i32, WasmRunError> {
        let mut result = 0i64;
        let mut shift = 0u32;
        loop {
            let b = self.read_byte()?;
            result |= i64::from(b & 0x7F) << shift;
            shift += 7;
            if (b & 0x80) == 0 {
                if shift < 64 && (b & 0x40) != 0 {
                    result |= !0i64 << shift;
                }
                return i32::try_from(result)
                    .map_err(|_| WasmRunError::InvalidModule("i32 LEB128 out of range".into()));
            }
            if shift >= 35 {
                return Err(WasmRunError::InvalidModule("i32 LEB128 too long".into()));
            }
        }
    }

    fn read_i64_leb(&mut self) -> Result<i64, WasmRunError> {
        let mut result = 0i128;
        let mut shift = 0u32;
        loop {
            let b = self.read_byte()?;
            result |= i128::from(b & 0x7F) << shift;
            shift += 7;
            if (b & 0x80) == 0 {
                if shift < 128 && (b & 0x40) != 0 {
                    result |= !0i128 << shift;
                }
                return i64::try_from(result)
                    .map_err(|_| WasmRunError::InvalidModule("i64 LEB128 out of range".into()));
            }
            if shift >= 70 {
                return Err(WasmRunError::InvalidModule("i64 LEB128 too long".into()));
            }
        }
    }

    fn read_name(&mut self) -> Result<String, WasmRunError> {
        let len = self.read_u32_leb()? as usize;
        if len > 4096 {
            return Err(WasmRunError::InvalidModule("identifier too long".into()));
        }
        let raw = self.read_slice(len)?;
        std::str::from_utf8(raw)
            .map(str::to_owned)
            .map_err(|_| WasmRunError::InvalidModule("invalid UTF-8 name".into()))
    }

    fn read_valtype(&mut self) -> Result<ValType, WasmRunError> {
        match self.read_byte()? {
            0x7F => Ok(ValType::I32),
            0x7E => Ok(ValType::I64),
            other => Err(WasmRunError::InvalidModule(format!(
                "unsupported wasm value type {other:#x} (core integer ABI only)"
            ))),
        }
    }
}

fn parse_wasm_module(bytes: &[u8]) -> Result<ParsedModule, WasmRunError> {
    if bytes.len() < 8 || &bytes[0..4] != b"\0asm" || bytes[4..8] != [1, 0, 0, 0] {
        return Err(WasmRunError::InvalidModule(
            "bad WebAssembly magic or version (expected \\0asm v1)".into(),
        ));
    }
    let mut cur = Cursor::new(&bytes[8..]);
    let mut types = Vec::new();
    let mut func_type_indices = Vec::new();
    let mut mem_initial_pages = 0usize;
    let mut mem_max_pages = None;
    let mut globals = Vec::new();
    let mut exports = Vec::new();
    let mut code_bodies: Vec<(Vec<ValType>, Vec<Insn>)> = Vec::new();
    let mut data_segments = Vec::new();
    let mut last_sec_id = 0u8;

    while !cur.is_eof() {
        let sec_id = cur.read_byte()?;
        let sec_len = cur.read_u32_leb()? as usize;
        let sec_bytes = cur.read_slice(sec_len)?;
        if sec_id != 0 {
            if sec_id <= last_sec_id {
                return Err(WasmRunError::InvalidModule("out-of-order or duplicate section".into()));
            }
            last_sec_id = sec_id;
        }
        let mut sc = Cursor::new(sec_bytes);
        match sec_id {
            0 => {} // custom section ignored safely
            1 => {
                let n = sc.read_u32_leb()? as usize;
                if n > 4096 {
                    return Err(WasmRunError::InvalidModule("too many types".into()));
                }
                for _ in 0..n {
                    if sc.read_byte()? != 0x60 {
                        return Err(WasmRunError::InvalidModule("expected 0x60 functype".into()));
                    }
                    let np = sc.read_u32_leb()? as usize;
                    if np > 64 {
                        return Err(WasmRunError::InvalidModule("too many params".into()));
                    }
                    let mut params = Vec::with_capacity(np);
                    for _ in 0..np {
                        params.push(sc.read_valtype()?);
                    }
                    let nr = sc.read_u32_leb()? as usize;
                    if nr > 16 {
                        return Err(WasmRunError::InvalidModule("too many results".into()));
                    }
                    let mut results = Vec::with_capacity(nr);
                    for _ in 0..nr {
                        results.push(sc.read_valtype()?);
                    }
                    types.push(FuncType { params, results });
                }
            }
            2 => {
                // Import section: empty-linker policy denies ALL host imports fail-closed!
                let n = sc.read_u32_leb()?;
                if n > 0 {
                    let module = sc.read_name().unwrap_or_else(|_| "<unknown>".into());
                    let name = sc.read_name().unwrap_or_else(|_| "<unknown>".into());
                    return Err(WasmRunError::HostImportDenied { module, name });
                }
            }
            3 => {
                let n = sc.read_u32_leb()? as usize;
                if n > 4096 {
                    return Err(WasmRunError::InvalidModule("too many functions".into()));
                }
                for _ in 0..n {
                    let idx = sc.read_u32_leb()? as usize;
                    if idx >= types.len() {
                        return Err(WasmRunError::InvalidModule("function type index OOB".into()));
                    }
                    func_type_indices.push(idx);
                }
            }
            4 => {
                let n = sc.read_u32_leb()?;
                for _ in 0..n {
                    let _elem = sc.read_byte()?;
                    let flags = sc.read_byte()?;
                    let _min = sc.read_u32_leb()?;
                    if (flags & 1) != 0 {
                        let _max = sc.read_u32_leb()?;
                    }
                }
            }
            5 => {
                let n = sc.read_u32_leb()?;
                if n > 1 {
                    return Err(WasmRunError::InvalidModule("multiple memories unsupported".into()));
                }
                if n == 1 {
                    let flags = sc.read_byte()?;
                    mem_initial_pages = sc.read_u32_leb()? as usize;
                    if (flags & 1) != 0 {
                        mem_max_pages = Some(sc.read_u32_leb()? as usize);
                    }
                }
            }
            6 => {
                let n = sc.read_u32_leb()? as usize;
                if n > 1024 {
                    return Err(WasmRunError::InvalidModule("too many globals".into()));
                }
                for _ in 0..n {
                    let vt = sc.read_valtype()?;
                    let mutable = sc.read_byte()? != 0;
                    let init_op = sc.read_byte()?;
                    let val = match (vt, init_op) {
                        (ValType::I32, 0x41) => WasmVal::I32(sc.read_i32_leb()?),
                        (ValType::I64, 0x42) => WasmVal::I64(sc.read_i64_leb()?),
                        _ => {
                            return Err(WasmRunError::InvalidModule(
                                "unsupported global init expr".into(),
                            ))
                        }
                    };
                    if sc.read_byte()? != 0x0B {
                        return Err(WasmRunError::InvalidModule("missing global end 0x0B".into()));
                    }
                    globals.push((vt, mutable, val));
                }
            }
            7 => {
                let n = sc.read_u32_leb()? as usize;
                if n > 4096 {
                    return Err(WasmRunError::InvalidModule("too many exports".into()));
                }
                for _ in 0..n {
                    let name = sc.read_name()?;
                    let kind = sc.read_byte()?;
                    let idx = sc.read_u32_leb()?;
                    exports.push((name, kind, idx));
                }
            }
            8 => {
                // Start section refused so side effects cannot bypass fuel-metered `run` call
                return Err(WasmRunError::InvalidModule(
                    "implicit start section prohibited; invoke exported entrypoint explicitly".into(),
                ));
            }
            10 => {
                let n = sc.read_u32_leb()? as usize;
                if n != func_type_indices.len() {
                    return Err(WasmRunError::InvalidModule(
                        "code section count != function section count".into(),
                    ));
                }
                for _ in 0..n {
                    let body_len = sc.read_u32_leb()? as usize;
                    let body_bytes = sc.read_slice(body_len)?;
                    code_bodies.push(parse_code_body(body_bytes)?);
                }
            }
            11 => {
                let n = sc.read_u32_leb()? as usize;
                if n > 1024 {
                    return Err(WasmRunError::InvalidModule("too many data segments".into()));
                }
                for _ in 0..n {
                    let mode = sc.read_u32_leb()?;
                    if mode != 0 {
                        return Err(WasmRunError::InvalidModule(
                            "only active memory-0 data segments supported".into(),
                        ));
                    }
                    if sc.read_byte()? != 0x41 {
                        return Err(WasmRunError::InvalidModule(
                            "data segment offset must be i32.const".into(),
                        ));
                    }
                    let offset = usize::try_from(sc.read_i32_leb()?)
                        .map_err(|_| WasmRunError::InvalidModule("negative data offset".into()))?;
                    if sc.read_byte()? != 0x0B {
                        return Err(WasmRunError::InvalidModule("missing data offset 0x0B".into()));
                    }
                    let dlen = sc.read_u32_leb()? as usize;
                    let dbytes = sc.read_slice(dlen)?.to_vec();
                    data_segments.push((offset, dbytes));
                }
            }
            _ => {}
        }
    }

    if func_type_indices.len() != code_bodies.len() {
        return Err(WasmRunError::InvalidModule("missing code section".into()));
    }
    let funcs = func_type_indices
        .into_iter()
        .zip(code_bodies)
        .map(|(ty_idx, (extra_locals, insns))| CompiledFunc {
            ty_idx,
            extra_locals,
            insns,
        })
        .collect();

    Ok(ParsedModule {
        types,
        funcs,
        mem_initial_pages,
        mem_max_pages,
        globals,
        exports,
        data_segments,
    })
}

fn parse_block_arity(cur: &mut Cursor<'_>, _types: &[FuncType]) -> Result<usize, WasmRunError> {
    let b = cur.read_byte()?;
    match b {
        0x40 => Ok(0),
        0x7F | 0x7E => Ok(1),
        other => Err(WasmRunError::InvalidModule(format!(
            "unsupported blocktype {other:#x}"
        ))),
    }
}

fn parse_code_body(bytes: &[u8]) -> Result<(Vec<ValType>, Vec<Insn>), WasmRunError> {
    let mut cur = Cursor::new(bytes);
    let local_groups = cur.read_u32_leb()? as usize;
    if local_groups > 256 {
        return Err(WasmRunError::InvalidModule("too many local groups".into()));
    }
    let mut locals = Vec::new();
    for _ in 0..local_groups {
        let count = cur.read_u32_leb()? as usize;
        if locals.len().saturating_add(count) > 4096 {
            return Err(WasmRunError::InvalidModule("too many locals".into()));
        }
        let vt = cur.read_valtype()?;
        locals.resize(locals.len() + count, vt);
    }

    let mut insns = Vec::new();
    // Stack of open control blocks: `(kind, insn_idx, optional_else_idx)`
    let mut ctl: Vec<(BlockKind, usize, Option<usize>)> = vec![(BlockKind::Func, usize::MAX, None)];

    while !cur.is_eof() {
        let op = cur.read_byte()?;
        match op {
            0x00 => insns.push(Insn::Unreachable),
            0x01 => insns.push(Insn::Nop),
            0x02 => {
                let arity = parse_block_arity(&mut cur, &[])?;
                let idx = insns.len();
                insns.push(Insn::Block { arity, end_pc: 0 });
                ctl.push((BlockKind::Block, idx, None));
            }
            0x03 => {
                let _arity = parse_block_arity(&mut cur, &[])?;
                let idx = insns.len();
                insns.push(Insn::Loop { start_pc: idx + 1 });
                ctl.push((BlockKind::Loop, idx, None));
            }
            0x04 => {
                let arity = parse_block_arity(&mut cur, &[])?;
                let idx = insns.len();
                insns.push(Insn::If {
                    arity,
                    else_pc: None,
                    end_pc: 0,
                });
                ctl.push((BlockKind::If, idx, None));
            }
            0x05 => {
                let Some((kind, if_idx, else_slot)) = ctl.last_mut() else {
                    return Err(WasmRunError::InvalidModule("unmatched else".into()));
                };
                if *kind != BlockKind::If || else_slot.is_some() {
                    return Err(WasmRunError::InvalidModule("invalid else placement".into()));
                }
                let else_idx = insns.len();
                insns.push(Insn::Else { end_pc: 0 });
                *else_slot = Some(else_idx);
                if let Insn::If { else_pc, .. } = &mut insns[*if_idx] {
                    *else_pc = Some(else_idx + 1);
                }
            }
            0x0B => {
                let Some((kind, start_idx, else_idx_opt)) = ctl.pop() else {
                    return Err(WasmRunError::InvalidModule("extra end opcode".into()));
                };
                let end_idx = insns.len();
                insns.push(Insn::End);
                match kind {
                    BlockKind::Func => {
                        if !cur.is_eof() {
                            return Err(WasmRunError::InvalidModule(
                                "trailing bytes after function end".into(),
                            ));
                        }
                        return Ok((locals, insns));
                    }
                    BlockKind::Block => {
                        if let Insn::Block { end_pc, .. } = &mut insns[start_idx] {
                            *end_pc = end_idx + 1;
                        }
                    }
                    BlockKind::Loop => {}
                    BlockKind::If => {
                        if let Insn::If { end_pc, .. } = &mut insns[start_idx] {
                            *end_pc = end_idx + 1;
                        }
                        if let Some(e_idx) = else_idx_opt {
                            if let Insn::Else { end_pc } = &mut insns[e_idx] {
                                *end_pc = end_idx + 1;
                            }
                        }
                    }
                }
            }
            0x0C => insns.push(Insn::Br(cur.read_u32_leb()?)),
            0x0D => insns.push(Insn::BrIf(cur.read_u32_leb()?)),
            0x0F => insns.push(Insn::Return),
            0x10 => insns.push(Insn::Call(cur.read_u32_leb()?)),
            0x1A => insns.push(Insn::Drop),
            0x1B => insns.push(Insn::Select),
            0x20 => insns.push(Insn::LocalGet(cur.read_u32_leb()?)),
            0x21 => insns.push(Insn::LocalSet(cur.read_u32_leb()?)),
            0x22 => insns.push(Insn::LocalTee(cur.read_u32_leb()?)),
            0x23 => insns.push(Insn::GlobalGet(cur.read_u32_leb()?)),
            0x24 => insns.push(Insn::GlobalSet(cur.read_u32_leb()?)),
            0x28 => {
                let _align = cur.read_u32_leb()?;
                insns.push(Insn::I32Load {
                    offset: cur.read_u32_leb()?,
                });
            }
            0x29 => {
                let _align = cur.read_u32_leb()?;
                insns.push(Insn::I64Load {
                    offset: cur.read_u32_leb()?,
                });
            }
            0x36 => {
                let _align = cur.read_u32_leb()?;
                insns.push(Insn::I32Store {
                    offset: cur.read_u32_leb()?,
                });
            }
            0x37 => {
                let _align = cur.read_u32_leb()?;
                insns.push(Insn::I64Store {
                    offset: cur.read_u32_leb()?,
                });
            }
            0x3F => {
                if cur.read_byte()? != 0 {
                    return Err(WasmRunError::InvalidModule("memory.size memidx != 0".into()));
                }
                insns.push(Insn::MemorySize);
            }
            0x40 => {
                if cur.read_byte()? != 0 {
                    return Err(WasmRunError::InvalidModule("memory.grow memidx != 0".into()));
                }
                insns.push(Insn::MemoryGrow);
            }
            0x41 => insns.push(Insn::I32Const(cur.read_i32_leb()?)),
            0x42 => insns.push(Insn::I64Const(cur.read_i64_leb()?)),
            0x45 => insns.push(Insn::I32Eqz),
            0x46 => insns.push(Insn::I32Eq),
            0x47 => insns.push(Insn::I32Ne),
            0x48 => insns.push(Insn::I32LtS),
            0x49 => insns.push(Insn::I32LtU),
            0x4A => insns.push(Insn::I32GtS),
            0x4B => insns.push(Insn::I32GtU),
            0x4C => insns.push(Insn::I32LeS),
            0x4D => insns.push(Insn::I32LeU),
            0x4E => insns.push(Insn::I32GeS),
            0x4F => insns.push(Insn::I32GeU),
            0x50 => insns.push(Insn::I64Eqz),
            0x51 => insns.push(Insn::I64Eq),
            0x52 => insns.push(Insn::I64Ne),
            0x53 => insns.push(Insn::I64LtS),
            0x54 => insns.push(Insn::I64LtU),
            0x55 => insns.push(Insn::I64GtS),
            0x56 => insns.push(Insn::I64GtU),
            0x6A => insns.push(Insn::I32Add),
            0x6B => insns.push(Insn::I32Sub),
            0x6C => insns.push(Insn::I32Mul),
            0x6D => insns.push(Insn::I32DivS),
            0x6E => insns.push(Insn::I32DivU),
            0x6F => insns.push(Insn::I32RemS),
            0x70 => insns.push(Insn::I32RemU),
            0x71 => insns.push(Insn::I32And),
            0x72 => insns.push(Insn::I32Or),
            0x73 => insns.push(Insn::I32Xor),
            0x74 => insns.push(Insn::I32Shl),
            0x75 => insns.push(Insn::I32ShrS),
            0x76 => insns.push(Insn::I32ShrU),
            0x7C => insns.push(Insn::I64Add),
            0x7D => insns.push(Insn::I64Sub),
            0x7E => insns.push(Insn::I64Mul),
            0x83 => insns.push(Insn::I64And),
            0x84 => insns.push(Insn::I64Or),
            0x85 => insns.push(Insn::I64Xor),
            0x86 => insns.push(Insn::I64Shl),
            0x88 => insns.push(Insn::I64ShrU),
            other => {
                return Err(WasmRunError::InvalidModule(format!(
                    "unsupported wasm opcode {other:#x}"
                )))
            }
        }
    }
    Err(WasmRunError::InvalidModule("unclosed function body".into()))
}

#[derive(Clone, Copy)]
struct Label {
    target_pc: usize,
    stack_height: usize,
    arity: usize,
    is_func: bool,
}

/// Execute an exported function (`"run"` by default) in a WebAssembly 1.0 module under strict
/// fuel, linear-memory, operand-stack, call-depth, and wall-clock bounds (`CAP-23` closed).
pub fn run_wasm_metered(
    tier: WasmCapTier,
    module_bytes: &[u8],
    entrypoint: &str,
    args: &[WasmVal],
    budget: &WasmExecutionBudget,
) -> Result<WasmExecutionReceipt, WasmRunError> {
    budget.validate()?;
    if !tier.is_served() {
        return Err(WasmRunError::TierNotServed {
            tier,
            detail: "only WasmCapTier::Sandboxed is served in-process; stronger tiers fail closed"
                .into(),
        });
    }

    let module_digest = sha256(module_bytes);
    let parsed = parse_wasm_module(module_bytes)?;

    let init_mem_bytes = parsed
        .mem_initial_pages
        .checked_mul(WASM_PAGE_SIZE)
        .ok_or(WasmRunError::MemoryLimitExceeded {
            requested_bytes: usize::MAX,
            max_bytes: budget.max_memory_bytes,
        })?;
    if init_mem_bytes > budget.max_memory_bytes {
        return Err(WasmRunError::MemoryLimitExceeded {
            requested_bytes: init_mem_bytes,
            max_bytes: budget.max_memory_bytes,
        });
    }
    let mut memory = vec![0u8; init_mem_bytes];
    for (off, data) in &parsed.data_segments {
        let end = off
            .checked_add(data.len())
            .ok_or_else(|| WasmRunError::InvalidModule("data segment overflow".into()))?;
        if end > memory.len() {
            return Err(WasmRunError::InvalidModule(
                "data segment out of initial memory bounds".into(),
            ));
        }
        memory[*off..end].copy_from_slice(data);
    }

    let mut globals: Vec<(bool, WasmVal)> = parsed
        .globals
        .iter()
        .map(|&(_, mutable, val)| (mutable, val))
        .collect();

    let func_idx = parsed
        .exports
        .iter()
        .find(|(name, kind, _)| name == entrypoint && *kind == 0)
        .map(|(_, _, idx)| *idx as usize)
        .ok_or_else(|| WasmRunError::MissingExport(entrypoint.to_string()))?;

    let entry_func = parsed
        .funcs
        .get(func_idx)
        .ok_or_else(|| WasmRunError::InvalidModule("export func index OOB".into()))?;
    let entry_ty = &parsed.types[entry_func.ty_idx];
    if args.len() != entry_ty.params.len()
        || args
            .iter()
            .zip(&entry_ty.params)
            .any(|(a, expected)| a.ty() != *expected)
    {
        return Err(WasmRunError::SignatureMismatch(format!(
            "expected {:?}, got {:?}",
            entry_ty.params, args
        )));
    }

    let start = Instant::now();
    let mut fuel_consumed = 0u64;
    let mut peak_memory_bytes = memory.len();
    let mut stack: Vec<WasmVal> = Vec::with_capacity(64);

    struct CallState<'a> {
        parsed: &'a ParsedModule,
        budget: &'a WasmExecutionBudget,
        start: Instant,
        fuel_consumed: &'a mut u64,
        peak_memory_bytes: &'a mut usize,
        memory: &'a mut Vec<u8>,
        globals: &'a mut [(bool, WasmVal)],
        stack: &'a mut Vec<WasmVal>,
    }

    fn exec_call(
        st: &mut CallState<'_>,
        func_idx: usize,
        call_args: Vec<WasmVal>,
        depth: usize,
    ) -> Result<(), WasmRunError> {
        if depth > st.budget.max_call_depth {
            return Err(WasmRunError::CallDepthExceeded {
                max_depth: st.budget.max_call_depth,
            });
        }
        let func = st
            .parsed
            .funcs
            .get(func_idx)
            .ok_or_else(|| WasmRunError::InvalidModule("call func index OOB".into()))?;
        let fty = &st.parsed.types[func.ty_idx];
        let mut locals = call_args;
        for &vt in &func.extra_locals {
            locals.push(match vt {
                ValType::I32 => WasmVal::I32(0),
                ValType::I64 => WasmVal::I64(0),
            });
        }

        let base_stack = st.stack.len();
        let mut labels = vec![Label {
            target_pc: func.insns.len(),
            stack_height: base_stack,
            arity: fty.results.len(),
            is_func: true,
        }];
        let mut pc = 0usize;
        let mut step_counter = 0u32;

        let pop_val = |stack: &mut Vec<WasmVal>| -> Result<WasmVal, WasmRunError> {
            stack
                .pop()
                .ok_or_else(|| WasmRunError::Trap("operand stack underflow".into()))
        };
        let pop_i32 = |stack: &mut Vec<WasmVal>| -> Result<i32, WasmRunError> {
            match pop_val(stack)? {
                WasmVal::I32(v) => Ok(v),
                _ => Err(WasmRunError::Trap("expected i32 on stack".into())),
            }
        };
        let pop_i64 = |stack: &mut Vec<WasmVal>| -> Result<i64, WasmRunError> {
            match pop_val(stack)? {
                WasmVal::I64(v) => Ok(v),
                _ => Err(WasmRunError::Trap("expected i64 on stack".into())),
            }
        };
        let push_val = |stack: &mut Vec<WasmVal>, v: WasmVal, limit: usize| -> Result<(), WasmRunError> {
            if stack.len() >= limit {
                return Err(WasmRunError::StackOverflow);
            }
            stack.push(v);
            Ok(())
        };

        while pc < func.insns.len() {
            step_counter = step_counter.wrapping_add(1);
            if (step_counter & 0xFF) == 0 {
                if let Some(limit) = st.budget.max_wall_time {
                    if st.start.elapsed() > limit {
                        return Err(WasmRunError::WallTimeoutExceeded {
                            limit_ms: limit.as_millis() as u64,
                        });
                    }
                }
            }

            let insn = &func.insns[pc];
            let cost = insn.fuel_cost();
            match st.fuel_consumed.checked_add(cost) {
                Some(next) if next <= st.budget.max_fuel => *st.fuel_consumed = next,
                _ => {
                    *st.fuel_consumed = st.budget.max_fuel;
                    return Err(WasmRunError::OutOfFuel {
                        max_fuel: st.budget.max_fuel,
                        consumed: st.budget.max_fuel,
                    });
                }
            }

            let unwind_branch = |depth_idx: u32,
                                 labels: &mut Vec<Label>,
                                 stack: &mut Vec<WasmVal>|
             -> Result<Option<usize>, WasmRunError> {
                let target_label_pos = labels
                    .len()
                    .checked_sub(1 + depth_idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("branch depth OOB".into()))?;
                let lbl = labels[target_label_pos];
                let mut kept = Vec::with_capacity(lbl.arity);
                for _ in 0..lbl.arity {
                    kept.push(pop_val(stack)?);
                }
                kept.reverse();
                stack.truncate(lbl.stack_height);
                stack.extend(kept);
                if lbl.is_func {
                    return Ok(None);
                }
                // For `loop`, target_pc is loop body start so keep the loop label on stack!
                if matches!(func.insns.get(lbl.target_pc.saturating_sub(1)), Some(Insn::Loop { .. })) {
                    labels.truncate(target_label_pos + 1);
                } else {
                    labels.truncate(target_label_pos);
                }
                Ok(Some(lbl.target_pc))
            };

            match *insn {
                Insn::Unreachable => return Err(WasmRunError::Trap("unreachable executed".into())),
                Insn::Nop => pc += 1,
                Insn::Block { arity, end_pc } => {
                    labels.push(Label {
                        target_pc: end_pc,
                        stack_height: st.stack.len(),
                        arity,
                        is_func: false,
                    });
                    pc += 1;
                }
                Insn::Loop { start_pc } => {
                    labels.push(Label {
                        target_pc: start_pc,
                        stack_height: st.stack.len(),
                        arity: 0,
                        is_func: false,
                    });
                    pc += 1;
                }
                Insn::If {
                    arity,
                    else_pc,
                    end_pc,
                } => {
                    let cond = pop_i32(st.stack)?;
                    if cond != 0 {
                        labels.push(Label {
                            target_pc: end_pc,
                            stack_height: st.stack.len(),
                            arity,
                            is_func: false,
                        });
                        pc += 1;
                    } else if let Some(epc) = else_pc {
                        labels.push(Label {
                            target_pc: end_pc,
                            stack_height: st.stack.len(),
                            arity,
                            is_func: false,
                        });
                        pc = epc;
                    } else {
                        pc = end_pc;
                    }
                }
                Insn::Else { end_pc } => {
                    labels.pop();
                    pc = end_pc;
                }
                Insn::End => {
                    let Some(lbl) = labels.pop() else {
                        break;
                    };
                    if lbl.is_func {
                        break;
                    }
                    pc += 1;
                }
                Insn::Br(d) => match unwind_branch(d, &mut labels, st.stack)? {
                    Some(next_pc) => pc = next_pc,
                    None => break,
                },
                Insn::BrIf(d) => {
                    let cond = pop_i32(st.stack)?;
                    if cond != 0 {
                        match unwind_branch(d, &mut labels, st.stack)? {
                            Some(next_pc) => pc = next_pc,
                            None => break,
                        }
                    } else {
                        pc += 1;
                    }
                }
                Insn::Return => {
                    let depth_to_func = (labels.len() - 1) as u32;
                    let _ = unwind_branch(depth_to_func, &mut labels, st.stack)?;
                    break;
                }
                Insn::Call(callee_idx) => {
                    let callee = st
                        .parsed
                        .funcs
                        .get(callee_idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("callee OOB".into()))?;
                    let cty = &st.parsed.types[callee.ty_idx];
                    let mut cargs = Vec::with_capacity(cty.params.len());
                    for _ in 0..cty.params.len() {
                        cargs.push(pop_val(st.stack)?);
                    }
                    cargs.reverse();
                    exec_call(st, callee_idx as usize, cargs, depth + 1)?;
                    pc += 1;
                }
                Insn::Drop => {
                    let _ = pop_val(st.stack)?;
                    pc += 1;
                }
                Insn::Select => {
                    let c = pop_i32(st.stack)?;
                    let v2 = pop_val(st.stack)?;
                    let v1 = pop_val(st.stack)?;
                    push_val(st.stack, if c != 0 { v1 } else { v2 }, st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::LocalGet(idx) => {
                    let v = *locals
                        .get(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.get OOB".into()))?;
                    push_val(st.stack, v, st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::LocalSet(idx) => {
                    let v = pop_val(st.stack)?;
                    let slot = locals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.set OOB".into()))?;
                    *slot = v;
                    pc += 1;
                }
                Insn::LocalTee(idx) => {
                    let v = *st
                        .stack
                        .last()
                        .ok_or_else(|| WasmRunError::Trap("stack underflow".into()))?;
                    let slot = locals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.tee OOB".into()))?;
                    *slot = v;
                    pc += 1;
                }
                Insn::GlobalGet(idx) => {
                    let (_, v) = *st
                        .globals
                        .get(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("global.get OOB".into()))?;
                    push_val(st.stack, v, st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::GlobalSet(idx) => {
                    let v = pop_val(st.stack)?;
                    let (mutable, slot) = st
                        .globals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("global.set OOB".into()))?;
                    if !*mutable {
                        return Err(WasmRunError::InvalidModule("immutable global.set".into()));
                    }
                    *slot = v;
                    pc += 1;
                }
                Insn::I32Load { offset } => {
                    let base = pop_i32(st.stack)? as u32 as usize;
                    let ea = base
                        .checked_add(offset as usize)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let bytes = st
                        .memory
                        .get(ea..ea.saturating_add(4))
                        .filter(|s| s.len() == 4)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let v = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                    push_val(st.stack, WasmVal::I32(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::I64Load { offset } => {
                    let base = pop_i32(st.stack)? as u32 as usize;
                    let ea = base
                        .checked_add(offset as usize)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let bytes = st
                        .memory
                        .get(ea..ea.saturating_add(8))
                        .filter(|s| s.len() == 8)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let v = i64::from_le_bytes([
                        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6],
                        bytes[7],
                    ]);
                    push_val(st.stack, WasmVal::I64(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::I32Store { offset } => {
                    let val = pop_i32(st.stack)?;
                    let base = pop_i32(st.stack)? as u32 as usize;
                    let ea = base
                        .checked_add(offset as usize)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let dst = st
                        .memory
                        .get_mut(ea..ea.saturating_add(4))
                        .filter(|s| s.len() == 4)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    dst.copy_from_slice(&val.to_le_bytes());
                    pc += 1;
                }
                Insn::I64Store { offset } => {
                    let val = pop_i64(st.stack)?;
                    let base = pop_i32(st.stack)? as u32 as usize;
                    let ea = base
                        .checked_add(offset as usize)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let dst = st
                        .memory
                        .get_mut(ea..ea.saturating_add(8))
                        .filter(|s| s.len() == 8)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    dst.copy_from_slice(&val.to_le_bytes());
                    pc += 1;
                }
                Insn::MemorySize => {
                    let pages = (st.memory.len() / WASM_PAGE_SIZE) as i32;
                    push_val(st.stack, WasmVal::I32(pages), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::MemoryGrow => {
                    let delta_pages = pop_i32(st.stack)? as u32 as usize;
                    let extra_fuel = (delta_pages as u64).saturating_mul(8);
                    match st.fuel_consumed.checked_add(extra_fuel) {
                        Some(nf) if nf <= st.budget.max_fuel => *st.fuel_consumed = nf,
                        _ => {
                            *st.fuel_consumed = st.budget.max_fuel;
                            return Err(WasmRunError::OutOfFuel {
                                max_fuel: st.budget.max_fuel,
                                consumed: st.budget.max_fuel,
                            });
                        }
                    }
                    let cur_pages = st.memory.len() / WASM_PAGE_SIZE;
                    let new_pages = cur_pages.saturating_add(delta_pages);
                    let new_bytes = new_pages.saturating_mul(WASM_PAGE_SIZE);
                    let max_pages_ok = st
                        .parsed
                        .mem_max_pages
                        .is_none_or(|mp| new_pages <= mp);
                    if !max_pages_ok || new_bytes > st.budget.max_memory_bytes {
                        push_val(st.stack, WasmVal::I32(-1), st.budget.max_stack_values)?;
                    } else {
                        st.memory.resize(new_bytes, 0u8);
                        *st.peak_memory_bytes = (*st.peak_memory_bytes).max(new_bytes);
                        push_val(
                            st.stack,
                            WasmVal::I32(cur_pages as i32),
                            st.budget.max_stack_values,
                        )?;
                    }
                    pc += 1;
                }
                Insn::I32Const(v) => {
                    push_val(st.stack, WasmVal::I32(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::I64Const(v) => {
                    push_val(st.stack, WasmVal::I64(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::I32Eqz => {
                    let a = pop_i32(st.stack)?;
                    push_val(
                        st.stack,
                        WasmVal::I32(i32::from(a == 0)),
                        st.budget.max_stack_values,
                    )?;
                    pc += 1;
                }
                Insn::I32Eq | Insn::I32Ne | Insn::I32LtS | Insn::I32LtU | Insn::I32GtS
                | Insn::I32GtU | Insn::I32LeS | Insn::I32LeU | Insn::I32GeS | Insn::I32GeU => {
                    let b = pop_i32(st.stack)?;
                    let a = pop_i32(st.stack)?;
                    let res = match insn {
                        Insn::I32Eq => a == b,
                        Insn::I32Ne => a != b,
                        Insn::I32LtS => a < b,
                        Insn::I32LtU => (a as u32) < (b as u32),
                        Insn::I32GtS => a > b,
                        Insn::I32GtU => (a as u32) > (b as u32),
                        Insn::I32LeS => a <= b,
                        Insn::I32LeU => (a as u32) <= (b as u32),
                        Insn::I32GeS => a >= b,
                        Insn::I32GeU => (a as u32) >= (b as u32),
                        _ => unreachable!(),
                    };
                    push_val(
                        st.stack,
                        WasmVal::I32(i32::from(res)),
                        st.budget.max_stack_values,
                    )?;
                    pc += 1;
                }
                Insn::I64Eqz => {
                    let a = pop_i64(st.stack)?;
                    push_val(
                        st.stack,
                        WasmVal::I32(i32::from(a == 0)),
                        st.budget.max_stack_values,
                    )?;
                    pc += 1;
                }
                Insn::I64Eq | Insn::I64Ne | Insn::I64LtS | Insn::I64LtU | Insn::I64GtS
                | Insn::I64GtU => {
                    let b = pop_i64(st.stack)?;
                    let a = pop_i64(st.stack)?;
                    let res = match insn {
                        Insn::I64Eq => a == b,
                        Insn::I64Ne => a != b,
                        Insn::I64LtS => a < b,
                        Insn::I64LtU => (a as u64) < (b as u64),
                        Insn::I64GtS => a > b,
                        Insn::I64GtU => (a as u64) > (b as u64),
                        _ => unreachable!(),
                    };
                    push_val(
                        st.stack,
                        WasmVal::I32(i32::from(res)),
                        st.budget.max_stack_values,
                    )?;
                    pc += 1;
                }
                Insn::I32Add
                | Insn::I32Sub
                | Insn::I32Mul
                | Insn::I32DivS
                | Insn::I32DivU
                | Insn::I32RemS
                | Insn::I32RemU
                | Insn::I32And
                | Insn::I32Or
                | Insn::I32Xor
                | Insn::I32Shl
                | Insn::I32ShrS
                | Insn::I32ShrU => {
                    let b = pop_i32(st.stack)?;
                    let a = pop_i32(st.stack)?;
                    let v = match insn {
                        Insn::I32Add => a.wrapping_add(b),
                        Insn::I32Sub => a.wrapping_sub(b),
                        Insn::I32Mul => a.wrapping_mul(b),
                        Insn::I32DivS => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            if a == i32::MIN && b == -1 {
                                return Err(WasmRunError::Trap("integer overflow".into()));
                            }
                            a / b
                        }
                        Insn::I32DivU => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            ((a as u32) / (b as u32)) as i32
                        }
                        Insn::I32RemS => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            a.wrapping_rem(b)
                        }
                        Insn::I32RemU => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            ((a as u32) % (b as u32)) as i32
                        }
                        Insn::I32And => a & b,
                        Insn::I32Or => a | b,
                        Insn::I32Xor => a ^ b,
                        Insn::I32Shl => a.wrapping_shl(b as u32),
                        Insn::I32ShrS => a.wrapping_shr(b as u32),
                        Insn::I32ShrU => ((a as u32).wrapping_shr(b as u32)) as i32,
                        _ => unreachable!(),
                    };
                    push_val(st.stack, WasmVal::I32(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
                Insn::I64Add
                | Insn::I64Sub
                | Insn::I64Mul
                | Insn::I64And
                | Insn::I64Or
                | Insn::I64Xor
                | Insn::I64Shl
                | Insn::I64ShrU => {
                    let b = pop_i64(st.stack)?;
                    let a = pop_i64(st.stack)?;
                    let v = match insn {
                        Insn::I64Add => a.wrapping_add(b),
                        Insn::I64Sub => a.wrapping_sub(b),
                        Insn::I64Mul => a.wrapping_mul(b),
                        Insn::I64And => a & b,
                        Insn::I64Or => a | b,
                        Insn::I64Xor => a ^ b,
                        Insn::I64Shl => a.wrapping_shl(b as u32),
                        Insn::I64ShrU => ((a as u64).wrapping_shr(b as u32)) as i64,
                        _ => unreachable!(),
                    };
                    push_val(st.stack, WasmVal::I64(v), st.budget.max_stack_values)?;
                    pc += 1;
                }
            }
        }
        Ok(())
    }

    {
        let mut call_state = CallState {
            parsed: &parsed,
            budget,
            start,
            fuel_consumed: &mut fuel_consumed,
            peak_memory_bytes: &mut peak_memory_bytes,
            memory: &mut memory,
            globals: &mut globals,
            stack: &mut stack,
        };
        exec_call(&mut call_state, func_idx, args.to_vec(), 1)?;
    }

    if stack.len() != entry_ty.results.len() {
        return Err(WasmRunError::Trap("unexpected result stack arity".into()));
    }
    let tier_rec = ReproducibilityTier::R2DeterministicGrain;
    let commitment = compute_wasm_commitment(
        &module_digest,
        entrypoint,
        args,
        &stack,
        fuel_consumed,
        peak_memory_bytes,
        tier_rec,
    );
    Ok(WasmExecutionReceipt {
        module_digest,
        entrypoint: entrypoint.to_string(),
        results: stack,
        fuel_consumed,
        peak_memory_bytes,
        tier: tier_rec,
        egress: EgressPosture::DenyByConstruction,
        commitment,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Hand-assembled core Wasm 1.0 module: `(module (func (export "run") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))`
    const WASM_ADD: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // \0asm v1
        0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f, // type 0: (i32, i32) -> i32
        0x03, 0x02, 0x01, 0x00, // func 0 -> type 0
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00, // export "run" -> func 0
        0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x0b, // local.get 0; local.get 1; i32.add; end
    ];

    // Infinite loop `(module (func (export "run") (loop (br 0))))` (`CAP-23` exploit payload)
    const WASM_INFINITE_LOOP: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // \0asm v1
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00, // type 0: () -> ()
        0x03, 0x02, 0x01, 0x00, // func 0
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00, // export "run"
        0x0a, 0x09, 0x01, 0x07, 0x00, 0x03, 0x40, 0x0c, 0x00, 0x0b, 0x0b, // loop { br 0 } end
    ];

    // Host import sneak attempt `(module (import "env" "sneak" (func)))`
    const WASM_IMPORT_SNEAK: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
        0x02, 0x0d, 0x01, 0x03, b'e', b'n', b'v', 0x05, b's', b'n', b'e', b'a', b'k', 0x00, 0x00,
    ];

    #[test]
    fn executes_core_wasm_and_binds_receipt_commitment() {
        let budget = WasmExecutionBudget::default();
        let args = [WasmVal::I32(40), WasmVal::I32(2)];
        let receipt =
            run_wasm_metered(WasmCapTier::Sandboxed, WASM_ADD, "run", &args, &budget).unwrap();
        assert_eq!(receipt.results, vec![WasmVal::I32(42)]);
        assert_eq!(receipt.fuel_consumed, 4);
        assert!(receipt.verify_commitment(&args));
        assert!(!receipt.verify_commitment(&[WasmVal::I32(41), WasmVal::I32(1)]));
    }

    #[test]
    fn cap23_infinite_loop_halts_deterministically_on_fuel_budget() {
        let budget = WasmExecutionBudget::new(250, 65_536);
        let res = run_wasm_metered(
            WasmCapTier::Sandboxed,
            WASM_INFINITE_LOOP,
            "run",
            &[],
            &budget,
        );
        assert_eq!(
            res,
            Err(WasmRunError::OutOfFuel {
                max_fuel: 250,
                consumed: 250
            })
        );
        // Zero fuel budget is refused up front
        assert!(matches!(
            run_wasm_metered(
                WasmCapTier::Sandboxed,
                WASM_ADD,
                "run",
                &[WasmVal::I32(1), WasmVal::I32(2)],
                &WasmExecutionBudget::new(0, 65_536)
            ),
            Err(WasmRunError::InvalidBudget(_))
        ));
    }

    #[test]
    fn empty_linker_denies_host_imports_and_unserved_tiers_fail_closed() {
        assert_eq!(
            run_wasm_metered(
                WasmCapTier::Sandboxed,
                WASM_IMPORT_SNEAK,
                "run",
                &[],
                &WasmExecutionBudget::default()
            ),
            Err(WasmRunError::HostImportDenied {
                module: "env".into(),
                name: "sneak".into()
            })
        );
        assert!(matches!(
            run_wasm_metered(
                WasmCapTier::MicroVm,
                WASM_ADD,
                "run",
                &[WasmVal::I32(1), WasmVal::I32(2)],
                &WasmExecutionBudget::default()
            ),
            Err(WasmRunError::TierNotServed { .. })
        ));
    }
}
