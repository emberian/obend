#![forbid(unsafe_code)]
//! Deterministic Fuel- & Memory-Metered WebAssembly 1.0 + Sign-Ext + Bulk-Memory Sandbox (`CAP-23`).
//!
//! Replaces `breadstuffs/dregg-sandbox/src/lib.rs:364-375` (which instantiated `wasmi` with
//! zero fuel cap, zero memory limiter, and zero wall-clock timeout, allowing `(loop (br 0))` to
//! wedge host worker threads indefinitely) with a pure-Rust, zero-`unsafe`, empty-linker
//! WebAssembly 1.0 + Sign-Extension + Non-Trapping Float-to-Int + Bulk-Memory + `funcref`
//! binary (`\0asm\x01\0\0\0`) validator and fuel-metered interpreter capable of executing real
//! `rustc --target wasm32-unknown-unknown` binaries deterministically across `x86_64` and `aarch64`.

use std::collections::HashSet;
use std::fmt;
use std::time::{Duration, Instant};

use crate::grain::{ReproducibilityTier, sha256};

/// Standard WebAssembly linear memory page size (`64 KiB`).
pub const WASM_PAGE_SIZE: usize = 65_536;

/// Canonical positive quiet-NaN bit pattern for `f32` (`0x7fc0_0000`).
pub const CANON_F32_NAN_BITS: u32 = 0x7fc0_0000;

/// Canonical positive quiet-NaN bit pattern for `f64` (`0x7ff8_0000_0000_0000`).
pub const CANON_F64_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

const MAX_MODULE_BYTES: usize = 16 * 1024 * 1024;
const MAX_TYPES: usize = 16_384;
const MAX_FUNCS: usize = 16_384;
const MAX_TABLES: usize = 16;
const MAX_TABLE_ELEMENTS: usize = 65_536;
const MAX_WASM32_PAGES: usize = 65_536;
const MAX_GLOBALS: usize = 4_096;
const MAX_EXPORTS: usize = 16_384;
const MAX_ELEM_SEGMENTS: usize = 4_096;
const MAX_DATA_SEGMENTS: usize = 4_096;
const MAX_PARAMS: usize = 128;
const MAX_RESULTS: usize = 64;
const MAX_LOCAL_GROUPS: usize = 1_024;
const MAX_LOCALS_PER_FUNC: usize = 4_096;
const MAX_DECLARED_LOCALS_TOTAL: usize = 65_536;
const MAX_TOTAL_INSNS: usize = 262_144;
const MAX_CONTROL_NESTING: usize = 1_024;
const MAX_LIVE_LOCALS_TOTAL: usize = 262_144;
const MAX_BR_TABLE_TARGETS: usize = 16_384;

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

impl EgressPosture {
    fn tag_byte(self) -> u8 {
        match self {
            Self::DenyByConstruction => 1,
            Self::NoEngineNoEgress => 0,
        }
    }
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

/// WebAssembly 1.0 + `funcref` runtime value (`i32`, `i64`, bit-exact IEEE-754 `f32`/`f64`, `funcref`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmVal {
    I32(i32),
    I64(i64),
    F32(u32),
    F64(u64),
    FuncRef(Option<u32>),
}

impl WasmVal {
    #[inline]
    pub fn f32(v: f32) -> Self {
        Self::F32(v.to_bits())
    }

    #[inline]
    pub fn f64(v: f64) -> Self {
        Self::F64(v.to_bits())
    }

    #[inline]
    pub const fn f32_bits(bits: u32) -> Self {
        Self::F32(bits)
    }

    #[inline]
    pub const fn f64_bits(bits: u64) -> Self {
        Self::F64(bits)
    }

    #[inline]
    pub const fn as_i32(self) -> Option<i32> {
        match self {
            Self::I32(v) => Some(v),
            _ => None,
        }
    }

    #[inline]
    pub const fn as_i64(self) -> Option<i64> {
        match self {
            Self::I64(v) => Some(v),
            _ => None,
        }
    }

    #[inline]
    pub fn as_f32(self) -> Option<f32> {
        match self {
            Self::F32(bits) => Some(f32::from_bits(bits)),
            _ => None,
        }
    }

    #[inline]
    pub fn as_f64(self) -> Option<f64> {
        match self {
            Self::F64(bits) => Some(f64::from_bits(bits)),
            _ => None,
        }
    }

    #[inline]
    pub const fn as_f32_bits(self) -> Option<u32> {
        match self {
            Self::F32(bits) => Some(bits),
            _ => None,
        }
    }

    #[inline]
    pub const fn as_f64_bits(self) -> Option<u64> {
        match self {
            Self::F64(bits) => Some(bits),
            _ => None,
        }
    }

    #[inline]
    pub const fn as_funcref(self) -> Option<Option<u32>> {
        match self {
            Self::FuncRef(r) => Some(r),
            _ => None,
        }
    }

    fn ty(self) -> ValType {
        match self {
            Self::I32(_) => ValType::I32,
            Self::I64(_) => ValType::I64,
            Self::F32(_) => ValType::F32,
            Self::F64(_) => ValType::F64,
            Self::FuncRef(_) => ValType::FuncRef,
        }
    }

    fn default_for(vt: ValType) -> Self {
        match vt {
            ValType::I32 => Self::I32(0),
            ValType::I64 => Self::I64(0),
            ValType::F32 => Self::F32(0),
            ValType::F64 => Self::F64(0),
            ValType::FuncRef => Self::FuncRef(None),
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
            Self::F32(bits) => {
                out.push(0x7D);
                out.extend_from_slice(&bits.to_le_bytes());
            }
            Self::F64(bits) => {
                out.push(0x7C);
                out.extend_from_slice(&bits.to_le_bytes());
            }
            Self::FuncRef(None) => {
                out.push(0x70);
                out.push(0x00);
            }
            Self::FuncRef(Some(idx)) => {
                out.push(0x70);
                out.push(0x01);
                out.extend_from_slice(&idx.to_le_bytes());
            }
        }
    }
}

impl fmt::Display for WasmVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I32(v) => write!(f, "{v}"),
            Self::I64(v) => write!(f, "{v}"),
            Self::F32(bits) => write!(f, "{:#010x} ({})", bits, f32::from_bits(*bits)),
            Self::F64(bits) => write!(f, "{:#018x} ({})", bits, f64::from_bits(*bits)),
            Self::FuncRef(None) => write!(f, "funcref(null)"),
            Self::FuncRef(Some(idx)) => write!(f, "funcref({idx})"),
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
        self.egress == EgressPosture::DenyByConstruction
            && self.commitment
                == compute_wasm_commitment(
                    &self.module_digest,
                    &self.entrypoint,
                    args,
                    &self.results,
                    self.fuel_consumed,
                    self.peak_memory_bytes,
                    self.tier,
                    self.egress,
                )
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_wasm_commitment(
    module_digest: &[u8; 32],
    entrypoint: &str,
    args: &[WasmVal],
    results: &[WasmVal],
    fuel_consumed: u64,
    peak_memory_bytes: usize,
    tier: ReproducibilityTier,
    egress: EgressPosture,
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(164);
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
    buf.push(egress.tag_byte());
    sha256(&buf)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValType {
    I32,
    I64,
    F32,
    F64,
    FuncRef,
}

impl ValType {
    fn is_numeric(self) -> bool {
        matches!(self, Self::I32 | Self::I64 | Self::F32 | Self::F64)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    Else,
}

#[derive(Debug, Clone, Copy)]
struct TableType {
    min: u32,
    max: Option<u32>,
}

#[derive(Debug, Clone)]
enum ElemSegment {
    Active {
        table_idx: usize,
        offset: u32,
        init: Vec<Option<u32>>,
    },
    Passive(Vec<Option<u32>>),
    Declarative,
}

#[derive(Debug, Clone, Copy)]
enum DataSegmentKind {
    Active { offset: u32 },
    Passive,
}

#[derive(Debug, Clone, Copy)]
struct DataSegmentSpan {
    kind: DataSegmentKind,
    byte_start: usize,
    byte_end: usize,
}

#[derive(Debug, Clone)]
enum Insn {
    Unreachable,
    Nop,
    Block {
        param_len: usize,
        result_len: usize,
        end_pc: usize,
    },
    Loop {
        param_len: usize,
        start_pc: usize,
    },
    If {
        param_len: usize,
        result_len: usize,
        else_pc: Option<usize>,
        end_pc: usize,
    },
    Else {
        end_pc: usize,
    },
    End,
    Br(u32),
    BrIf(u32),
    BrTable {
        targets: Vec<u32>,
        default_target: u32,
    },
    Return,
    Call(u32),
    CallIndirect {
        type_idx: u32,
        table_idx: u32,
    },
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    TableGet(u32),
    TableSet(u32),
    I32Load { offset: u32 },
    I64Load { offset: u32 },
    F32Load { offset: u32 },
    F64Load { offset: u32 },
    I32Load8S { offset: u32 },
    I32Load8U { offset: u32 },
    I32Load16S { offset: u32 },
    I32Load16U { offset: u32 },
    I64Load8S { offset: u32 },
    I64Load8U { offset: u32 },
    I64Load16S { offset: u32 },
    I64Load16U { offset: u32 },
    I64Load32S { offset: u32 },
    I64Load32U { offset: u32 },
    I32Store { offset: u32 },
    I64Store { offset: u32 },
    F32Store { offset: u32 },
    F64Store { offset: u32 },
    I32Store8 { offset: u32 },
    I32Store16 { offset: u32 },
    I64Store8 { offset: u32 },
    I64Store16 { offset: u32 },
    I64Store32 { offset: u32 },
    MemorySize,
    MemoryGrow,
    I32Const(i32),
    I64Const(i64),
    F32Const(u32),
    F64Const(u64),
    RefNullFunc,
    RefIsNull,
    RefFunc(u32),
    // Comparisons
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
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    // i32 numeric
    I32Clz,
    I32Ctz,
    I32Popcnt,
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
    I32Rotl,
    I32Rotr,
    // i64 numeric
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
    // f32 numeric
    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    // f64 numeric
    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,
    // Conversions, promotions, reinterpretations, sign-ext
    I32WrapI64,
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64ExtendI32S,
    I64ExtendI32U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    // 0xFC 0..7 saturating float-to-int
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
    // 0xFC 8..17 bulk-memory & bulk-table ops
    MemoryInit { data_idx: u32 },
    DataDrop { data_idx: u32 },
    MemoryCopy,
    MemoryFill,
    TableInit { elem_idx: u32, table_idx: u32 },
    ElemDrop { elem_idx: u32 },
    TableCopy { dst_table: u32, src_table: u32 },
    TableGrow { table_idx: u32 },
    TableSize { table_idx: u32 },
    TableFill { table_idx: u32 },
}

impl Insn {
    fn fuel_cost(&self) -> u64 {
        match self {
            Self::I32Mul | Self::I64Mul | Self::F32Mul | Self::F64Mul => 2,
            Self::I32DivS
            | Self::I32DivU
            | Self::I32RemS
            | Self::I32RemU
            | Self::I64DivS
            | Self::I64DivU
            | Self::I64RemS
            | Self::I64RemU
            | Self::F32Div
            | Self::F64Div
            | Self::F32Sqrt
            | Self::F64Sqrt => 3,
            Self::I32Load { .. }
            | Self::I64Load { .. }
            | Self::F32Load { .. }
            | Self::F64Load { .. }
            | Self::I32Load8S { .. }
            | Self::I32Load8U { .. }
            | Self::I32Load16S { .. }
            | Self::I32Load16U { .. }
            | Self::I64Load8S { .. }
            | Self::I64Load8U { .. }
            | Self::I64Load16S { .. }
            | Self::I64Load16U { .. }
            | Self::I64Load32S { .. }
            | Self::I64Load32U { .. }
            | Self::I32Store { .. }
            | Self::I64Store { .. }
            | Self::F32Store { .. }
            | Self::F64Store { .. }
            | Self::I32Store8 { .. }
            | Self::I32Store16 { .. }
            | Self::I64Store8 { .. }
            | Self::I64Store16 { .. }
            | Self::I64Store32 { .. }
            | Self::TableGet(_)
            | Self::TableSet(_) => 3,
            Self::Call(_) | Self::CallIndirect { .. } => 4,
            Self::MemoryGrow | Self::TableGrow { .. } => 8,
            // Note: Bulk-memory & bulk-table ops pay `1` base fuel here PLUS `len / 64` dynamic
            // fuel BEFORE copying inside the VM loop (`1 + len / 64` total).
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
    tables: Vec<TableType>,
    mem_initial_pages: usize,
    mem_max_pages: Option<usize>,
    globals: Vec<(ValType, bool, WasmVal)>,
    exports: Vec<(String, u8, u32)>,
    start_func: Option<usize>,
    elem_segments: Vec<ElemSegment>,
    data_segments: Vec<DataSegmentSpan>,
}

struct Cursor<'a> {
    bytes: &'a [u8],
    base_offset: usize,
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            base_offset: 0,
            pos: 0,
        }
    }

    fn with_offset(bytes: &'a [u8], base_offset: usize) -> Self {
        Self {
            bytes,
            base_offset,
            pos: 0,
        }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    fn abs_pos(&self) -> usize {
        self.base_offset + self.pos
    }

    fn peek_byte(&self) -> Result<u8, WasmRunError> {
        self.bytes
            .get(self.pos)
            .copied()
            .ok_or_else(|| WasmRunError::InvalidModule("unexpected EOF".into()))
    }

    fn read_byte(&mut self) -> Result<u8, WasmRunError> {
        let b = self.peek_byte()?;
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

    fn read_u32_le(&mut self) -> Result<u32, WasmRunError> {
        let s = self.read_slice(4)?;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }

    fn read_u64_le(&mut self) -> Result<u64, WasmRunError> {
        let s = self.read_slice(8)?;
        Ok(u64::from_le_bytes([
            s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7],
        ]))
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

    fn read_s33_leb(&mut self) -> Result<i64, WasmRunError> {
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
                if !(-(1i64 << 32)..(1i64 << 32)).contains(&result) {
                    return Err(WasmRunError::InvalidModule("s33 LEB128 out of range".into()));
                }
                return Ok(result);
            }
            if shift >= 35 {
                return Err(WasmRunError::InvalidModule("s33 LEB128 too long".into()));
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
            0x7D => Ok(ValType::F32),
            0x7C => Ok(ValType::F64),
            0x70 => Ok(ValType::FuncRef),
            other => Err(WasmRunError::InvalidModule(format!(
                "unsupported wasm value type {other:#x}"
            ))),
        }
    }
}

/// Canonical WebAssembly binary section order (`DataCount` section 12 sits between `Element` 9 and `Code` 10).
fn section_order_rank(sec_id: u8) -> Result<u8, WasmRunError> {
    match sec_id {
        1 => Ok(1),   // Type
        2 => Ok(2),   // Import
        3 => Ok(3),   // Function
        4 => Ok(4),   // Table
        5 => Ok(5),   // Memory
        6 => Ok(6),   // Global
        7 => Ok(7),   // Export
        8 => Ok(8),   // Start
        9 => Ok(9),   // Element
        12 => Ok(10), // DataCount (precedes Code & Data!)
        10 => Ok(11), // Code
        11 => Ok(12), // Data
        other => Err(WasmRunError::InvalidModule(format!(
            "unknown wasm section id {other}"
        ))),
    }
}

/// Evaluate a strict WebAssembly 1.0 + Reference-Types single-instruction constant expression
/// (`Global`, `Element` offset/item, `Data` offset) under our zero-import profile.
fn eval_const_expr(
    cur: &mut Cursor<'_>,
    expected_ty: ValType,
    num_funcs: usize,
    declared_func_refs: Option<&mut [bool]>,
) -> Result<WasmVal, WasmRunError> {
    let op = cur.read_byte()?;
    let val = match op {
        0x41 => WasmVal::I32(cur.read_i32_leb()?),
        0x42 => WasmVal::I64(cur.read_i64_leb()?),
        0x43 => WasmVal::F32(cur.read_u32_le()?),
        0x44 => WasmVal::F64(cur.read_u64_le()?),
        0xD0 => {
            if cur.read_byte()? != 0x70 {
                return Err(WasmRunError::InvalidModule(
                    "unsupported ref.null type in const expr".into(),
                ));
            }
            WasmVal::FuncRef(None)
        }
        0xD2 => {
            let fidx = cur.read_u32_leb()?;
            if (fidx as usize) >= num_funcs {
                return Err(WasmRunError::InvalidModule(
                    "ref.func index OOB in const expr".into(),
                ));
            }
            if let Some(decl) = declared_func_refs {
                decl[fidx as usize] = true;
            }
            WasmVal::FuncRef(Some(fidx))
        }
        other => {
            return Err(WasmRunError::InvalidModule(format!(
                "unsupported const expr opcode {other:#x}"
            )))
        }
    };
    if cur.read_byte()? != 0x0B {
        return Err(WasmRunError::InvalidModule(
            "const expr missing terminating 0x0B end".into(),
        ));
    }
    if val.ty() != expected_ty {
        return Err(WasmRunError::InvalidModule(format!(
            "const expr type mismatch: expected {:?}, got {:?}",
            expected_ty,
            val.ty()
        )));
    }
    Ok(val)
}

fn check_wall_timeout(start: &Instant, limit: Option<Duration>) -> Result<(), WasmRunError> {
    if let Some(lim) = limit {
        if start.elapsed() > lim {
            return Err(WasmRunError::WallTimeoutExceeded {
                limit_ms: lim.as_millis() as u64,
            });
        }
    }
    Ok(())
}

fn parse_wasm_module(
    bytes: &[u8],
    start: &Instant,
    wall_limit: Option<Duration>,
) -> Result<ParsedModule, WasmRunError> {
    if bytes.len() > MAX_MODULE_BYTES {
        return Err(WasmRunError::InvalidModule(format!(
            "module size ({} B) exceeds MAX_MODULE_BYTES ({MAX_MODULE_BYTES} B)",
            bytes.len()
        )));
    }
    if bytes.len() < 8 || &bytes[0..4] != b"\0asm" || bytes[4..8] != [1, 0, 0, 0] {
        return Err(WasmRunError::InvalidModule(
            "bad WebAssembly magic or version (expected \\0asm v1)".into(),
        ));
    }
    let mut cur = Cursor::with_offset(&bytes[8..], 8);
    let mut types = Vec::new();
    let mut func_type_indices = Vec::new();
    let mut tables = Vec::new();
    let mut has_memory = false;
    let mut mem_initial_pages = 0usize;
    let mut mem_max_pages = None;
    let mut globals: Vec<(ValType, bool, WasmVal)> = Vec::new();
    let mut exports = Vec::new();
    let mut export_names = HashSet::new();
    let mut start_func = None;
    let mut elem_segments = Vec::new();
    let mut declared_data_count: Option<usize> = None;
    let mut saw_code_section = false;
    let mut saw_data_section = false;
    let mut code_bodies: Vec<(Vec<ValType>, Vec<Insn>)> = Vec::new();
    let mut data_segments = Vec::new();
    let mut declared_func_refs: Vec<bool> = Vec::new();
    let mut last_rank = 0u8;

    while !cur.is_eof() {
        let sec_id = cur.read_byte()?;
        let sec_len = cur.read_u32_leb()? as usize;
        let sec_abs_start = cur.abs_pos();
        let sec_bytes = cur.read_slice(sec_len)?;
        if sec_id == 0 {
            // Custom sections (`name`, `producers`, `.debug_*`, `target_features`) require at least a valid UTF-8 name.
            let mut cc = Cursor::new(sec_bytes);
            let _custom_name = cc.read_name()?;
            continue;
        }
        let rank = section_order_rank(sec_id)?;
        if rank <= last_rank {
            return Err(WasmRunError::InvalidModule(
                "out-of-order or duplicate section".into(),
            ));
        }
        last_rank = rank;

        let mut sc = Cursor::with_offset(sec_bytes, sec_abs_start);
        match sec_id {
            1 => {
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_TYPES || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many types".into()));
                }
                types.reserve(n);
                for _ in 0..n {
                    if sc.read_byte()? != 0x60 {
                        return Err(WasmRunError::InvalidModule("expected 0x60 functype".into()));
                    }
                    let np = sc.read_u32_leb()? as usize;
                    if np > MAX_PARAMS || np > sc.remaining() {
                        return Err(WasmRunError::InvalidModule("too many params".into()));
                    }
                    let mut params = Vec::with_capacity(np);
                    for _ in 0..np {
                        params.push(sc.read_valtype()?);
                    }
                    let nr = sc.read_u32_leb()? as usize;
                    if nr > MAX_RESULTS || nr > sc.remaining() {
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
                if n > MAX_FUNCS || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many functions".into()));
                }
                func_type_indices.reserve(n);
                for _ in 0..n {
                    let idx = sc.read_u32_leb()? as usize;
                    if idx >= types.len() {
                        return Err(WasmRunError::InvalidModule("function type index OOB".into()));
                    }
                    func_type_indices.push(idx);
                }
                declared_func_refs.resize(func_type_indices.len(), false);
            }
            4 => {
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_TABLES || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many tables".into()));
                }
                for _ in 0..n {
                    let reftype = sc.read_byte()?;
                    if reftype != 0x70 {
                        return Err(WasmRunError::InvalidModule(format!(
                            "unsupported table elemtype {reftype:#x} (only funcref 0x70)"
                        )));
                    }
                    let flags = sc.read_byte()?;
                    let min = sc.read_u32_leb()?;
                    let max = match flags {
                        0x00 => None,
                        0x01 => {
                            let m = sc.read_u32_leb()?;
                            if m < min {
                                return Err(WasmRunError::InvalidModule(
                                    "table limits max < min".into(),
                                ));
                            }
                            Some(m)
                        }
                        _ => {
                            return Err(WasmRunError::InvalidModule(
                                "invalid table limits flags".into(),
                            ))
                        }
                    };
                    tables.push(TableType { min, max });
                }
            }
            5 => {
                let n = sc.read_u32_leb()?;
                if n > 1 {
                    return Err(WasmRunError::InvalidModule(
                        "multiple memories unsupported".into(),
                    ));
                }
                if n == 1 {
                    has_memory = true;
                    let flags = sc.read_byte()?;
                    let min = sc.read_u32_leb()? as usize;
                    if min > MAX_WASM32_PAGES {
                        return Err(WasmRunError::InvalidModule(
                            "memory min pages exceeds 65536".into(),
                        ));
                    }
                    mem_initial_pages = min;
                    mem_max_pages = match flags {
                        0x00 => None,
                        0x01 => {
                            let max = sc.read_u32_leb()? as usize;
                            if max < min || max > MAX_WASM32_PAGES {
                                return Err(WasmRunError::InvalidModule(
                                    "invalid memory max pages".into(),
                                ));
                            }
                            Some(max)
                        }
                        _ => {
                            return Err(WasmRunError::InvalidModule(
                                "invalid memory limits flags".into(),
                            ))
                        }
                    };
                }
            }
            6 => {
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_GLOBALS || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many globals".into()));
                }
                let num_funcs = func_type_indices.len();
                for _ in 0..n {
                    let vt = sc.read_valtype()?;
                    let mut_byte = sc.read_byte()?;
                    if mut_byte > 1 {
                        return Err(WasmRunError::InvalidModule(
                            "invalid global mutability flag".into(),
                        ));
                    }
                    let mutable = mut_byte == 1;
                    let val =
                        eval_const_expr(&mut sc, vt, num_funcs, Some(&mut declared_func_refs))?;
                    globals.push((vt, mutable, val));
                }
            }
            7 => {
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_EXPORTS || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many exports".into()));
                }
                for _ in 0..n {
                    let name = sc.read_name()?;
                    if !export_names.insert(name.clone()) {
                        return Err(WasmRunError::InvalidModule(format!(
                            "duplicate export name `{name}`"
                        )));
                    }
                    let kind = sc.read_byte()?;
                    let idx = sc.read_u32_leb()?;
                    match kind {
                        0 => {
                            if (idx as usize) >= func_type_indices.len() {
                                return Err(WasmRunError::InvalidModule(
                                    "export func index OOB".into(),
                                ));
                            }
                            declared_func_refs[idx as usize] = true;
                        }
                        1 => {
                            if (idx as usize) >= tables.len() {
                                return Err(WasmRunError::InvalidModule(
                                    "export table index OOB".into(),
                                ));
                            }
                        }
                        2 => {
                            if idx != 0 || !has_memory {
                                return Err(WasmRunError::InvalidModule(
                                    "export memory index OOB".into(),
                                ));
                            }
                        }
                        3 => {
                            if (idx as usize) >= globals.len() {
                                return Err(WasmRunError::InvalidModule(
                                    "export global index OOB".into(),
                                ));
                            }
                        }
                        _ => {
                            return Err(WasmRunError::InvalidModule("invalid export kind".into()))
                        }
                    }
                    exports.push((name, kind, idx));
                }
            }
            8 => {
                let sidx = sc.read_u32_leb()? as usize;
                let &ty_idx = func_type_indices.get(sidx).ok_or_else(|| {
                    WasmRunError::InvalidModule("start function index OOB".into())
                })?;
                let sty = &types[ty_idx];
                if !sty.params.is_empty() || !sty.results.is_empty() {
                    return Err(WasmRunError::InvalidModule(
                        "start function must have signature () -> ()".into(),
                    ));
                }
                start_func = Some(sidx);
            }
            9 => {
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_ELEM_SEGMENTS || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many element segments".into()));
                }
                let num_funcs = func_type_indices.len();
                let mut total_elems = 0usize;
                for _ in 0..n {
                    let mode = sc.read_u32_leb()?;
                    if mode > 7 {
                        return Err(WasmRunError::InvalidModule(format!(
                            "unsupported element segment flags {mode:#x}"
                        )));
                    }
                    let is_passive_or_decl = (mode & 0x01) != 0;
                    let is_declarative = (mode & 0x03) == 0x03;
                    let has_explicit_table_or_kind = (mode & 0x02) != 0;
                    let uses_exprs = (mode & 0x04) != 0;

                    let mut active_target: Option<(usize, u32)> = None;
                    if !is_passive_or_decl {
                        let tidx = if has_explicit_table_or_kind {
                            sc.read_u32_leb()? as usize
                        } else {
                            0usize
                        };
                        if tidx >= tables.len() {
                            return Err(WasmRunError::InvalidModule(
                                "element segment table index OOB".into(),
                            ));
                        }
                        let WasmVal::I32(off) =
                            eval_const_expr(&mut sc, ValType::I32, num_funcs, None)?
                        else {
                            unreachable!()
                        };
                        active_target = Some((tidx, off as u32));
                    }

                    if is_passive_or_decl || has_explicit_table_or_kind {
                        if uses_exprs {
                            if sc.read_byte()? != 0x70 {
                                return Err(WasmRunError::InvalidModule(
                                    "unsupported element reftype (expected funcref 0x70)".into(),
                                ));
                            }
                        } else if sc.read_byte()? != 0x00 {
                            return Err(WasmRunError::InvalidModule(
                                "unsupported elemkind (expected 0x00)".into(),
                            ));
                        }
                    }

                    let count = sc.read_u32_leb()? as usize;
                    total_elems = total_elems.saturating_add(count);
                    if count > sc.remaining() || total_elems > MAX_TABLE_ELEMENTS {
                        return Err(WasmRunError::InvalidModule(
                            "element segment count exceeds limit".into(),
                        ));
                    }
                    let mut items = Vec::with_capacity(count);
                    if uses_exprs {
                        for _ in 0..count {
                            let WasmVal::FuncRef(r) = eval_const_expr(
                                &mut sc,
                                ValType::FuncRef,
                                num_funcs,
                                Some(&mut declared_func_refs),
                            )?
                            else {
                                unreachable!()
                            };
                            items.push(r);
                        }
                    } else {
                        for _ in 0..count {
                            let fidx = sc.read_u32_leb()?;
                            if (fidx as usize) >= num_funcs {
                                return Err(WasmRunError::InvalidModule(
                                    "element func index OOB".into(),
                                ));
                            }
                            declared_func_refs[fidx as usize] = true;
                            items.push(Some(fidx));
                        }
                    }

                    let seg = if let Some((table_idx, offset)) = active_target {
                        ElemSegment::Active {
                            table_idx,
                            offset,
                            init: items,
                        }
                    } else if is_declarative {
                        ElemSegment::Declarative
                    } else {
                        ElemSegment::Passive(items)
                    };
                    elem_segments.push(seg);
                }
            }
            12 => {
                let dc = sc.read_u32_leb()? as usize;
                if dc > MAX_DATA_SEGMENTS {
                    return Err(WasmRunError::InvalidModule("datacount exceeds limit".into()));
                }
                declared_data_count = Some(dc);
            }
            10 => {
                saw_code_section = true;
                let n = sc.read_u32_leb()? as usize;
                if n != func_type_indices.len() {
                    return Err(WasmRunError::InvalidModule(
                        "code section count != function section count".into(),
                    ));
                }
                let ctx = ValidateCtx {
                    types: &types,
                    func_type_indices: &func_type_indices,
                    tables: &tables,
                    has_memory,
                    globals: &globals,
                    num_elem_segments: elem_segments.len(),
                    declared_data_count,
                    declared_func_refs: &declared_func_refs,
                };
                code_bodies.reserve(n);
                let mut total_insns = 0usize;
                let mut total_declared_locals = 0usize;
                for &ty_idx in &func_type_indices {
                    check_wall_timeout(start, wall_limit)?;
                    let body_len = sc.read_u32_leb()? as usize;
                    let body_bytes = sc.read_slice(body_len)?;
                    let (extra_locals, insns) = parse_and_validate_code_body(
                        body_bytes,
                        ty_idx,
                        &ctx,
                        &mut total_insns,
                        &mut total_declared_locals,
                    )?;
                    code_bodies.push((extra_locals, insns));
                }
            }
            11 => {
                saw_data_section = true;
                let n = sc.read_u32_leb()? as usize;
                if n > MAX_DATA_SEGMENTS || n > sc.remaining() {
                    return Err(WasmRunError::InvalidModule("too many data segments".into()));
                }
                if let Some(dc) = declared_data_count {
                    if n != dc {
                        return Err(WasmRunError::InvalidModule(
                            "data section count != datacount section".into(),
                        ));
                    }
                }
                let num_funcs = func_type_indices.len();
                for _ in 0..n {
                    let mode = sc.read_u32_leb()?;
                    let kind = match mode {
                        0 => {
                            if !has_memory {
                                return Err(WasmRunError::InvalidModule(
                                    "active data segment without memory".into(),
                                ));
                            }
                            let WasmVal::I32(off) =
                                eval_const_expr(&mut sc, ValType::I32, num_funcs, None)?
                            else {
                                unreachable!()
                            };
                            DataSegmentKind::Active { offset: off as u32 }
                        }
                        1 => DataSegmentKind::Passive,
                        2 => {
                            let mem_idx = sc.read_u32_leb()?;
                            if mem_idx != 0 || !has_memory {
                                return Err(WasmRunError::InvalidModule(
                                    "active data segment memory index OOB".into(),
                                ));
                            }
                            let WasmVal::I32(off) =
                                eval_const_expr(&mut sc, ValType::I32, num_funcs, None)?
                            else {
                                unreachable!()
                            };
                            DataSegmentKind::Active { offset: off as u32 }
                        }
                        other => {
                            return Err(WasmRunError::InvalidModule(format!(
                                "unsupported data segment mode {other}"
                            )))
                        }
                    };
                    let dlen = sc.read_u32_leb()? as usize;
                    let byte_start = sc.abs_pos();
                    let _ = sc.read_slice(dlen)?;
                    let byte_end = sc.abs_pos();
                    data_segments.push(DataSegmentSpan {
                        kind,
                        byte_start,
                        byte_end,
                    });
                }
            }
            _ => unreachable!(),
        }
        if !sc.is_eof() {
            return Err(WasmRunError::InvalidModule(format!(
                "trailing bytes in section {sec_id}"
            )));
        }
    }

    if !func_type_indices.is_empty() && !saw_code_section {
        return Err(WasmRunError::InvalidModule("missing code section".into()));
    }
    if let Some(dc) = declared_data_count {
        if !saw_data_section && dc != 0 {
            return Err(WasmRunError::InvalidModule(
                "missing data section required by datacount".into(),
            ));
        }
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
        tables,
        mem_initial_pages,
        mem_max_pages,
        globals,
        exports,
        start_func,
        elem_segments,
        data_segments,
    })
}

struct ValidateCtx<'a> {
    types: &'a [FuncType],
    func_type_indices: &'a [usize],
    tables: &'a [TableType],
    has_memory: bool,
    globals: &'a [(ValType, bool, WasmVal)],
    num_elem_segments: usize,
    declared_data_count: Option<usize>,
    declared_func_refs: &'a [bool],
}

struct CtrlFrame {
    kind: BlockKind,
    start_types: Vec<ValType>,
    end_types: Vec<ValType>,
    height: usize,
    unreachable: bool,
    insn_idx: usize,
    else_idx: Option<usize>,
}

impl CtrlFrame {
    fn label_types(&self) -> &[ValType] {
        if self.kind == BlockKind::Loop {
            &self.start_types
        } else {
            &self.end_types
        }
    }
}

struct TypeStack {
    vals: Vec<Option<ValType>>,
    ctrls: Vec<CtrlFrame>,
}

impl TypeStack {
    fn new(func_results: Vec<ValType>) -> Self {
        Self {
            vals: Vec::with_capacity(32),
            ctrls: vec![CtrlFrame {
                kind: BlockKind::Func,
                start_types: Vec::new(),
                end_types: func_results,
                height: 0,
                unreachable: false,
                insn_idx: usize::MAX,
                else_idx: None,
            }],
        }
    }

    fn push_val(&mut self, t: Option<ValType>) {
        self.vals.push(t);
    }

    fn push_concrete(&mut self, t: ValType) {
        self.vals.push(Some(t));
    }

    fn push_vals(&mut self, ts: &[ValType]) {
        for &t in ts {
            self.vals.push(Some(t));
        }
    }

    fn pop_any(&mut self) -> Result<Option<ValType>, WasmRunError> {
        let frame = self
            .ctrls
            .last()
            .ok_or_else(|| WasmRunError::InvalidModule("empty control stack".into()))?;
        if self.vals.len() == frame.height {
            if frame.unreachable {
                return Ok(None);
            }
            return Err(WasmRunError::InvalidModule(
                "type validation operand stack underflow".into(),
            ));
        }
        Ok(self.vals.pop().unwrap())
    }

    fn pop_expect(&mut self, expected: ValType) -> Result<(), WasmRunError> {
        match self.pop_any()? {
            None => Ok(()),
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(WasmRunError::InvalidModule(format!(
                "type mismatch: expected {expected:?}, got {actual:?}"
            ))),
        }
    }

    fn pop_vals(&mut self, ts: &[ValType]) -> Result<(), WasmRunError> {
        for &t in ts.iter().rev() {
            self.pop_expect(t)?;
        }
        Ok(())
    }

    fn check_peek_vals(&self, ts: &[ValType]) -> Result<(), WasmRunError> {
        let frame = self
            .ctrls
            .last()
            .ok_or_else(|| WasmRunError::InvalidModule("empty control stack".into()))?;
        let avail = self.vals.len().saturating_sub(frame.height);
        if ts.len() > avail && !frame.unreachable {
            return Err(WasmRunError::InvalidModule(
                "type validation operand stack underflow".into(),
            ));
        }
        for (i, &expected) in ts.iter().rev().enumerate() {
            if i < avail {
                if let Some(actual) = self.vals[self.vals.len() - 1 - i] {
                    if actual != expected {
                        return Err(WasmRunError::InvalidModule(format!(
                            "type mismatch: expected {expected:?}, got {actual:?}"
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    fn push_ctrl(&mut self, frame: CtrlFrame) -> Result<(), WasmRunError> {
        if self.ctrls.len() >= MAX_CONTROL_NESTING {
            return Err(WasmRunError::InvalidModule(
                "control-frame nesting exceeds MAX_CONTROL_NESTING".into(),
            ));
        }
        self.ctrls.push(frame);
        Ok(())
    }

    fn mark_unreachable(&mut self) -> Result<(), WasmRunError> {
        let frame = self
            .ctrls
            .last_mut()
            .ok_or_else(|| WasmRunError::InvalidModule("empty control stack".into()))?;
        self.vals.truncate(frame.height);
        frame.unreachable = true;
        Ok(())
    }

    fn label_at(&self, depth: u32) -> Result<&CtrlFrame, WasmRunError> {
        let idx = self
            .ctrls
            .len()
            .checked_sub(1 + depth as usize)
            .ok_or_else(|| WasmRunError::InvalidModule("branch label depth OOB".into()))?;
        Ok(&self.ctrls[idx])
    }
}

fn parse_block_sig(
    cur: &mut Cursor<'_>,
    types: &[FuncType],
) -> Result<(Vec<ValType>, Vec<ValType>), WasmRunError> {
    let b = cur.peek_byte()?;
    match b {
        0x40 => {
            cur.pos += 1;
            Ok((Vec::new(), Vec::new()))
        }
        0x7F | 0x7E | 0x7D | 0x7C | 0x70 => {
            let vt = cur.read_valtype()?;
            Ok((Vec::new(), vec![vt]))
        }
        _ => {
            let idx = cur.read_s33_leb()?;
            if idx < 0 {
                return Err(WasmRunError::InvalidModule(format!(
                    "negative blocktype s33 {idx}"
                )));
            }
            let fty = types
                .get(idx as usize)
                .ok_or_else(|| WasmRunError::InvalidModule("blocktype index OOB".into()))?;
            Ok((fty.params.clone(), fty.results.clone()))
        }
    }
}

fn read_memarg(
    cur: &mut Cursor<'_>,
    has_memory: bool,
    max_align_log2: u32,
) -> Result<u32, WasmRunError> {
    if !has_memory {
        return Err(WasmRunError::InvalidModule(
            "memory instruction without declared memory".into(),
        ));
    }
    let align = cur.read_u32_leb()?;
    if align > max_align_log2 {
        return Err(WasmRunError::InvalidModule(
            "alignment must not be larger than natural".into(),
        ));
    }
    cur.read_u32_leb()
}

fn parse_and_validate_code_body(
    bytes: &[u8],
    func_ty_idx: usize,
    ctx: &ValidateCtx<'_>,
    total_insns: &mut usize,
    total_declared_locals: &mut usize,
) -> Result<(Vec<ValType>, Vec<Insn>), WasmRunError> {
    let mut cur = Cursor::new(bytes);
    let fty = &ctx.types[func_ty_idx];

    let local_groups = cur.read_u32_leb()? as usize;
    if local_groups > MAX_LOCAL_GROUPS || local_groups > cur.remaining() {
        return Err(WasmRunError::InvalidModule("too many local groups".into()));
    }
    let mut extra_locals = Vec::new();
    for _ in 0..local_groups {
        let count = cur.read_u32_leb()? as usize;
        *total_declared_locals = total_declared_locals.saturating_add(count);
        if fty
            .params
            .len()
            .saturating_add(extra_locals.len())
            .saturating_add(count)
            > MAX_LOCALS_PER_FUNC
            || *total_declared_locals > MAX_DECLARED_LOCALS_TOTAL
        {
            return Err(WasmRunError::InvalidModule("too many locals".into()));
        }
        let vt = cur.read_valtype()?;
        extra_locals.resize(extra_locals.len() + count, vt);
    }

    let mut all_locals = Vec::with_capacity(fty.params.len() + extra_locals.len());
    all_locals.extend_from_slice(&fty.params);
    all_locals.extend_from_slice(&extra_locals);

    let mut ts = TypeStack::new(fty.results.clone());
    let mut insns = Vec::new();

    while !cur.is_eof() {
        *total_insns = total_insns.saturating_add(1);
        if *total_insns > MAX_TOTAL_INSNS {
            return Err(WasmRunError::InvalidModule(
                "decoded instruction count exceeds MAX_TOTAL_INSNS".into(),
            ));
        }
        let op = cur.read_byte()?;
        match op {
            0x00 => {
                ts.mark_unreachable()?;
                insns.push(Insn::Unreachable);
            }
            0x01 => insns.push(Insn::Nop),
            0x02 => {
                let (start_types, end_types) = parse_block_sig(&mut cur, ctx.types)?;
                ts.pop_vals(&start_types)?;
                let height = ts.vals.len();
                ts.push_vals(&start_types);
                let idx = insns.len();
                insns.push(Insn::Block {
                    param_len: start_types.len(),
                    result_len: end_types.len(),
                    end_pc: 0,
                });
                ts.push_ctrl(CtrlFrame {
                    kind: BlockKind::Block,
                    start_types,
                    end_types,
                    height,
                    unreachable: false,
                    insn_idx: idx,
                    else_idx: None,
                })?;
            }
            0x03 => {
                let (start_types, end_types) = parse_block_sig(&mut cur, ctx.types)?;
                ts.pop_vals(&start_types)?;
                let height = ts.vals.len();
                ts.push_vals(&start_types);
                let idx = insns.len();
                insns.push(Insn::Loop {
                    param_len: start_types.len(),
                    start_pc: idx + 1,
                });
                ts.push_ctrl(CtrlFrame {
                    kind: BlockKind::Loop,
                    start_types,
                    end_types,
                    height,
                    unreachable: false,
                    insn_idx: idx,
                    else_idx: None,
                })?;
            }
            0x04 => {
                let (start_types, end_types) = parse_block_sig(&mut cur, ctx.types)?;
                ts.pop_expect(ValType::I32)?;
                ts.pop_vals(&start_types)?;
                let height = ts.vals.len();
                ts.push_vals(&start_types);
                let idx = insns.len();
                insns.push(Insn::If {
                    param_len: start_types.len(),
                    result_len: end_types.len(),
                    else_pc: None,
                    end_pc: 0,
                });
                ts.push_ctrl(CtrlFrame {
                    kind: BlockKind::If,
                    start_types,
                    end_types,
                    height,
                    unreachable: false,
                    insn_idx: idx,
                    else_idx: None,
                })?;
            }
            0x05 => {
                let top_kind = ts.ctrls.last().map(|f| f.kind);
                if top_kind != Some(BlockKind::If) {
                    return Err(WasmRunError::InvalidModule("invalid else placement".into()));
                }
                let end_types = ts.ctrls.last().unwrap().end_types.clone();
                ts.pop_vals(&end_types)?;
                let frame = ts.ctrls.pop().unwrap();
                if ts.vals.len() != frame.height {
                    return Err(WasmRunError::InvalidModule(
                        "extra values left on stack before else".into(),
                    ));
                }
                let else_idx = insns.len();
                insns.push(Insn::Else { end_pc: 0 });
                if let Insn::If { else_pc, .. } = &mut insns[frame.insn_idx] {
                    *else_pc = Some(else_idx + 1);
                }
                ts.push_vals(&frame.start_types);
                ts.ctrls.push(CtrlFrame {
                    kind: BlockKind::Else,
                    start_types: frame.start_types,
                    end_types: frame.end_types,
                    height: frame.height,
                    unreachable: false,
                    insn_idx: frame.insn_idx,
                    else_idx: Some(else_idx),
                });
            }
            0x0B => {
                let Some(end_types) = ts.ctrls.last().map(|f| f.end_types.clone()) else {
                    return Err(WasmRunError::InvalidModule("extra end opcode".into()));
                };
                ts.pop_vals(&end_types)?;
                let frame = ts.ctrls.pop().unwrap();
                if ts.vals.len() != frame.height {
                    return Err(WasmRunError::InvalidModule(
                        "operand stack height mismatch at block end".into(),
                    ));
                }
                if frame.kind == BlockKind::If && frame.start_types != frame.end_types {
                    return Err(WasmRunError::InvalidModule(
                        "if without else must have matching param and result types".into(),
                    ));
                }
                let end_idx = insns.len();
                insns.push(Insn::End);
                match frame.kind {
                    BlockKind::Func => {
                        if !cur.is_eof() {
                            return Err(WasmRunError::InvalidModule(
                                "trailing bytes after function end".into(),
                            ));
                        }
                        return Ok((extra_locals, insns));
                    }
                    BlockKind::Block => {
                        if let Insn::Block { end_pc, .. } = &mut insns[frame.insn_idx] {
                            *end_pc = end_idx + 1;
                        }
                    }
                    BlockKind::Loop => {}
                    BlockKind::If | BlockKind::Else => {
                        if let Insn::If { end_pc, .. } = &mut insns[frame.insn_idx] {
                            *end_pc = end_idx + 1;
                        }
                        if let Some(e_idx) = frame.else_idx {
                            if let Insn::Else { end_pc } = &mut insns[e_idx] {
                                *end_pc = end_idx + 1;
                            }
                        }
                    }
                }
                ts.push_vals(&frame.end_types);
            }
            0x0C => {
                let d = cur.read_u32_leb()?;
                let lt = ts.label_at(d)?.label_types().to_vec();
                ts.pop_vals(&lt)?;
                ts.mark_unreachable()?;
                insns.push(Insn::Br(d));
            }
            0x0D => {
                let d = cur.read_u32_leb()?;
                ts.pop_expect(ValType::I32)?;
                let lt = ts.label_at(d)?.label_types().to_vec();
                ts.pop_vals(&lt)?;
                ts.push_vals(&lt);
                insns.push(Insn::BrIf(d));
            }
            0x0E => {
                let count = cur.read_u32_leb()? as usize;
                if count > MAX_BR_TABLE_TARGETS || count > cur.remaining() {
                    return Err(WasmRunError::InvalidModule(
                        "br_table target count exceeds limit".into(),
                    ));
                }
                let mut targets = Vec::with_capacity(count);
                for _ in 0..count {
                    targets.push(cur.read_u32_leb()?);
                }
                let default_target = cur.read_u32_leb()?;
                ts.pop_expect(ValType::I32)?;
                let default_lt = ts.label_at(default_target)?.label_types().to_vec();
                let arity = default_lt.len();
                ts.check_peek_vals(&default_lt)?;
                for &d in &targets {
                    let lt = ts.label_at(d)?.label_types().to_vec();
                    if lt.len() != arity {
                        return Err(WasmRunError::InvalidModule(
                            "br_table target label arity mismatch".into(),
                        ));
                    }
                    ts.check_peek_vals(&lt)?;
                }
                for _ in 0..arity {
                    let _ = ts.pop_any()?;
                }
                ts.mark_unreachable()?;
                insns.push(Insn::BrTable {
                    targets,
                    default_target,
                });
            }
            0x0F => {
                let ret_types = ts.ctrls[0].end_types.clone();
                ts.pop_vals(&ret_types)?;
                ts.mark_unreachable()?;
                insns.push(Insn::Return);
            }
            0x10 => {
                let fidx = cur.read_u32_leb()?;
                let &cty_idx = ctx
                    .func_type_indices
                    .get(fidx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("call func index OOB".into()))?;
                let cty = &ctx.types[cty_idx];
                ts.pop_vals(&cty.params)?;
                ts.push_vals(&cty.results);
                insns.push(Insn::Call(fidx));
            }
            0x11 => {
                let type_idx = cur.read_u32_leb()?;
                let table_idx = cur.read_u32_leb()?;
                let cty = ctx.types.get(type_idx as usize).ok_or_else(|| {
                    WasmRunError::InvalidModule("call_indirect type index OOB".into())
                })?;
                if (table_idx as usize) >= ctx.tables.len() {
                    return Err(WasmRunError::InvalidModule(
                        "call_indirect table index OOB".into(),
                    ));
                }
                ts.pop_expect(ValType::I32)?;
                ts.pop_vals(&cty.params)?;
                ts.push_vals(&cty.results);
                insns.push(Insn::CallIndirect {
                    type_idx,
                    table_idx,
                });
            }
            0x1A => {
                let _ = ts.pop_any()?;
                insns.push(Insn::Drop);
            }
            0x1B => {
                ts.pop_expect(ValType::I32)?;
                let t2 = ts.pop_any()?;
                let t1 = ts.pop_any()?;
                let out = match (t1, t2) {
                    (Some(a), Some(b)) => {
                        if a != b || !a.is_numeric() {
                            return Err(WasmRunError::InvalidModule(
                                "untyped select requires matching numeric operands".into(),
                            ));
                        }
                        Some(a)
                    }
                    (Some(a), None) | (None, Some(a)) => {
                        if !a.is_numeric() {
                            return Err(WasmRunError::InvalidModule(
                                "untyped select requires numeric operands".into(),
                            ));
                        }
                        Some(a)
                    }
                    (None, None) => None,
                };
                ts.push_val(out);
                insns.push(Insn::Select);
            }
            0x1C => {
                let n = cur.read_u32_leb()?;
                if n != 1 {
                    return Err(WasmRunError::InvalidModule(
                        "typed select must have arity 1".into(),
                    ));
                }
                let vt = cur.read_valtype()?;
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(vt)?;
                ts.pop_expect(vt)?;
                ts.push_concrete(vt);
                insns.push(Insn::Select);
            }
            0x20 => {
                let idx = cur.read_u32_leb()?;
                let &vt = all_locals
                    .get(idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("local.get index OOB".into()))?;
                ts.push_concrete(vt);
                insns.push(Insn::LocalGet(idx));
            }
            0x21 => {
                let idx = cur.read_u32_leb()?;
                let &vt = all_locals
                    .get(idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("local.set index OOB".into()))?;
                ts.pop_expect(vt)?;
                insns.push(Insn::LocalSet(idx));
            }
            0x22 => {
                let idx = cur.read_u32_leb()?;
                let &vt = all_locals
                    .get(idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("local.tee index OOB".into()))?;
                ts.pop_expect(vt)?;
                ts.push_concrete(vt);
                insns.push(Insn::LocalTee(idx));
            }
            0x23 => {
                let idx = cur.read_u32_leb()?;
                let &(vt, _, _) = ctx
                    .globals
                    .get(idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("global.get index OOB".into()))?;
                ts.push_concrete(vt);
                insns.push(Insn::GlobalGet(idx));
            }
            0x24 => {
                let idx = cur.read_u32_leb()?;
                let &(vt, mutable, _) = ctx
                    .globals
                    .get(idx as usize)
                    .ok_or_else(|| WasmRunError::InvalidModule("global.set index OOB".into()))?;
                if !mutable {
                    return Err(WasmRunError::InvalidModule("immutable global.set".into()));
                }
                ts.pop_expect(vt)?;
                insns.push(Insn::GlobalSet(idx));
            }
            0x25 => {
                let tidx = cur.read_u32_leb()?;
                if (tidx as usize) >= ctx.tables.len() {
                    return Err(WasmRunError::InvalidModule("table.get index OOB".into()));
                }
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::FuncRef);
                insns.push(Insn::TableGet(tidx));
            }
            0x26 => {
                let tidx = cur.read_u32_leb()?;
                if (tidx as usize) >= ctx.tables.len() {
                    return Err(WasmRunError::InvalidModule("table.set index OOB".into()));
                }
                ts.pop_expect(ValType::FuncRef)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::TableSet(tidx));
            }
            0x28 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Load { offset });
            }
            0x29 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 3)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load { offset });
            }
            0x2A => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::F32);
                insns.push(Insn::F32Load { offset });
            }
            0x2B => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 3)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::F64);
                insns.push(Insn::F64Load { offset });
            }
            0x2C => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Load8S { offset });
            }
            0x2D => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Load8U { offset });
            }
            0x2E => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Load16S { offset });
            }
            0x2F => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Load16U { offset });
            }
            0x30 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load8S { offset });
            }
            0x31 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load8U { offset });
            }
            0x32 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load16S { offset });
            }
            0x33 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load16U { offset });
            }
            0x34 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load32S { offset });
            }
            0x35 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Load32U { offset });
            }
            0x36 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I32Store { offset });
            }
            0x37 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 3)?;
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I64Store { offset });
            }
            0x38 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::F32)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::F32Store { offset });
            }
            0x39 => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 3)?;
                ts.pop_expect(ValType::F64)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::F64Store { offset });
            }
            0x3A => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I32Store8 { offset });
            }
            0x3B => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I32Store16 { offset });
            }
            0x3C => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 0)?;
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I64Store8 { offset });
            }
            0x3D => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 1)?;
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I64Store16 { offset });
            }
            0x3E => {
                let offset = read_memarg(&mut cur, ctx.has_memory, 2)?;
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I32)?;
                insns.push(Insn::I64Store32 { offset });
            }
            0x3F => {
                if cur.read_byte()? != 0x00 || !ctx.has_memory {
                    return Err(WasmRunError::InvalidModule("memory.size memidx OOB".into()));
                }
                ts.push_concrete(ValType::I32);
                insns.push(Insn::MemorySize);
            }
            0x40 => {
                if cur.read_byte()? != 0x00 || !ctx.has_memory {
                    return Err(WasmRunError::InvalidModule("memory.grow memidx OOB".into()));
                }
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::MemoryGrow);
            }
            0x41 => {
                let v = cur.read_i32_leb()?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Const(v));
            }
            0x42 => {
                let v = cur.read_i64_leb()?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64Const(v));
            }
            0x43 => {
                let v = cur.read_u32_le()?;
                ts.push_concrete(ValType::F32);
                insns.push(Insn::F32Const(v));
            }
            0x44 => {
                let v = cur.read_u64_le()?;
                ts.push_concrete(ValType::F64);
                insns.push(Insn::F64Const(v));
            }
            0xD0 => {
                if cur.read_byte()? != 0x70 {
                    return Err(WasmRunError::InvalidModule(
                        "unsupported ref.null type (expected funcref 0x70)".into(),
                    ));
                }
                ts.push_concrete(ValType::FuncRef);
                insns.push(Insn::RefNullFunc);
            }
            0xD1 => {
                ts.pop_expect(ValType::FuncRef)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::RefIsNull);
            }
            0xD2 => {
                let fidx = cur.read_u32_leb()?;
                let Some(&declared) = ctx.declared_func_refs.get(fidx as usize) else {
                    return Err(WasmRunError::InvalidModule("ref.func index OOB".into()));
                };
                if !declared {
                    return Err(WasmRunError::InvalidModule(
                        "undeclared function reference in ref.func".into(),
                    ));
                }
                ts.push_concrete(ValType::FuncRef);
                insns.push(Insn::RefFunc(fidx));
            }
            0x45 => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32Eqz);
            }
            0x46..=0x4F => {
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x46 => Insn::I32Eq,
                    0x47 => Insn::I32Ne,
                    0x48 => Insn::I32LtS,
                    0x49 => Insn::I32LtU,
                    0x4A => Insn::I32GtS,
                    0x4B => Insn::I32GtU,
                    0x4C => Insn::I32LeS,
                    0x4D => Insn::I32LeU,
                    0x4E => Insn::I32GeS,
                    _ => Insn::I32GeU,
                });
            }
            0x50 => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I64Eqz);
            }
            0x51..=0x5A => {
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x51 => Insn::I64Eq,
                    0x52 => Insn::I64Ne,
                    0x53 => Insn::I64LtS,
                    0x54 => Insn::I64LtU,
                    0x55 => Insn::I64GtS,
                    0x56 => Insn::I64GtU,
                    0x57 => Insn::I64LeS,
                    0x58 => Insn::I64LeU,
                    0x59 => Insn::I64GeS,
                    _ => Insn::I64GeU,
                });
            }
            0x5B..=0x60 => {
                ts.pop_expect(ValType::F32)?;
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x5B => Insn::F32Eq,
                    0x5C => Insn::F32Ne,
                    0x5D => Insn::F32Lt,
                    0x5E => Insn::F32Gt,
                    0x5F => Insn::F32Le,
                    _ => Insn::F32Ge,
                });
            }
            0x61..=0x66 => {
                ts.pop_expect(ValType::F64)?;
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x61 => Insn::F64Eq,
                    0x62 => Insn::F64Ne,
                    0x63 => Insn::F64Lt,
                    0x64 => Insn::F64Gt,
                    0x65 => Insn::F64Le,
                    _ => Insn::F64Ge,
                });
            }
            0x67..=0x69 => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x67 => Insn::I32Clz,
                    0x68 => Insn::I32Ctz,
                    _ => Insn::I32Popcnt,
                });
            }
            0x6A..=0x78 => {
                ts.pop_expect(ValType::I32)?;
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(match op {
                    0x6A => Insn::I32Add,
                    0x6B => Insn::I32Sub,
                    0x6C => Insn::I32Mul,
                    0x6D => Insn::I32DivS,
                    0x6E => Insn::I32DivU,
                    0x6F => Insn::I32RemS,
                    0x70 => Insn::I32RemU,
                    0x71 => Insn::I32And,
                    0x72 => Insn::I32Or,
                    0x73 => Insn::I32Xor,
                    0x74 => Insn::I32Shl,
                    0x75 => Insn::I32ShrS,
                    0x76 => Insn::I32ShrU,
                    0x77 => Insn::I32Rotl,
                    _ => Insn::I32Rotr,
                });
            }
            0x79..=0x7B => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I64);
                insns.push(match op {
                    0x79 => Insn::I64Clz,
                    0x7A => Insn::I64Ctz,
                    _ => Insn::I64Popcnt,
                });
            }
            0x7C..=0x8A => {
                ts.pop_expect(ValType::I64)?;
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I64);
                insns.push(match op {
                    0x7C => Insn::I64Add,
                    0x7D => Insn::I64Sub,
                    0x7E => Insn::I64Mul,
                    0x7F => Insn::I64DivS,
                    0x80 => Insn::I64DivU,
                    0x81 => Insn::I64RemS,
                    0x82 => Insn::I64RemU,
                    0x83 => Insn::I64And,
                    0x84 => Insn::I64Or,
                    0x85 => Insn::I64Xor,
                    0x86 => Insn::I64Shl,
                    0x87 => Insn::I64ShrS,
                    0x88 => Insn::I64ShrU,
                    0x89 => Insn::I64Rotl,
                    _ => Insn::I64Rotr,
                });
            }
            0x8B..=0x91 => {
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::F32);
                insns.push(match op {
                    0x8B => Insn::F32Abs,
                    0x8C => Insn::F32Neg,
                    0x8D => Insn::F32Ceil,
                    0x8E => Insn::F32Floor,
                    0x8F => Insn::F32Trunc,
                    0x90 => Insn::F32Nearest,
                    _ => Insn::F32Sqrt,
                });
            }
            0x92..=0x98 => {
                ts.pop_expect(ValType::F32)?;
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::F32);
                insns.push(match op {
                    0x92 => Insn::F32Add,
                    0x93 => Insn::F32Sub,
                    0x94 => Insn::F32Mul,
                    0x95 => Insn::F32Div,
                    0x96 => Insn::F32Min,
                    0x97 => Insn::F32Max,
                    _ => Insn::F32Copysign,
                });
            }
            0x99..=0x9F => {
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::F64);
                insns.push(match op {
                    0x99 => Insn::F64Abs,
                    0x9A => Insn::F64Neg,
                    0x9B => Insn::F64Ceil,
                    0x9C => Insn::F64Floor,
                    0x9D => Insn::F64Trunc,
                    0x9E => Insn::F64Nearest,
                    _ => Insn::F64Sqrt,
                });
            }
            0xA0..=0xA6 => {
                ts.pop_expect(ValType::F64)?;
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::F64);
                insns.push(match op {
                    0xA0 => Insn::F64Add,
                    0xA1 => Insn::F64Sub,
                    0xA2 => Insn::F64Mul,
                    0xA3 => Insn::F64Div,
                    0xA4 => Insn::F64Min,
                    0xA5 => Insn::F64Max,
                    _ => Insn::F64Copysign,
                });
            }
            0xA7 => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32WrapI64);
            }
            0xA8 | 0xA9 => {
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::I32);
                insns.push(if op == 0xA8 {
                    Insn::I32TruncF32S
                } else {
                    Insn::I32TruncF32U
                });
            }
            0xAA | 0xAB => {
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::I32);
                insns.push(if op == 0xAA {
                    Insn::I32TruncF64S
                } else {
                    Insn::I32TruncF64U
                });
            }
            0xAC | 0xAD => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I64);
                insns.push(if op == 0xAC {
                    Insn::I64ExtendI32S
                } else {
                    Insn::I64ExtendI32U
                });
            }
            0xAE | 0xAF => {
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::I64);
                insns.push(if op == 0xAE {
                    Insn::I64TruncF32S
                } else {
                    Insn::I64TruncF32U
                });
            }
            0xB0 | 0xB1 => {
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::I64);
                insns.push(if op == 0xB0 {
                    Insn::I64TruncF64S
                } else {
                    Insn::I64TruncF64U
                });
            }
            0xB2 | 0xB3 => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::F32);
                insns.push(if op == 0xB2 {
                    Insn::F32ConvertI32S
                } else {
                    Insn::F32ConvertI32U
                });
            }
            0xB4 | 0xB5 => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::F32);
                insns.push(if op == 0xB4 {
                    Insn::F32ConvertI64S
                } else {
                    Insn::F32ConvertI64U
                });
            }
            0xB6 => {
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::F32);
                insns.push(Insn::F32DemoteF64);
            }
            0xB7 | 0xB8 => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::F64);
                insns.push(if op == 0xB7 {
                    Insn::F64ConvertI32S
                } else {
                    Insn::F64ConvertI32U
                });
            }
            0xB9 | 0xBA => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::F64);
                insns.push(if op == 0xB9 {
                    Insn::F64ConvertI64S
                } else {
                    Insn::F64ConvertI64U
                });
            }
            0xBB => {
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::F64);
                insns.push(Insn::F64PromoteF32);
            }
            0xBC => {
                ts.pop_expect(ValType::F32)?;
                ts.push_concrete(ValType::I32);
                insns.push(Insn::I32ReinterpretF32);
            }
            0xBD => {
                ts.pop_expect(ValType::F64)?;
                ts.push_concrete(ValType::I64);
                insns.push(Insn::I64ReinterpretF64);
            }
            0xBE => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::F32);
                insns.push(Insn::F32ReinterpretI32);
            }
            0xBF => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::F64);
                insns.push(Insn::F64ReinterpretI64);
            }
            0xC0 | 0xC1 => {
                ts.pop_expect(ValType::I32)?;
                ts.push_concrete(ValType::I32);
                insns.push(if op == 0xC0 {
                    Insn::I32Extend8S
                } else {
                    Insn::I32Extend16S
                });
            }
            0xC2..=0xC4 => {
                ts.pop_expect(ValType::I64)?;
                ts.push_concrete(ValType::I64);
                insns.push(match op {
                    0xC2 => Insn::I64Extend8S,
                    0xC3 => Insn::I64Extend16S,
                    _ => Insn::I64Extend32S,
                });
            }
            0xFC => {
                let sub = cur.read_u32_leb()?;
                match sub {
                    0 | 1 => {
                        ts.pop_expect(ValType::F32)?;
                        ts.push_concrete(ValType::I32);
                        insns.push(if sub == 0 {
                            Insn::I32TruncSatF32S
                        } else {
                            Insn::I32TruncSatF32U
                        });
                    }
                    2 | 3 => {
                        ts.pop_expect(ValType::F64)?;
                        ts.push_concrete(ValType::I32);
                        insns.push(if sub == 2 {
                            Insn::I32TruncSatF64S
                        } else {
                            Insn::I32TruncSatF64U
                        });
                    }
                    4 | 5 => {
                        ts.pop_expect(ValType::F32)?;
                        ts.push_concrete(ValType::I64);
                        insns.push(if sub == 4 {
                            Insn::I64TruncSatF32S
                        } else {
                            Insn::I64TruncSatF32U
                        });
                    }
                    6 | 7 => {
                        ts.pop_expect(ValType::F64)?;
                        ts.push_concrete(ValType::I64);
                        insns.push(if sub == 6 {
                            Insn::I64TruncSatF64S
                        } else {
                            Insn::I64TruncSatF64U
                        });
                    }
                    8 => {
                        let data_idx = cur.read_u32_leb()?;
                        let mem_idx = cur.read_byte()?;
                        let Some(dc) = ctx.declared_data_count else {
                            return Err(WasmRunError::InvalidModule(
                                "memory.init requires datacount section".into(),
                            ));
                        };
                        if (data_idx as usize) >= dc || mem_idx != 0x00 || !ctx.has_memory {
                            return Err(WasmRunError::InvalidModule(
                                "memory.init index OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::MemoryInit { data_idx });
                    }
                    9 => {
                        let data_idx = cur.read_u32_leb()?;
                        let Some(dc) = ctx.declared_data_count else {
                            return Err(WasmRunError::InvalidModule(
                                "data.drop requires datacount section".into(),
                            ));
                        };
                        if (data_idx as usize) >= dc {
                            return Err(WasmRunError::InvalidModule("data.drop index OOB".into()));
                        }
                        insns.push(Insn::DataDrop { data_idx });
                    }
                    10 => {
                        let dst_mem = cur.read_byte()?;
                        let src_mem = cur.read_byte()?;
                        if dst_mem != 0x00 || src_mem != 0x00 || !ctx.has_memory {
                            return Err(WasmRunError::InvalidModule(
                                "memory.copy memidx OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::MemoryCopy);
                    }
                    11 => {
                        let mem_idx = cur.read_byte()?;
                        if mem_idx != 0x00 || !ctx.has_memory {
                            return Err(WasmRunError::InvalidModule(
                                "memory.fill memidx OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::MemoryFill);
                    }
                    12 => {
                        let elem_idx = cur.read_u32_leb()?;
                        let table_idx = cur.read_u32_leb()?;
                        if (elem_idx as usize) >= ctx.num_elem_segments
                            || (table_idx as usize) >= ctx.tables.len()
                        {
                            return Err(WasmRunError::InvalidModule(
                                "table.init index OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::TableInit {
                            elem_idx,
                            table_idx,
                        });
                    }
                    13 => {
                        let elem_idx = cur.read_u32_leb()?;
                        if (elem_idx as usize) >= ctx.num_elem_segments {
                            return Err(WasmRunError::InvalidModule(
                                "elem.drop index OOB".into(),
                            ));
                        }
                        insns.push(Insn::ElemDrop { elem_idx });
                    }
                    14 => {
                        let dst_table = cur.read_u32_leb()?;
                        let src_table = cur.read_u32_leb()?;
                        if (dst_table as usize) >= ctx.tables.len()
                            || (src_table as usize) >= ctx.tables.len()
                        {
                            return Err(WasmRunError::InvalidModule(
                                "table.copy index OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::TableCopy {
                            dst_table,
                            src_table,
                        });
                    }
                    15 => {
                        let table_idx = cur.read_u32_leb()?;
                        if (table_idx as usize) >= ctx.tables.len() {
                            return Err(WasmRunError::InvalidModule(
                                "table.grow index OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::FuncRef)?;
                        ts.push_concrete(ValType::I32);
                        insns.push(Insn::TableGrow { table_idx });
                    }
                    16 => {
                        let table_idx = cur.read_u32_leb()?;
                        if (table_idx as usize) >= ctx.tables.len() {
                            return Err(WasmRunError::InvalidModule(
                                "table.size index OOB".into(),
                            ));
                        }
                        ts.push_concrete(ValType::I32);
                        insns.push(Insn::TableSize { table_idx });
                    }
                    17 => {
                        let table_idx = cur.read_u32_leb()?;
                        if (table_idx as usize) >= ctx.tables.len() {
                            return Err(WasmRunError::InvalidModule(
                                "table.fill index OOB".into(),
                            ));
                        }
                        ts.pop_expect(ValType::I32)?;
                        ts.pop_expect(ValType::FuncRef)?;
                        ts.pop_expect(ValType::I32)?;
                        insns.push(Insn::TableFill { table_idx });
                    }
                    other => {
                        return Err(WasmRunError::InvalidModule(format!(
                            "unsupported 0xFC sub-opcode {other:#x}"
                        )))
                    }
                }
            }
            other => {
                return Err(WasmRunError::InvalidModule(format!(
                    "unsupported wasm opcode {other:#x}"
                )))
            }
        }
    }
    Err(WasmRunError::InvalidModule("unclosed function body".into()))
}

#[inline]
fn canon_f32(x: f32) -> u32 {
    if x.is_nan() {
        CANON_F32_NAN_BITS
    } else {
        x.to_bits()
    }
}

#[inline]
fn canon_f64(x: f64) -> u64 {
    if x.is_nan() {
        CANON_F64_NAN_BITS
    } else {
        x.to_bits()
    }
}

#[inline]
fn wasm_f32_min(a_bits: u32, b_bits: u32) -> u32 {
    let a = f32::from_bits(a_bits);
    let b = f32::from_bits(b_bits);
    if a.is_nan() || b.is_nan() {
        CANON_F32_NAN_BITS
    } else if a == 0.0 && b == 0.0 {
        (a_bits | b_bits) & 0x8000_0000
    } else if a < b {
        a.to_bits()
    } else {
        b.to_bits()
    }
}

#[inline]
fn wasm_f32_max(a_bits: u32, b_bits: u32) -> u32 {
    let a = f32::from_bits(a_bits);
    let b = f32::from_bits(b_bits);
    if a.is_nan() || b.is_nan() {
        CANON_F32_NAN_BITS
    } else if a == 0.0 && b == 0.0 {
        (a_bits & b_bits) & 0x8000_0000
    } else if a > b {
        a.to_bits()
    } else {
        b.to_bits()
    }
}

#[inline]
fn wasm_f64_min(a_bits: u64, b_bits: u64) -> u64 {
    let a = f64::from_bits(a_bits);
    let b = f64::from_bits(b_bits);
    if a.is_nan() || b.is_nan() {
        CANON_F64_NAN_BITS
    } else if a == 0.0 && b == 0.0 {
        (a_bits | b_bits) & 0x8000_0000_0000_0000
    } else if a < b {
        a.to_bits()
    } else {
        b.to_bits()
    }
}

#[inline]
fn wasm_f64_max(a_bits: u64, b_bits: u64) -> u64 {
    let a = f64::from_bits(a_bits);
    let b = f64::from_bits(b_bits);
    if a.is_nan() || b.is_nan() {
        CANON_F64_NAN_BITS
    } else if a == 0.0 && b == 0.0 {
        (a_bits & b_bits) & 0x8000_0000_0000_0000
    } else if a > b {
        a.to_bits()
    } else {
        b.to_bits()
    }
}

#[inline]
fn trunc_f32_to_i32_s(x: f32) -> Result<i32, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    // Exact power-of-two bounds in f32: [-2^31, +2^31)
    if !(-2_147_483_648.0_f32..2_147_483_648.0_f32).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as i32)
}

#[inline]
fn trunc_f32_to_u32(x: f32) -> Result<u32, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(0.0_f32..4_294_967_296.0_f32).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as u32)
}

#[inline]
fn trunc_f64_to_i32_s(x: f64) -> Result<i32, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(-2_147_483_648.0_f64..2_147_483_648.0_f64).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as i32)
}

#[inline]
fn trunc_f64_to_u32(x: f64) -> Result<u32, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(0.0_f64..4_294_967_296.0_f64).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as u32)
}

#[inline]
fn trunc_f32_to_i64_s(x: f32) -> Result<i64, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(-9_223_372_036_854_775_808.0_f32..9_223_372_036_854_775_808.0_f32).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as i64)
}

#[inline]
fn trunc_f32_to_u64(x: f32) -> Result<u64, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(0.0_f32..18_446_744_073_709_551_616.0_f32).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as u64)
}

#[inline]
fn trunc_f64_to_i64_s(x: f64) -> Result<i64, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(-9_223_372_036_854_775_808.0_f64..9_223_372_036_854_775_808.0_f64).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as i64)
}

#[inline]
fn trunc_f64_to_u64(x: f64) -> Result<u64, WasmRunError> {
    if x.is_nan() {
        return Err(WasmRunError::Trap("invalid conversion to integer".into()));
    }
    let t = x.trunc();
    if !(0.0_f64..18_446_744_073_709_551_616.0_f64).contains(&t) {
        return Err(WasmRunError::Trap("integer overflow".into()));
    }
    Ok(t as u64)
}

#[inline]
fn checked_mem_range(
    mem_len: usize,
    base_i32: i32,
    offset: u32,
    width: usize,
) -> Result<(usize, usize), WasmRunError> {
    let base = u64::from(base_i32 as u32);
    let ea = base
        .checked_add(u64::from(offset))
        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
    let end = ea
        .checked_add(width as u64)
        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
    if end > mem_len as u64 {
        return Err(WasmRunError::Trap("out of bounds memory access".into()));
    }
    Ok((ea as usize, end as usize))
}

#[derive(Clone, Copy)]
struct Label {
    target_pc: usize,
    stack_height: usize,
    arity: usize,
    is_loop: bool,
    is_func: bool,
}

struct CallFrame {
    func_idx: usize,
    pc: usize,
    base_stack: usize,
    locals: Vec<WasmVal>,
    labels: Vec<Label>,
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

    let start = Instant::now();
    let mut fuel_consumed = 0u64;
    let mut charge_init_fuel = |cost: u64| -> Result<(), WasmRunError> {
        match fuel_consumed.checked_add(cost) {
            Some(next) if next <= budget.max_fuel => {
                fuel_consumed = next;
                Ok(())
            }
            _ => Err(WasmRunError::OutOfFuel {
                max_fuel: budget.max_fuel,
                consumed: budget.max_fuel,
            }),
        }
    };

    let module_digest = sha256(module_bytes);
    check_wall_timeout(&start, budget.max_wall_time)?;
    let parsed = parse_wasm_module(module_bytes, &start, budget.max_wall_time)?;

    // Validate entrypoint & arguments before allocating memory/tables so malformed invocations fail fast.
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
    for a in args {
        if let WasmVal::FuncRef(Some(fidx)) = *a {
            if (fidx as usize) >= parsed.funcs.len() {
                return Err(WasmRunError::SignatureMismatch(format!(
                    "funcref argument index {fidx} OOB (module has {} functions)",
                    parsed.funcs.len()
                )));
            }
        }
    }

    // Instantiate bounded linear memory via fallible reservation.
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
    check_wall_timeout(&start, budget.max_wall_time)?;
    let mut memory = Vec::new();
    memory
        .try_reserve_exact(init_mem_bytes)
        .map_err(|_| WasmRunError::MemoryLimitExceeded {
            requested_bytes: init_mem_bytes,
            max_bytes: budget.max_memory_bytes,
        })?;
    memory.resize(init_mem_bytes, 0u8);

    // Instantiate bounded tables via fallible reservation.
    let mut tables: Vec<Vec<Option<u32>>> = Vec::with_capacity(parsed.tables.len());
    for tt in &parsed.tables {
        let min_elems = tt.min as usize;
        if min_elems > MAX_TABLE_ELEMENTS {
            return Err(WasmRunError::MemoryLimitExceeded {
                requested_bytes: min_elems.saturating_mul(4),
                max_bytes: MAX_TABLE_ELEMENTS * 4,
            });
        }
        let mut tbl = Vec::new();
        tbl.try_reserve_exact(min_elems)
            .map_err(|_| WasmRunError::MemoryLimitExceeded {
                requested_bytes: min_elems.saturating_mul(4),
                max_bytes: MAX_TABLE_ELEMENTS * 4,
            })?;
        tbl.resize(min_elems, None);
        tables.push(tbl);
    }

    // Instantiate globals.
    let mut globals: Vec<(bool, WasmVal)> = parsed
        .globals
        .iter()
        .map(|&(_, mutable, val)| (mutable, val))
        .collect();

    // Initialize active element segments and build runtime passive element segments.
    let mut runtime_elems: Vec<Vec<Option<u32>>> = Vec::with_capacity(parsed.elem_segments.len());
    for seg in &parsed.elem_segments {
        check_wall_timeout(&start, budget.max_wall_time)?;
        match seg {
            ElemSegment::Active {
                table_idx,
                offset,
                init,
            } => {
                charge_init_fuel((init.len() as u64) / 64)?;
                let tbl = &mut tables[*table_idx];
                let off = u64::from(*offset);
                let end = off
                    .checked_add(init.len() as u64)
                    .ok_or_else(|| WasmRunError::Trap("element segment overflow".into()))?;
                if end > tbl.len() as u64 {
                    return Err(WasmRunError::Trap(
                        "out of bounds table access in active element segment".into(),
                    ));
                }
                tbl[*offset as usize..end as usize].copy_from_slice(init);
                runtime_elems.push(Vec::new()); // Active segment is dropped after init per spec
            }
            ElemSegment::Passive(init) => {
                charge_init_fuel((init.len() as u64) / 64)?;
                runtime_elems.push(init.clone());
            }
            ElemSegment::Declarative => runtime_elems.push(Vec::new()),
        }
    }

    // Initialize active data segments and build zero-copy passive data segment slices.
    let mut runtime_data: Vec<&[u8]> = Vec::with_capacity(parsed.data_segments.len());
    for seg in &parsed.data_segments {
        check_wall_timeout(&start, budget.max_wall_time)?;
        let raw = &module_bytes[seg.byte_start..seg.byte_end];
        match seg.kind {
            DataSegmentKind::Active { offset } => {
                charge_init_fuel((raw.len() as u64) / 64)?;
                let off = u64::from(offset);
                let end = off
                    .checked_add(raw.len() as u64)
                    .ok_or_else(|| WasmRunError::Trap("data segment overflow".into()))?;
                if end > memory.len() as u64 {
                    return Err(WasmRunError::Trap(
                        "out of bounds memory access in active data segment".into(),
                    ));
                }
                memory[offset as usize..end as usize].copy_from_slice(raw);
                runtime_data.push(&[]); // Active segment is dropped after init per Bulk-Memory spec
            }
            DataSegmentKind::Passive => runtime_data.push(raw),
        }
    }

    let mut peak_memory_bytes = memory.len();
    let mut stack: Vec<WasmVal> = Vec::with_capacity(64);

    let mut vm = VmExec {
        parsed: &parsed,
        budget,
        start,
        fuel_consumed: &mut fuel_consumed,
        peak_memory_bytes: &mut peak_memory_bytes,
        memory: &mut memory,
        tables: &mut tables,
        runtime_elems: &mut runtime_elems,
        runtime_data: &mut runtime_data,
        globals: &mut globals,
        stack: &mut stack,
        step_counter: 0,
    };

    if let Some(start_idx) = parsed.start_func {
        vm.run_root_call(start_idx, Vec::new())?;
    }
    vm.run_root_call(func_idx, args.to_vec())?;
    check_wall_timeout(&start, budget.max_wall_time)?;

    if stack.len() != entry_ty.results.len()
        || stack
            .iter()
            .zip(&entry_ty.results)
            .any(|(v, expected)| v.ty() != *expected)
    {
        return Err(WasmRunError::Trap("unexpected result stack arity or type".into()));
    }
    let tier_rec = ReproducibilityTier::R2DeterministicGrain;
    let egress_rec = EgressPosture::DenyByConstruction;
    let commitment = compute_wasm_commitment(
        &module_digest,
        entrypoint,
        args,
        &stack,
        fuel_consumed,
        peak_memory_bytes,
        tier_rec,
        egress_rec,
    );
    Ok(WasmExecutionReceipt {
        module_digest,
        entrypoint: entrypoint.to_string(),
        results: stack,
        fuel_consumed,
        peak_memory_bytes,
        tier: tier_rec,
        egress: egress_rec,
        commitment,
    })
}

struct VmExec<'a, 'm> {
    parsed: &'a ParsedModule,
    budget: &'a WasmExecutionBudget,
    start: Instant,
    fuel_consumed: &'a mut u64,
    peak_memory_bytes: &'a mut usize,
    memory: &'a mut Vec<u8>,
    tables: &'a mut [Vec<Option<u32>>],
    runtime_elems: &'a mut [Vec<Option<u32>>],
    runtime_data: &'a mut [&'m [u8]],
    globals: &'a mut [(bool, WasmVal)],
    stack: &'a mut Vec<WasmVal>,
    step_counter: u32,
}

impl<'a, 'm> VmExec<'a, 'm> {
    #[inline]
    fn charge_fuel(&mut self, cost: u64) -> Result<(), WasmRunError> {
        match self.fuel_consumed.checked_add(cost) {
            Some(next) if next <= self.budget.max_fuel => {
                *self.fuel_consumed = next;
                Ok(())
            }
            _ => {
                *self.fuel_consumed = self.budget.max_fuel;
                Err(WasmRunError::OutOfFuel {
                    max_fuel: self.budget.max_fuel,
                    consumed: self.budget.max_fuel,
                })
            }
        }
    }

    #[inline]
    fn push_val(&mut self, v: WasmVal) -> Result<(), WasmRunError> {
        if self.stack.len() >= self.budget.max_stack_values {
            return Err(WasmRunError::StackOverflow);
        }
        self.stack.push(v);
        Ok(())
    }

    #[inline]
    fn pop_val(&mut self, floor: usize) -> Result<WasmVal, WasmRunError> {
        if self.stack.len() <= floor {
            return Err(WasmRunError::Trap("operand stack underflow".into()));
        }
        self.stack
            .pop()
            .ok_or_else(|| WasmRunError::Trap("operand stack underflow".into()))
    }

    #[inline]
    fn pop_i32(&mut self, floor: usize) -> Result<i32, WasmRunError> {
        match self.pop_val(floor)? {
            WasmVal::I32(v) => Ok(v),
            _ => Err(WasmRunError::Trap("expected i32 on stack".into())),
        }
    }

    #[inline]
    fn pop_i64(&mut self, floor: usize) -> Result<i64, WasmRunError> {
        match self.pop_val(floor)? {
            WasmVal::I64(v) => Ok(v),
            _ => Err(WasmRunError::Trap("expected i64 on stack".into())),
        }
    }

    #[inline]
    fn pop_f32(&mut self, floor: usize) -> Result<u32, WasmRunError> {
        match self.pop_val(floor)? {
            WasmVal::F32(bits) => Ok(bits),
            _ => Err(WasmRunError::Trap("expected f32 on stack".into())),
        }
    }

    #[inline]
    fn pop_f64(&mut self, floor: usize) -> Result<u64, WasmRunError> {
        match self.pop_val(floor)? {
            WasmVal::F64(bits) => Ok(bits),
            _ => Err(WasmRunError::Trap("expected f64 on stack".into())),
        }
    }

    #[inline]
    fn pop_funcref(&mut self, floor: usize) -> Result<Option<u32>, WasmRunError> {
        match self.pop_val(floor)? {
            WasmVal::FuncRef(r) => Ok(r),
            _ => Err(WasmRunError::Trap("expected funcref on stack".into())),
        }
    }

    fn make_frame(
        &self,
        func_idx: usize,
        call_args: Vec<WasmVal>,
        live_locals: &mut usize,
    ) -> Result<CallFrame, WasmRunError> {
        let func = self
            .parsed
            .funcs
            .get(func_idx)
            .ok_or_else(|| WasmRunError::InvalidModule("call func index OOB".into()))?;
        let fty = &self.parsed.types[func.ty_idx];
        let total_frame_locals = call_args.len() + func.extra_locals.len();
        if live_locals.saturating_add(total_frame_locals) > MAX_LIVE_LOCALS_TOTAL {
            return Err(WasmRunError::StackOverflow);
        }
        *live_locals += total_frame_locals;

        let mut locals = Vec::with_capacity(total_frame_locals);
        locals.extend(call_args);
        for &vt in &func.extra_locals {
            locals.push(WasmVal::default_for(vt));
        }

        let base_stack = self.stack.len();
        let labels = vec![Label {
            target_pc: func.insns.len(),
            stack_height: base_stack,
            arity: fty.results.len(),
            is_loop: false,
            is_func: true,
        }];
        Ok(CallFrame {
            func_idx,
            pc: 0,
            base_stack,
            locals,
            labels,
        })
    }

    fn unwind_branch(
        stack: &mut Vec<WasmVal>,
        labels: &mut Vec<Label>,
        depth_idx: u32,
    ) -> Result<Option<usize>, WasmRunError> {
        let target_label_pos = labels
            .len()
            .checked_sub(1 + depth_idx as usize)
            .ok_or_else(|| WasmRunError::InvalidModule("branch depth OOB".into()))?;
        let lbl = labels[target_label_pos];
        let stack_len = stack.len();
        let src_start = stack_len
            .checked_sub(lbl.arity)
            .ok_or_else(|| WasmRunError::Trap("branch stack underflow".into()))?;
        if src_start < lbl.stack_height {
            return Err(WasmRunError::Trap("branch stack frame underflow".into()));
        }
        if lbl.arity > 0 && src_start != lbl.stack_height {
            stack.copy_within(src_start..stack_len, lbl.stack_height);
        }
        stack.truncate(lbl.stack_height + lbl.arity);

        if lbl.is_func {
            return Ok(None);
        }
        if lbl.is_loop {
            labels.truncate(target_label_pos + 1);
        } else {
            labels.truncate(target_label_pos);
        }
        Ok(Some(lbl.target_pc))
    }

    fn run_root_call(
        &mut self,
        root_func_idx: usize,
        root_args: Vec<WasmVal>,
    ) -> Result<(), WasmRunError> {
        if self.budget.max_call_depth == 0 {
            return Err(WasmRunError::CallDepthExceeded { max_depth: 0 });
        }
        let mut live_locals = 0usize;
        let mut frames = Vec::with_capacity(self.budget.max_call_depth.min(64));
        frames.push(self.make_frame(root_func_idx, root_args, &mut live_locals)?);

        while let Some(frame) = frames.last_mut() {
            let func = &self.parsed.funcs[frame.func_idx];
            if frame.pc >= func.insns.len() {
                live_locals = live_locals.saturating_sub(frame.locals.len());
                frames.pop();
                continue;
            }

            self.step_counter = self.step_counter.wrapping_add(1);
            if (self.step_counter & 0xFF) == 0 {
                if let Some(limit) = self.budget.max_wall_time {
                    if self.start.elapsed() > limit {
                        return Err(WasmRunError::WallTimeoutExceeded {
                            limit_ms: limit.as_millis() as u64,
                        });
                    }
                }
            }

            let insn = &func.insns[frame.pc];
            self.charge_fuel(insn.fuel_cost())?;
            let floor = frame.base_stack;

            match *insn {
                Insn::Unreachable => {
                    return Err(WasmRunError::Trap("unreachable executed".into()))
                }
                Insn::Nop => frame.pc += 1,
                Insn::Block {
                    param_len,
                    result_len,
                    end_pc,
                } => {
                    let sh = self
                        .stack
                        .len()
                        .checked_sub(param_len)
                        .ok_or_else(|| WasmRunError::Trap("block param underflow".into()))?;
                    frame.labels.push(Label {
                        target_pc: end_pc,
                        stack_height: sh,
                        arity: result_len,
                        is_loop: false,
                        is_func: false,
                    });
                    frame.pc += 1;
                }
                Insn::Loop {
                    param_len,
                    start_pc,
                } => {
                    let sh = self
                        .stack
                        .len()
                        .checked_sub(param_len)
                        .ok_or_else(|| WasmRunError::Trap("loop param underflow".into()))?;
                    frame.labels.push(Label {
                        target_pc: start_pc,
                        stack_height: sh,
                        arity: param_len,
                        is_loop: true,
                        is_func: false,
                    });
                    frame.pc += 1;
                }
                Insn::If {
                    param_len,
                    result_len,
                    else_pc,
                    end_pc,
                } => {
                    let cond = self.pop_i32(floor)?;
                    let sh = self
                        .stack
                        .len()
                        .checked_sub(param_len)
                        .ok_or_else(|| WasmRunError::Trap("if param underflow".into()))?;
                    if cond != 0 {
                        frame.labels.push(Label {
                            target_pc: end_pc,
                            stack_height: sh,
                            arity: result_len,
                            is_loop: false,
                            is_func: false,
                        });
                        frame.pc += 1;
                    } else if let Some(epc) = else_pc {
                        frame.labels.push(Label {
                            target_pc: end_pc,
                            stack_height: sh,
                            arity: result_len,
                            is_loop: false,
                            is_func: false,
                        });
                        frame.pc = epc;
                    } else {
                        frame.pc = end_pc;
                    }
                }
                Insn::Else { end_pc } => {
                    frame.labels.pop();
                    frame.pc = end_pc;
                }
                Insn::End => {
                    let Some(lbl) = frame.labels.pop() else {
                        live_locals = live_locals.saturating_sub(frame.locals.len());
                        frames.pop();
                        continue;
                    };
                    if lbl.is_func {
                        live_locals = live_locals.saturating_sub(frame.locals.len());
                        frames.pop();
                    } else {
                        frame.pc += 1;
                    }
                }
                Insn::Br(d) => match Self::unwind_branch(self.stack, &mut frame.labels, d)? {
                    Some(next_pc) => frame.pc = next_pc,
                    None => {
                        live_locals = live_locals.saturating_sub(frame.locals.len());
                        frames.pop();
                    }
                },
                Insn::BrIf(d) => {
                    let cond = self.pop_i32(floor)?;
                    if cond != 0 {
                        match Self::unwind_branch(self.stack, &mut frame.labels, d)? {
                            Some(next_pc) => frame.pc = next_pc,
                            None => {
                                live_locals = live_locals.saturating_sub(frame.locals.len());
                                frames.pop();
                            }
                        }
                    } else {
                        frame.pc += 1;
                    }
                }
                Insn::BrTable {
                    ref targets,
                    default_target,
                } => {
                    let idx = self.pop_i32(floor)? as u32 as usize;
                    let d = targets.get(idx).copied().unwrap_or(default_target);
                    match Self::unwind_branch(self.stack, &mut frame.labels, d)? {
                        Some(next_pc) => frame.pc = next_pc,
                        None => {
                            live_locals = live_locals.saturating_sub(frame.locals.len());
                            frames.pop();
                        }
                    }
                }
                Insn::Return => {
                    let depth_to_func = (frame.labels.len() - 1) as u32;
                    let _ = Self::unwind_branch(self.stack, &mut frame.labels, depth_to_func)?;
                    live_locals = live_locals.saturating_sub(frame.locals.len());
                    frames.pop();
                }
                Insn::Call(callee_u32) => {
                    let callee_idx = callee_u32 as usize;
                    let callee = self
                        .parsed
                        .funcs
                        .get(callee_idx)
                        .ok_or_else(|| WasmRunError::InvalidModule("callee OOB".into()))?;
                    let cty = &self.parsed.types[callee.ty_idx];
                    let mut cargs = Vec::with_capacity(cty.params.len());
                    for _ in 0..cty.params.len() {
                        cargs.push(self.pop_val(floor)?);
                    }
                    cargs.reverse();
                    frame.pc += 1;
                    if frames.len() >= self.budget.max_call_depth {
                        return Err(WasmRunError::CallDepthExceeded {
                            max_depth: self.budget.max_call_depth,
                        });
                    }
                    let next_frame = self.make_frame(callee_idx, cargs, &mut live_locals)?;
                    frames.push(next_frame);
                }
                Insn::CallIndirect {
                    type_idx,
                    table_idx,
                } => {
                    let elem_idx = self.pop_i32(floor)? as u32 as usize;
                    let tbl = self
                        .tables
                        .get(table_idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("table OOB".into()))?;
                    if elem_idx >= tbl.len() {
                        return Err(WasmRunError::Trap(
                            "undefined element: call_indirect index out of bounds".into(),
                        ));
                    }
                    let callee_idx = tbl[elem_idx].ok_or_else(|| {
                        WasmRunError::Trap("uninitialized element: null funcref".into())
                    })? as usize;
                    let callee = self
                        .parsed
                        .funcs
                        .get(callee_idx)
                        .ok_or_else(|| WasmRunError::InvalidModule("callee OOB".into()))?;
                    let actual_ty = &self.parsed.types[callee.ty_idx];
                    let expected_ty = &self.parsed.types[type_idx as usize];
                    if actual_ty != expected_ty {
                        return Err(WasmRunError::Trap(format!(
                            "indirect call type mismatch: expected {:?} -> {:?}, got {:?} -> {:?}",
                            expected_ty.params,
                            expected_ty.results,
                            actual_ty.params,
                            actual_ty.results
                        )));
                    }
                    let mut cargs = Vec::with_capacity(expected_ty.params.len());
                    for _ in 0..expected_ty.params.len() {
                        cargs.push(self.pop_val(floor)?);
                    }
                    cargs.reverse();
                    frame.pc += 1;
                    if frames.len() >= self.budget.max_call_depth {
                        return Err(WasmRunError::CallDepthExceeded {
                            max_depth: self.budget.max_call_depth,
                        });
                    }
                    let next_frame = self.make_frame(callee_idx, cargs, &mut live_locals)?;
                    frames.push(next_frame);
                }
                Insn::Drop => {
                    let _ = self.pop_val(floor)?;
                    frame.pc += 1;
                }
                Insn::Select => {
                    let c = self.pop_i32(floor)?;
                    let v2 = self.pop_val(floor)?;
                    let v1 = self.pop_val(floor)?;
                    self.push_val(if c != 0 { v1 } else { v2 })?;
                    frame.pc += 1;
                }
                Insn::LocalGet(idx) => {
                    let v = *frame
                        .locals
                        .get(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.get OOB".into()))?;
                    self.push_val(v)?;
                    frame.pc += 1;
                }
                Insn::LocalSet(idx) => {
                    let v = self.pop_val(floor)?;
                    let slot = frame
                        .locals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.set OOB".into()))?;
                    *slot = v;
                    frame.pc += 1;
                }
                Insn::LocalTee(idx) => {
                    if self.stack.len() <= floor {
                        return Err(WasmRunError::Trap("stack underflow".into()));
                    }
                    let v = *self
                        .stack
                        .last()
                        .ok_or_else(|| WasmRunError::Trap("stack underflow".into()))?;
                    let slot = frame
                        .locals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("local.tee OOB".into()))?;
                    *slot = v;
                    frame.pc += 1;
                }
                Insn::GlobalGet(idx) => {
                    let (_, v) = *self
                        .globals
                        .get(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("global.get OOB".into()))?;
                    self.push_val(v)?;
                    frame.pc += 1;
                }
                Insn::GlobalSet(idx) => {
                    let v = self.pop_val(floor)?;
                    let (mutable, slot) = self
                        .globals
                        .get_mut(idx as usize)
                        .ok_or_else(|| WasmRunError::InvalidModule("global.set OOB".into()))?;
                    if !*mutable {
                        return Err(WasmRunError::InvalidModule("immutable global.set".into()));
                    }
                    *slot = v;
                    frame.pc += 1;
                }
                Insn::TableGet(tidx) => {
                    let elem_idx = self.pop_i32(floor)? as u32 as usize;
                    let tbl = &self.tables[tidx as usize];
                    let r = *tbl.get(elem_idx).ok_or_else(|| {
                        WasmRunError::Trap("out of bounds table access".into())
                    })?;
                    self.push_val(WasmVal::FuncRef(r))?;
                    frame.pc += 1;
                }
                Insn::TableSet(tidx) => {
                    let r = self.pop_funcref(floor)?;
                    let elem_idx = self.pop_i32(floor)? as u32 as usize;
                    let tbl = &mut self.tables[tidx as usize];
                    let slot = tbl.get_mut(elem_idx).ok_or_else(|| {
                        WasmRunError::Trap("out of bounds table access".into())
                    })?;
                    *slot = r;
                    frame.pc += 1;
                }
                Insn::I32Load { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    let b = &self.memory[s..e];
                    let v = i32::from_le_bytes([b[0], b[1], b[2], b[3]]);
                    self.push_val(WasmVal::I32(v))?;
                    frame.pc += 1;
                }
                Insn::I64Load { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 8)?;
                    let b = &self.memory[s..e];
                    let v = i64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                    self.push_val(WasmVal::I64(v))?;
                    frame.pc += 1;
                }
                Insn::F32Load { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    let b = &self.memory[s..e];
                    let bits = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
                    self.push_val(WasmVal::F32(bits))?;
                    frame.pc += 1;
                }
                Insn::F64Load { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 8)?;
                    let b = &self.memory[s..e];
                    let bits = u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                    self.push_val(WasmVal::F64(bits))?;
                    frame.pc += 1;
                }
                Insn::I32Load8S { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.push_val(WasmVal::I32(i32::from(self.memory[s] as i8)))?;
                    frame.pc += 1;
                }
                Insn::I32Load8U { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.push_val(WasmVal::I32(i32::from(self.memory[s])))?;
                    frame.pc += 1;
                }
                Insn::I32Load16S { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I32(i32::from(i16::from_le_bytes([b[0], b[1]]))))?;
                    frame.pc += 1;
                }
                Insn::I32Load16U { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I32(i32::from(u16::from_le_bytes([b[0], b[1]]))))?;
                    frame.pc += 1;
                }
                Insn::I64Load8S { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.push_val(WasmVal::I64(i64::from(self.memory[s] as i8)))?;
                    frame.pc += 1;
                }
                Insn::I64Load8U { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.push_val(WasmVal::I64(i64::from(self.memory[s])))?;
                    frame.pc += 1;
                }
                Insn::I64Load16S { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I64(i64::from(i16::from_le_bytes([b[0], b[1]]))))?;
                    frame.pc += 1;
                }
                Insn::I64Load16U { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I64(i64::from(u16::from_le_bytes([b[0], b[1]]))))?;
                    frame.pc += 1;
                }
                Insn::I64Load32S { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I64(i64::from(i32::from_le_bytes([
                        b[0], b[1], b[2], b[3],
                    ]))))?;
                    frame.pc += 1;
                }
                Insn::I64Load32U { offset } => {
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    let b = &self.memory[s..e];
                    self.push_val(WasmVal::I64(i64::from(u32::from_le_bytes([
                        b[0], b[1], b[2], b[3],
                    ]))))?;
                    frame.pc += 1;
                }
                Insn::I32Store { offset } => {
                    let val = self.pop_i32(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    self.memory[s..e].copy_from_slice(&val.to_le_bytes());
                    frame.pc += 1;
                }
                Insn::I64Store { offset } => {
                    let val = self.pop_i64(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 8)?;
                    self.memory[s..e].copy_from_slice(&val.to_le_bytes());
                    frame.pc += 1;
                }
                Insn::F32Store { offset } => {
                    let bits = self.pop_f32(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    self.memory[s..e].copy_from_slice(&bits.to_le_bytes());
                    frame.pc += 1;
                }
                Insn::F64Store { offset } => {
                    let bits = self.pop_f64(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 8)?;
                    self.memory[s..e].copy_from_slice(&bits.to_le_bytes());
                    frame.pc += 1;
                }
                Insn::I32Store8 { offset } => {
                    let val = self.pop_i32(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.memory[s] = val as u8;
                    frame.pc += 1;
                }
                Insn::I32Store16 { offset } => {
                    let val = self.pop_i32(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    self.memory[s..e].copy_from_slice(&(val as u16).to_le_bytes());
                    frame.pc += 1;
                }
                Insn::I64Store8 { offset } => {
                    let val = self.pop_i64(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, _) = checked_mem_range(self.memory.len(), base, offset, 1)?;
                    self.memory[s] = val as u8;
                    frame.pc += 1;
                }
                Insn::I64Store16 { offset } => {
                    let val = self.pop_i64(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 2)?;
                    self.memory[s..e].copy_from_slice(&(val as u16).to_le_bytes());
                    frame.pc += 1;
                }
                Insn::I64Store32 { offset } => {
                    let val = self.pop_i64(floor)?;
                    let base = self.pop_i32(floor)?;
                    let (s, e) = checked_mem_range(self.memory.len(), base, offset, 4)?;
                    self.memory[s..e].copy_from_slice(&(val as u32).to_le_bytes());
                    frame.pc += 1;
                }
                Insn::MemorySize => {
                    let pages = (self.memory.len() / WASM_PAGE_SIZE) as i32;
                    self.push_val(WasmVal::I32(pages))?;
                    frame.pc += 1;
                }
                Insn::MemoryGrow => {
                    let delta_pages = self.pop_i32(floor)? as u32 as usize;
                    let cur_pages = self.memory.len() / WASM_PAGE_SIZE;
                    let new_pages = cur_pages.saturating_add(delta_pages);
                    let new_bytes = new_pages.saturating_mul(WASM_PAGE_SIZE);
                    let max_pages_ok = new_pages <= MAX_WASM32_PAGES
                        && self.parsed.mem_max_pages.is_none_or(|mp| new_pages <= mp);
                    if !max_pages_ok {
                        self.push_val(WasmVal::I32(-1))?;
                    } else if new_bytes > self.budget.max_memory_bytes {
                        return Err(WasmRunError::MemoryLimitExceeded {
                            requested_bytes: new_bytes,
                            max_bytes: self.budget.max_memory_bytes,
                        });
                    } else {
                        check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                        let extra_fuel = (delta_pages as u64).saturating_mul(8);
                        self.charge_fuel(extra_fuel)?;
                        let add_bytes = new_bytes.saturating_sub(self.memory.len());
                        self.memory
                            .try_reserve(add_bytes)
                            .map_err(|_| WasmRunError::MemoryLimitExceeded {
                                requested_bytes: new_bytes,
                                max_bytes: self.budget.max_memory_bytes,
                            })?;
                        self.memory.resize(new_bytes, 0u8);
                        *self.peak_memory_bytes = (*self.peak_memory_bytes).max(new_bytes);
                        self.push_val(WasmVal::I32(cur_pages as i32))?;
                    }
                    frame.pc += 1;
                }
                Insn::I32Const(v) => {
                    self.push_val(WasmVal::I32(v))?;
                    frame.pc += 1;
                }
                Insn::I64Const(v) => {
                    self.push_val(WasmVal::I64(v))?;
                    frame.pc += 1;
                }
                Insn::F32Const(bits) => {
                    self.push_val(WasmVal::F32(bits))?;
                    frame.pc += 1;
                }
                Insn::F64Const(bits) => {
                    self.push_val(WasmVal::F64(bits))?;
                    frame.pc += 1;
                }
                Insn::RefNullFunc => {
                    self.push_val(WasmVal::FuncRef(None))?;
                    frame.pc += 1;
                }
                Insn::RefIsNull => {
                    let r = self.pop_funcref(floor)?;
                    self.push_val(WasmVal::I32(i32::from(r.is_none())))?;
                    frame.pc += 1;
                }
                Insn::RefFunc(fidx) => {
                    self.push_val(WasmVal::FuncRef(Some(fidx)))?;
                    frame.pc += 1;
                }
                Insn::I32Eqz => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::I32(i32::from(a == 0)))?;
                    frame.pc += 1;
                }
                Insn::I32Eq
                | Insn::I32Ne
                | Insn::I32LtS
                | Insn::I32LtU
                | Insn::I32GtS
                | Insn::I32GtU
                | Insn::I32LeS
                | Insn::I32LeU
                | Insn::I32GeS
                | Insn::I32GeU => {
                    let b = self.pop_i32(floor)?;
                    let a = self.pop_i32(floor)?;
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
                    self.push_val(WasmVal::I32(i32::from(res)))?;
                    frame.pc += 1;
                }
                Insn::I64Eqz => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::I32(i32::from(a == 0)))?;
                    frame.pc += 1;
                }
                Insn::I64Eq
                | Insn::I64Ne
                | Insn::I64LtS
                | Insn::I64LtU
                | Insn::I64GtS
                | Insn::I64GtU
                | Insn::I64LeS
                | Insn::I64LeU
                | Insn::I64GeS
                | Insn::I64GeU => {
                    let b = self.pop_i64(floor)?;
                    let a = self.pop_i64(floor)?;
                    let res = match insn {
                        Insn::I64Eq => a == b,
                        Insn::I64Ne => a != b,
                        Insn::I64LtS => a < b,
                        Insn::I64LtU => (a as u64) < (b as u64),
                        Insn::I64GtS => a > b,
                        Insn::I64GtU => (a as u64) > (b as u64),
                        Insn::I64LeS => a <= b,
                        Insn::I64LeU => (a as u64) <= (b as u64),
                        Insn::I64GeS => a >= b,
                        Insn::I64GeU => (a as u64) >= (b as u64),
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::I32(i32::from(res)))?;
                    frame.pc += 1;
                }
                Insn::F32Eq
                | Insn::F32Ne
                | Insn::F32Lt
                | Insn::F32Gt
                | Insn::F32Le
                | Insn::F32Ge => {
                    let b = f32::from_bits(self.pop_f32(floor)?);
                    let a = f32::from_bits(self.pop_f32(floor)?);
                    let res = match insn {
                        Insn::F32Eq => a == b,
                        Insn::F32Ne => a != b,
                        Insn::F32Lt => a < b,
                        Insn::F32Gt => a > b,
                        Insn::F32Le => a <= b,
                        Insn::F32Ge => a >= b,
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::I32(i32::from(res)))?;
                    frame.pc += 1;
                }
                Insn::F64Eq
                | Insn::F64Ne
                | Insn::F64Lt
                | Insn::F64Gt
                | Insn::F64Le
                | Insn::F64Ge => {
                    let b = f64::from_bits(self.pop_f64(floor)?);
                    let a = f64::from_bits(self.pop_f64(floor)?);
                    let res = match insn {
                        Insn::F64Eq => a == b,
                        Insn::F64Ne => a != b,
                        Insn::F64Lt => a < b,
                        Insn::F64Gt => a > b,
                        Insn::F64Le => a <= b,
                        Insn::F64Ge => a >= b,
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::I32(i32::from(res)))?;
                    frame.pc += 1;
                }
                Insn::I32Clz | Insn::I32Ctz | Insn::I32Popcnt => {
                    let a = self.pop_i32(floor)? as u32;
                    let v = match insn {
                        Insn::I32Clz => a.leading_zeros() as i32,
                        Insn::I32Ctz => a.trailing_zeros() as i32,
                        _ => a.count_ones() as i32,
                    };
                    self.push_val(WasmVal::I32(v))?;
                    frame.pc += 1;
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
                | Insn::I32ShrU
                | Insn::I32Rotl
                | Insn::I32Rotr => {
                    let b = self.pop_i32(floor)?;
                    let a = self.pop_i32(floor)?;
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
                        Insn::I32Rotl => (a as u32).rotate_left(b as u32) as i32,
                        Insn::I32Rotr => (a as u32).rotate_right(b as u32) as i32,
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::I32(v))?;
                    frame.pc += 1;
                }
                Insn::I64Clz | Insn::I64Ctz | Insn::I64Popcnt => {
                    let a = self.pop_i64(floor)? as u64;
                    let v = match insn {
                        Insn::I64Clz => i64::from(a.leading_zeros()),
                        Insn::I64Ctz => i64::from(a.trailing_zeros()),
                        _ => i64::from(a.count_ones()),
                    };
                    self.push_val(WasmVal::I64(v))?;
                    frame.pc += 1;
                }
                Insn::I64Add
                | Insn::I64Sub
                | Insn::I64Mul
                | Insn::I64DivS
                | Insn::I64DivU
                | Insn::I64RemS
                | Insn::I64RemU
                | Insn::I64And
                | Insn::I64Or
                | Insn::I64Xor
                | Insn::I64Shl
                | Insn::I64ShrS
                | Insn::I64ShrU
                | Insn::I64Rotl
                | Insn::I64Rotr => {
                    let b = self.pop_i64(floor)?;
                    let a = self.pop_i64(floor)?;
                    let v = match insn {
                        Insn::I64Add => a.wrapping_add(b),
                        Insn::I64Sub => a.wrapping_sub(b),
                        Insn::I64Mul => a.wrapping_mul(b),
                        Insn::I64DivS => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            if a == i64::MIN && b == -1 {
                                return Err(WasmRunError::Trap("integer overflow".into()));
                            }
                            a / b
                        }
                        Insn::I64DivU => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            ((a as u64) / (b as u64)) as i64
                        }
                        Insn::I64RemS => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            a.wrapping_rem(b)
                        }
                        Insn::I64RemU => {
                            if b == 0 {
                                return Err(WasmRunError::Trap("integer divide by zero".into()));
                            }
                            ((a as u64) % (b as u64)) as i64
                        }
                        Insn::I64And => a & b,
                        Insn::I64Or => a | b,
                        Insn::I64Xor => a ^ b,
                        Insn::I64Shl => a.wrapping_shl(b as u32),
                        Insn::I64ShrS => a.wrapping_shr(b as u32),
                        Insn::I64ShrU => ((a as u64).wrapping_shr(b as u32)) as i64,
                        Insn::I64Rotl => (a as u64).rotate_left(b as u32) as i64,
                        Insn::I64Rotr => (a as u64).rotate_right(b as u32) as i64,
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::I64(v))?;
                    frame.pc += 1;
                }
                Insn::F32Abs
                | Insn::F32Neg
                | Insn::F32Ceil
                | Insn::F32Floor
                | Insn::F32Trunc
                | Insn::F32Nearest
                | Insn::F32Sqrt => {
                    let bits = self.pop_f32(floor)?;
                    let out = match insn {
                        Insn::F32Abs => bits & 0x7fff_ffff,
                        Insn::F32Neg => bits ^ 0x8000_0000,
                        Insn::F32Ceil => canon_f32(f32::from_bits(bits).ceil()),
                        Insn::F32Floor => canon_f32(f32::from_bits(bits).floor()),
                        Insn::F32Trunc => canon_f32(f32::from_bits(bits).trunc()),
                        Insn::F32Nearest => canon_f32(f32::from_bits(bits).round_ties_even()),
                        // Exact IEEE-754 f32 sqrt via f64::sqrt (provably free of double-rounding)
                        Insn::F32Sqrt => canon_f32(f64::from(f32::from_bits(bits)).sqrt() as f32),
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::F32(out))?;
                    frame.pc += 1;
                }
                Insn::F32Add
                | Insn::F32Sub
                | Insn::F32Mul
                | Insn::F32Div
                | Insn::F32Min
                | Insn::F32Max
                | Insn::F32Copysign => {
                    let b_bits = self.pop_f32(floor)?;
                    let a_bits = self.pop_f32(floor)?;
                    let out = match insn {
                        Insn::F32Add => canon_f32(f32::from_bits(a_bits) + f32::from_bits(b_bits)),
                        Insn::F32Sub => canon_f32(f32::from_bits(a_bits) - f32::from_bits(b_bits)),
                        Insn::F32Mul => canon_f32(f32::from_bits(a_bits) * f32::from_bits(b_bits)),
                        Insn::F32Div => canon_f32(f32::from_bits(a_bits) / f32::from_bits(b_bits)),
                        Insn::F32Min => wasm_f32_min(a_bits, b_bits),
                        Insn::F32Max => wasm_f32_max(a_bits, b_bits),
                        Insn::F32Copysign => (a_bits & 0x7fff_ffff) | (b_bits & 0x8000_0000),
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::F32(out))?;
                    frame.pc += 1;
                }
                Insn::F64Abs
                | Insn::F64Neg
                | Insn::F64Ceil
                | Insn::F64Floor
                | Insn::F64Trunc
                | Insn::F64Nearest
                | Insn::F64Sqrt => {
                    let bits = self.pop_f64(floor)?;
                    let out = match insn {
                        Insn::F64Abs => bits & 0x7fff_ffff_ffff_ffff,
                        Insn::F64Neg => bits ^ 0x8000_0000_0000_0000,
                        Insn::F64Ceil => canon_f64(f64::from_bits(bits).ceil()),
                        Insn::F64Floor => canon_f64(f64::from_bits(bits).floor()),
                        Insn::F64Trunc => canon_f64(f64::from_bits(bits).trunc()),
                        Insn::F64Nearest => canon_f64(f64::from_bits(bits).round_ties_even()),
                        Insn::F64Sqrt => canon_f64(f64::from_bits(bits).sqrt()),
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::F64(out))?;
                    frame.pc += 1;
                }
                Insn::F64Add
                | Insn::F64Sub
                | Insn::F64Mul
                | Insn::F64Div
                | Insn::F64Min
                | Insn::F64Max
                | Insn::F64Copysign => {
                    let b_bits = self.pop_f64(floor)?;
                    let a_bits = self.pop_f64(floor)?;
                    let out = match insn {
                        Insn::F64Add => canon_f64(f64::from_bits(a_bits) + f64::from_bits(b_bits)),
                        Insn::F64Sub => canon_f64(f64::from_bits(a_bits) - f64::from_bits(b_bits)),
                        Insn::F64Mul => canon_f64(f64::from_bits(a_bits) * f64::from_bits(b_bits)),
                        Insn::F64Div => canon_f64(f64::from_bits(a_bits) / f64::from_bits(b_bits)),
                        Insn::F64Min => wasm_f64_min(a_bits, b_bits),
                        Insn::F64Max => wasm_f64_max(a_bits, b_bits),
                        Insn::F64Copysign => {
                            (a_bits & 0x7fff_ffff_ffff_ffff) | (b_bits & 0x8000_0000_0000_0000)
                        }
                        _ => unreachable!(),
                    };
                    self.push_val(WasmVal::F64(out))?;
                    frame.pc += 1;
                }
                Insn::I32WrapI64 => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::I32(a as i32))?;
                    frame.pc += 1;
                }
                Insn::I32TruncF32S => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I32(trunc_f32_to_i32_s(x)?))?;
                    frame.pc += 1;
                }
                Insn::I32TruncF32U => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I32(trunc_f32_to_u32(x)? as i32))?;
                    frame.pc += 1;
                }
                Insn::I32TruncF64S => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I32(trunc_f64_to_i32_s(x)?))?;
                    frame.pc += 1;
                }
                Insn::I32TruncF64U => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I32(trunc_f64_to_u32(x)? as i32))?;
                    frame.pc += 1;
                }
                Insn::I64ExtendI32S => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::I64(i64::from(a)))?;
                    frame.pc += 1;
                }
                Insn::I64ExtendI32U => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::I64(i64::from(a as u32)))?;
                    frame.pc += 1;
                }
                Insn::I64TruncF32S => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I64(trunc_f32_to_i64_s(x)?))?;
                    frame.pc += 1;
                }
                Insn::I64TruncF32U => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I64(trunc_f32_to_u64(x)? as i64))?;
                    frame.pc += 1;
                }
                Insn::I64TruncF64S => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I64(trunc_f64_to_i64_s(x)?))?;
                    frame.pc += 1;
                }
                Insn::I64TruncF64U => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I64(trunc_f64_to_u64(x)? as i64))?;
                    frame.pc += 1;
                }
                Insn::F32ConvertI32S => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::F32((a as f32).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F32ConvertI32U => {
                    let a = self.pop_i32(floor)? as u32;
                    self.push_val(WasmVal::F32((a as f32).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F32ConvertI64S => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::F32((a as f32).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F32ConvertI64U => {
                    let a = self.pop_i64(floor)? as u64;
                    self.push_val(WasmVal::F32((a as f32).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F32DemoteF64 => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::F32(canon_f32(x as f32)))?;
                    frame.pc += 1;
                }
                Insn::F64ConvertI32S => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::F64(f64::from(a).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F64ConvertI32U => {
                    let a = self.pop_i32(floor)? as u32;
                    self.push_val(WasmVal::F64(f64::from(a).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F64ConvertI64S => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::F64((a as f64).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F64ConvertI64U => {
                    let a = self.pop_i64(floor)? as u64;
                    self.push_val(WasmVal::F64((a as f64).to_bits()))?;
                    frame.pc += 1;
                }
                Insn::F64PromoteF32 => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::F64(canon_f64(f64::from(x))))?;
                    frame.pc += 1;
                }
                Insn::I32ReinterpretF32 => {
                    let bits = self.pop_f32(floor)?;
                    self.push_val(WasmVal::I32(bits as i32))?;
                    frame.pc += 1;
                }
                Insn::I64ReinterpretF64 => {
                    let bits = self.pop_f64(floor)?;
                    self.push_val(WasmVal::I64(bits as i64))?;
                    frame.pc += 1;
                }
                Insn::F32ReinterpretI32 => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::F32(a as u32))?;
                    frame.pc += 1;
                }
                Insn::F64ReinterpretI64 => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::F64(a as u64))?;
                    frame.pc += 1;
                }
                Insn::I32Extend8S => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::I32(i32::from(a as i8)))?;
                    frame.pc += 1;
                }
                Insn::I32Extend16S => {
                    let a = self.pop_i32(floor)?;
                    self.push_val(WasmVal::I32(i32::from(a as i16)))?;
                    frame.pc += 1;
                }
                Insn::I64Extend8S => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::I64(i64::from(a as i8)))?;
                    frame.pc += 1;
                }
                Insn::I64Extend16S => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::I64(i64::from(a as i16)))?;
                    frame.pc += 1;
                }
                Insn::I64Extend32S => {
                    let a = self.pop_i64(floor)?;
                    self.push_val(WasmVal::I64(i64::from(a as i32)))?;
                    frame.pc += 1;
                }
                Insn::I32TruncSatF32S => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I32(x as i32))?;
                    frame.pc += 1;
                }
                Insn::I32TruncSatF32U => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I32((x as u32) as i32))?;
                    frame.pc += 1;
                }
                Insn::I32TruncSatF64S => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I32(x as i32))?;
                    frame.pc += 1;
                }
                Insn::I32TruncSatF64U => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I32((x as u32) as i32))?;
                    frame.pc += 1;
                }
                Insn::I64TruncSatF32S => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I64(x as i64))?;
                    frame.pc += 1;
                }
                Insn::I64TruncSatF32U => {
                    let x = f32::from_bits(self.pop_f32(floor)?);
                    self.push_val(WasmVal::I64((x as u64) as i64))?;
                    frame.pc += 1;
                }
                Insn::I64TruncSatF64S => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I64(x as i64))?;
                    frame.pc += 1;
                }
                Insn::I64TruncSatF64U => {
                    let x = f64::from_bits(self.pop_f64(floor)?);
                    self.push_val(WasmVal::I64((x as u64) as i64))?;
                    frame.pc += 1;
                }
                Insn::MemoryInit { data_idx } => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let s = u64::from(self.pop_i32(floor)? as u32);
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let seg = self.runtime_data[data_idx as usize];
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let s_end = s
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    if d_end > self.memory.len() as u64 || s_end > seg.len() as u64 {
                        return Err(WasmRunError::Trap("out of bounds memory access".into()));
                    }
                    if n > 0 {
                        self.memory[d as usize..d_end as usize]
                            .copy_from_slice(&seg[s as usize..s_end as usize]);
                    }
                    frame.pc += 1;
                }
                Insn::DataDrop { data_idx } => {
                    self.runtime_data[data_idx as usize] = &[];
                    frame.pc += 1;
                }
                Insn::MemoryCopy => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let s = u64::from(self.pop_i32(floor)? as u32);
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let s_end = s
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    let mem_len = self.memory.len() as u64;
                    if d_end > mem_len || s_end > mem_len {
                        return Err(WasmRunError::Trap("out of bounds memory access".into()));
                    }
                    if n > 0 {
                        self.memory
                            .copy_within(s as usize..s_end as usize, d as usize);
                    }
                    frame.pc += 1;
                }
                Insn::MemoryFill => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let val = self.pop_i32(floor)? as u8;
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds memory access".into()))?;
                    if d_end > self.memory.len() as u64 {
                        return Err(WasmRunError::Trap("out of bounds memory access".into()));
                    }
                    if n > 0 {
                        self.memory[d as usize..d_end as usize].fill(val);
                    }
                    frame.pc += 1;
                }
                Insn::TableInit {
                    elem_idx,
                    table_idx,
                } => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let s = u64::from(self.pop_i32(floor)? as u32);
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let seg = &self.runtime_elems[elem_idx as usize];
                    let tbl = &mut self.tables[table_idx as usize];
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds table access".into()))?;
                    let s_end = s
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds table access".into()))?;
                    if d_end > tbl.len() as u64 || s_end > seg.len() as u64 {
                        return Err(WasmRunError::Trap("out of bounds table access".into()));
                    }
                    if n > 0 {
                        tbl[d as usize..d_end as usize]
                            .copy_from_slice(&seg[s as usize..s_end as usize]);
                    }
                    frame.pc += 1;
                }
                Insn::ElemDrop { elem_idx } => {
                    self.runtime_elems[elem_idx as usize].clear();
                    frame.pc += 1;
                }
                Insn::TableCopy {
                    dst_table,
                    src_table,
                } => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let s = u64::from(self.pop_i32(floor)? as u32);
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds table access".into()))?;
                    let s_end = s
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds table access".into()))?;
                    if dst_table == src_table {
                        let tbl = &mut self.tables[dst_table as usize];
                        let len = tbl.len() as u64;
                        if d_end > len || s_end > len {
                            return Err(WasmRunError::Trap("out of bounds table access".into()));
                        }
                        if n > 0 {
                            tbl.copy_within(s as usize..s_end as usize, d as usize);
                        }
                    } else {
                        let dst_len = self.tables[dst_table as usize].len() as u64;
                        let src_len = self.tables[src_table as usize].len() as u64;
                        if d_end > dst_len || s_end > src_len {
                            return Err(WasmRunError::Trap("out of bounds table access".into()));
                        }
                        if n > 0 {
                            let tmp =
                                self.tables[src_table as usize][s as usize..s_end as usize].to_vec();
                            self.tables[dst_table as usize][d as usize..d_end as usize]
                                .copy_from_slice(&tmp);
                        }
                    }
                    frame.pc += 1;
                }
                Insn::TableGrow { table_idx } => {
                    let delta = self.pop_i32(floor)? as u32 as usize;
                    let init_ref = self.pop_funcref(floor)?;
                    let old_len = self.tables[table_idx as usize].len();
                    let new_len = old_len.saturating_add(delta);
                    let max_ok = new_len <= MAX_TABLE_ELEMENTS
                        && self.parsed.tables[table_idx as usize]
                            .max
                            .is_none_or(|m| new_len <= m as usize);
                    if !max_ok {
                        self.push_val(WasmVal::I32(-1))?;
                    } else {
                        check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                        self.charge_fuel((delta as u64) / 64)?;
                        let tbl = &mut self.tables[table_idx as usize];
                        let add_elems = new_len.saturating_sub(old_len);
                        if tbl.try_reserve(add_elems).is_err() {
                            self.push_val(WasmVal::I32(-1))?;
                        } else {
                            tbl.resize(new_len, init_ref);
                            self.push_val(WasmVal::I32(old_len as i32))?;
                        }
                    }
                    frame.pc += 1;
                }
                Insn::TableSize { table_idx } => {
                    let len = self.tables[table_idx as usize].len() as i32;
                    self.push_val(WasmVal::I32(len))?;
                    frame.pc += 1;
                }
                Insn::TableFill { table_idx } => {
                    check_wall_timeout(&self.start, self.budget.max_wall_time)?;
                    let n = u64::from(self.pop_i32(floor)? as u32);
                    let val = self.pop_funcref(floor)?;
                    let d = u64::from(self.pop_i32(floor)? as u32);
                    self.charge_fuel(n / 64)?;
                    let tbl = &mut self.tables[table_idx as usize];
                    let d_end = d
                        .checked_add(n)
                        .ok_or_else(|| WasmRunError::Trap("out of bounds table access".into()))?;
                    if d_end > tbl.len() as u64 {
                        return Err(WasmRunError::Trap("out of bounds table access".into()));
                    }
                    if n > 0 {
                        tbl[d as usize..d_end as usize].fill(val);
                    }
                    frame.pc += 1;
                }
            }
        }
        Ok(())
    }
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
        // Mutating `egress` invalidates receipt verification (`gpt-6.2-astra` audit finding #3).
        let mut tampered = receipt.clone();
        tampered.egress = EgressPosture::NoEngineNoEgress;
        assert!(!tampered.verify_commitment(&args));
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

    #[test]
    fn bulk_memory_fill_charges_proportional_fuel_before_copying() {
        // `(module (memory 1) (func (export "fill") (param i32) i32.const 0 i32.const 0xAA local.get 0 memory.fill))`
        let wasm_fill: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x01, 0x7f, 0x00, // (i32) -> ()
            0x03, 0x02, 0x01, 0x00,
            0x05, 0x03, 0x01, 0x00, 0x01, // memory 1 page
            0x07, 0x08, 0x01, 0x04, b'f', b'i', b'l', b'l', 0x00, 0x00,
            0x0a, 0x0e, 0x01, 0x0c, 0x00,
            0x41, 0x00, // d = 0
            0x41, 0xaa, 0x01, // val = 0xAA
            0x20, 0x00, // n = param 0
            0xfc, 0x0b, 0x00, // memory.fill 0
            0x0b,
        ];
        // Attempting `memory.fill(0, 0xAA, 100_000_000)` on 50 fuel traps with `OutOfFuel` BEFORE touching memory.
        let res = run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_fill,
            "fill",
            &[WasmVal::I32(100_000_000)],
            &WasmExecutionBudget::new(50, 65_536),
        );
        assert_eq!(
            res,
            Err(WasmRunError::OutOfFuel {
                max_fuel: 50,
                consumed: 50
            })
        );

        // Within-budget 128-byte fill consumes: 3 pushes + (1 + 128/64 = 3) + end = 7 fuel.
        let ok = run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_fill,
            "fill",
            &[WasmVal::I32(128)],
            &WasmExecutionBudget::new(50, 65_536),
        )
        .unwrap();
        assert_eq!(ok.fuel_consumed, 7);
    }

    #[test]
    fn u32_max_offset_load_never_wraps_and_static_type_confusion_is_rejected() {
        // `(module (memory 1) (func (export "oob") (param i32) (result i32) local.get 0 i32.load offset=0xffffffff))`
        let wasm_u32max_off: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
            0x03, 0x02, 0x01, 0x00,
            0x05, 0x03, 0x01, 0x00, 0x01,
            0x07, 0x07, 0x01, 0x03, b'o', b'o', b'b', 0x00, 0x00,
            0x0a, 0x0d, 0x01, 0x0b, 0x00,
            0x20, 0x00, // base = param 0 (pass 1 -> 1 + 0xFFFF_FFFF = 0x1_0000_0000, would wrap to 0 on u32!)
            0x28, 0x02, 0xff, 0xff, 0xff, 0xff, 0x0f, // i32.load align=4 offset=u32::MAX
            0x0b,
        ];
        let trap = run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_u32max_off,
            "oob",
            &[WasmVal::I32(1)],
            &WasmExecutionBudget::default(),
        );
        assert!(matches!(trap, Err(WasmRunError::Trap(m)) if m.contains("out of bounds")));

        // Malformed module returning `f32` from `() -> i32` via `br 0` is rejected at load time!
        let bad_branch_type: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // () -> i32
            0x03, 0x02, 0x01, 0x00,
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
            0x0a, 0x0b, 0x01, 0x09, 0x00,
            0x43, 0x00, 0x00, 0x80, 0x3f, // f32.const 1.0
            0x0c, 0x00, // br 0 (into i32 result!)
            0x0b,
        ];
        assert!(matches!(
            run_wasm_metered(
                WasmCapTier::Sandboxed,
                bad_branch_type,
                "run",
                &[],
                &WasmExecutionBudget::default()
            ),
            Err(WasmRunError::InvalidModule(_))
        ));
    }

    #[test]
    fn ieee754_float_ops_and_canonical_nan_normalization_are_deterministic() {
        // Verify Wasm `min`/`max` propagate NaN to canonical quiet NaN and order `-0.0 < +0.0`.
        let neg_nan = 0xfff8_0000_0000_dead_u64;
        let one = 1.0_f64.to_bits();
        assert_eq!(wasm_f64_min(neg_nan, one), CANON_F64_NAN_BITS);
        assert_eq!(wasm_f64_max(one, neg_nan), CANON_F64_NAN_BITS);
        assert_eq!(wasm_f64_min((-0.0_f64).to_bits(), 0.0_f64.to_bits()), (-0.0_f64).to_bits());
        assert_eq!(wasm_f64_max((-0.0_f64).to_bits(), 0.0_f64.to_bits()), 0.0_f64.to_bits());

        // Verify trapping trunc edge cases (`-0.5 -> 0` for unsigned, `-1.0 -> Trap`, `2^31 -> Trap`).
        assert_eq!(trunc_f64_to_u32(-0.5).unwrap(), 0);
        assert!(trunc_f64_to_u32(-1.0).is_err());
        assert!(trunc_f32_to_i32_s(2_147_483_648.0_f32).is_err());
        assert!(trunc_f32_to_i64_s(9_223_372_036_854_775_808.0_f32).is_err());
    }

    #[test]
    fn polymorphic_br_table_passive_segments_start_and_mem_max_semantics_hold() {
        // 1. Polymorphic unreachable `br_table 0 1` where target 0 expects `f32` and target 1 expects `i32`
        // is valid per Wasm 2.0 / Reference-Types §3.3.8.8 (`gpt-6.2-astra` finding #4).
        let poly_br_table: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // () -> i32
            0x03, 0x02, 0x01, 0x00,
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
            0x0a, 0x17, 0x01, 0x15, 0x00,
            0x41, 0x00, // i32.const 0 (skip unreachable then-branch at runtime while validating it statically!)
            0x04, 0x7d, // if (result f32)
            0x00, // unreachable
            0x0e, 0x01, 0x00, 0x01, // br_table [0 -> f32] default=1 (-> func i32)
            0x05, // else
            0x43, 0x00, 0x00, 0x80, 0x3f, // f32.const 1.0
            0x0b, // end
            0x1a, // drop
            0x41, 0x07, // i32.const 7
            0x0b,
        ];
        let rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            poly_br_table,
            "run",
            &[],
            &WasmExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(rec.results, vec![WasmVal::I32(7)]);

        // Concrete `f32` operand pushed after `unreachable` before `br_table 0 1` (where target 1 expects `i32`) MUST fail validation!
        let bad_poly_br_table: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
            0x03, 0x02, 0x01, 0x00,
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
            0x0a, 0x16, 0x01, 0x14, 0x00,
            0x02, 0x7d,
            0x00,
            0x43, 0x00, 0x00, 0x80, 0x3f, // f32.const 1.0
            0x41, 0x00, // selector = 0
            0x0e, 0x01, 0x00, 0x01, // target 1 expects i32 != concrete f32!
            0x0b,
            0x1a,
            0x41, 0x07,
            0x0b,
        ];
        assert!(matches!(
            run_wasm_metered(
                WasmCapTier::Sandboxed,
                bad_poly_br_table,
                "run",
                &[],
                &WasmExecutionBudget::default()
            ),
            Err(WasmRunError::InvalidModule(_))
        ));

        // 2. Padded LEB128 reserved zero byte (`0x80, 0x00`) on `memory.size` is rejected (`gpt-6.2-astra` finding #6).
        let padded_memsize: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
            0x03, 0x02, 0x01, 0x00,
            0x05, 0x03, 0x01, 0x00, 0x01,
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
            0x0a, 0x07, 0x01, 0x05, 0x00, 0x3f, 0x80, 0x00, 0x0b,
        ];
        assert!(matches!(
            run_wasm_metered(
                WasmCapTier::Sandboxed,
                padded_memsize,
                "run",
                &[],
                &WasmExecutionBudget::default()
            ),
            Err(WasmRunError::InvalidModule(_))
        ));

        // 3. Module-declared `(memory 1 1)` returns `-1` on `memory.grow(1)` even under a 1-page host budget (`gpt-6.2-astra` finding #7).
        let mem_max_1: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
            0x03, 0x02, 0x01, 0x00,
            0x05, 0x04, 0x01, 0x01, 0x01, 0x01, // (memory 1 1)
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
            0x0a, 0x08, 0x01, 0x06, 0x00, 0x41, 0x01, 0x40, 0x00, 0x0b, // i32.const 1; memory.grow 0
        ];
        let mg_rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            mem_max_1,
            "run",
            &[],
            &WasmExecutionBudget::new(500, 65_536),
        )
        .unwrap();
        assert_eq!(mg_rec.results, vec![WasmVal::I32(-1)]);

        // 4. `Start (8)` + `DataCount (12)` + passive `Data` (`memory.init` + `data.drop`) + passive `Element` (`table.init` + `elem.drop`).
        let passive_and_start: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            // Type 0: () -> (), Type 1: () -> i32
            0x01, 0x08, 0x02, 0x60, 0x00, 0x00, 0x60, 0x00, 0x01, 0x7f,
            // Func 0 (start: () -> ()), Func 1 (callee: () -> i32), Func 2 (run: () -> i32)
            0x03, 0x04, 0x03, 0x00, 0x01, 0x01,
            // Table 0: funcref min=1
            0x04, 0x04, 0x01, 0x70, 0x00, 0x01,
            // Memory 0: min=1
            0x05, 0x03, 0x01, 0x00, 0x01,
            // Export "run" -> func 2
            0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x02,
            // Start -> func 0
            0x08, 0x01, 0x00,
            // Element 0 (passive mode=1, elemkind=0x00, [func 1])
            0x09, 0x05, 0x01, 0x01, 0x00, 0x01, 0x01,
            // DataCount = 1 (section 12 precedes Code section 10!)
            0x0c, 0x01, 0x01,
            // Code:
            // Func 0 (start): memory.init 0 (d=0, s=0, n=4); data.drop 0; table.init 0 0 (d=0, s=0, n=1); elem.drop 0; end
            // Func 1: i32.const 0; i32.load align=4 offset=0; end
            // Func 2 ("run"): i32.const 0; call_indirect (type 1, table 0); end
            0x0a, 0x2e, 0x03,
            0x1c, 0x00,
            0x41, 0x00, 0x41, 0x00, 0x41, 0x04, 0xfc, 0x08, 0x00, 0x00,
            0xfc, 0x09, 0x00,
            0x41, 0x00, 0x41, 0x00, 0x41, 0x01, 0xfc, 0x0c, 0x00, 0x00,
            0xfc, 0x0d, 0x00,
            0x0b,
            0x07, 0x00, 0x41, 0x00, 0x28, 0x02, 0x00, 0x0b,
            0x07, 0x00, 0x41, 0x00, 0x11, 0x01, 0x00, 0x0b,
            // Data 0 (passive mode=1, bytes=[0x78, 0x56, 0x34, 0x12] -> 0x1234_5678 LE)
            0x0b, 0x07, 0x01, 0x01, 0x04, 0x78, 0x56, 0x34, 0x12,
        ];
        let ps_rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            passive_and_start,
            "run",
            &[],
            &WasmExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(ps_rec.results, vec![WasmVal::I32(0x1234_5678)]);
    }
}
