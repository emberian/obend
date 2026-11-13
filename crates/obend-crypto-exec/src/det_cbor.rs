//! Strict **RFC 8949 §4.2 Deterministic CBOR** Encoder & Canonical Decoder,
//! `DualPcsReceipt` Wire Format for Lean C-ABI / CLI Stranger Workflows,
//! and 2-Bit Lexer Redaction Confinement Guard (`F8` defense).

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use crate::canopy::{
    CanopyBatchedProof, CanopyCommitment, CanopyError, CanopyOpenedColumn, CanopyParams,
    HashInvocationStats, canopy_commit, canopy_open, canopy_verify,
};
use crate::goldilocks::{
    CanonicalLiftError, Goldilocks, GoldilocksExecError, GoldilocksExt2, SumcheckRoundPolyExt2,
    mle_eval_base_at_ext2, prove_multilinear_sumcheck_ext2, verify_sumcheck_ext2,
};
use crate::pikkufold::{
    AkitaFoldProof, AkitaFoldRound, GADGET_LIMB_MAX, HALF_Q_LAT, LatticeCommitment, LatticeError,
    LatticeParams, RING_DEGREE, RingElem, akita_prove_open, akita_verify_open, commit_ring_witness,
    pack_goldilocks_to_ring_witness, unpack_ring_witness_to_goldilocks,
};
use crate::transcript::{
    DUAL_TRACK1_LABEL, DUAL_TRACK2_LABEL, FenziTranscript, leb128,
};

/// Maximum nesting depth permitted by the strict `DetCbor` decoder.
pub const MAX_CBOR_DEPTH: usize = 64;

/// Current canonical wire schema version for `DualPcsReceipt`.
pub const DUAL_PCS_RECEIPT_SCHEMA_VERSION: u64 = 2;

/// Errors returned by strict RFC 8949 §4.2 Deterministic CBOR encoding/decoding or `DualPcsReceipt` checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DetCborError {
    UnexpectedEof,
    TrailingBytes { remaining: usize },
    NonMinimalInteger { additional_info: u8, value: u64 },
    IndefiniteLengthForbidden,
    FloatForbidden { initial_byte: u8 },
    TagForbidden { tag_info: u8 },
    ReservedAdditionalInfo(u8),
    UnsupportedSimpleValue(u8),
    InvalidUtf8Text,
    DuplicateMapKey,
    UnsortedMapKeys,
    MaxDepthExceeded,
    LengthOverflow,
    SchemaMismatch(String),
    MissingField(&'static str),
    UnexpectedFieldCount { expected: usize, actual: usize },
    NonCanonicalGoldilocks(CanonicalLiftError),
    NonCanonicalLatticeCoeff(i64),
    GoldilocksFailure(GoldilocksExecError),
    CanopyFailure(CanopyError),
    LatticeFailure(LatticeError),
    FinalTranscriptDigestMismatch,
    ReducedClaimMismatch,
}

impl fmt::Display for DetCborError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl From<CanonicalLiftError> for DetCborError {
    fn from(e: CanonicalLiftError) -> Self {
        Self::NonCanonicalGoldilocks(e)
    }
}

impl From<GoldilocksExecError> for DetCborError {
    fn from(e: GoldilocksExecError) -> Self {
        Self::GoldilocksFailure(e)
    }
}

impl From<CanopyError> for DetCborError {
    fn from(e: CanopyError) -> Self {
        Self::CanopyFailure(e)
    }
}

impl From<LatticeError> for DetCborError {
    fn from(e: LatticeError) -> Self {
        Self::LatticeFailure(e)
    }
}

/// Float-free RFC 8949 §4.2 Deterministic CBOR AST.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CborValue {
    /// Major type 0: unsigned integer in `0..=u64::MAX`.
    Unsigned(u64),
    /// Major type 1: negative integer `-1 - n` for `n` in `0..=u64::MAX`.
    NegInt(u64),
    /// Major type 2: definite-length byte string.
    Bytes(Vec<u8>),
    /// Major type 3: definite-length valid UTF-8 text string.
    Text(String),
    /// Major type 4: definite-length array.
    Array(Vec<CborValue>),
    /// Major type 5: definite-length map (sorted in bytewise lexicographic order of encoded keys).
    Map(Vec<(CborValue, CborValue)>),
    /// Major type 7 (`20` / `21`): boolean (matching `Obend.Codec.DetCbor.CborVal.simpleBool`;
    /// `0xf6` `Null` and floats are forbidden).
    Bool(bool),
}

impl CborValue {
    /// Construct signed `i64` in canonical Major 0 or Major 1 representation.
    #[inline]
    pub const fn from_i64(v: i64) -> Self {
        if v >= 0 {
            Self::Unsigned(v as u64)
        } else {
            // v < 0 => -1 - v == (!v) as u64
            Self::NegInt((!v) as u64)
        }
    }

    /// Extract a signed `i64` if in `i64::MIN..=i64::MAX`.
    pub fn as_i64(&self) -> Result<i64, DetCborError> {
        match *self {
            Self::Unsigned(u) => i64::try_from(u)
                .map_err(|_| DetCborError::SchemaMismatch(String::from("u64 overflows i64"))),
            Self::NegInt(n) => {
                if n > (i64::MAX as u64) {
                    Err(DetCborError::SchemaMismatch(String::from("negint underflows i64")))
                } else {
                    Ok(!(n as i64))
                }
            }
            _ => Err(DetCborError::SchemaMismatch(String::from("expected integer"))),
        }
    }

    pub fn as_u64(&self) -> Result<u64, DetCborError> {
        match *self {
            Self::Unsigned(u) => Ok(u),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected unsigned integer"))),
        }
    }

    pub fn as_bytes(&self) -> Result<&[u8], DetCborError> {
        match self {
            Self::Bytes(b) => Ok(b),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected byte string"))),
        }
    }

    pub fn as_fixed_bytes<const N: usize>(&self) -> Result<[u8; N], DetCborError> {
        let b = self.as_bytes()?;
        if b.len() != N {
            return Err(DetCborError::SchemaMismatch(String::from("fixed byte length mismatch")));
        }
        let mut out = [0u8; N];
        out.copy_from_slice(b);
        Ok(out)
    }

    pub fn as_text(&self) -> Result<&str, DetCborError> {
        match self {
            Self::Text(s) => Ok(s),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected text string"))),
        }
    }

    pub fn as_bool(&self) -> Result<bool, DetCborError> {
        match *self {
            Self::Bool(b) => Ok(b),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected bool"))),
        }
    }

    pub fn as_array(&self) -> Result<&[CborValue], DetCborError> {
        match self {
            Self::Array(a) => Ok(a),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected array"))),
        }
    }

    pub fn as_map(&self) -> Result<&[(CborValue, CborValue)], DetCborError> {
        match self {
            Self::Map(m) => Ok(m),
            _ => Err(DetCborError::SchemaMismatch(String::from("expected map"))),
        }
    }
}

// ============================================================================
// RFC 8949 §4.2 Deterministic CBOR Encoder & Strict Canonical Decoder
// ============================================================================

#[inline]
fn write_type_and_arg(out: &mut Vec<u8>, major: u8, arg: u64) {
    let prefix = major << 5;
    if arg <= 23 {
        out.push(prefix | (arg as u8));
    } else if arg <= 0xFF {
        out.push(prefix | 24);
        out.push(arg as u8);
    } else if arg <= 0xFFFF {
        out.push(prefix | 25);
        out.extend_from_slice(&(arg as u16).to_be_bytes());
    } else if arg <= 0xFFFF_FFFF {
        out.push(prefix | 26);
        out.extend_from_slice(&(arg as u32).to_be_bytes());
    } else {
        out.push(prefix | 27);
        out.extend_from_slice(&arg.to_be_bytes());
    }
}

fn encode_value_into(val: &CborValue, out: &mut Vec<u8>, depth: usize) -> Result<(), DetCborError> {
    if depth > MAX_CBOR_DEPTH {
        return Err(DetCborError::MaxDepthExceeded);
    }
    match val {
        CborValue::Unsigned(u) => write_type_and_arg(out, 0, *u),
        CborValue::NegInt(n) => write_type_and_arg(out, 1, *n),
        CborValue::Bytes(b) => {
            write_type_and_arg(out, 2, b.len() as u64);
            out.extend_from_slice(b);
        }
        CborValue::Text(s) => {
            let bytes = s.as_bytes();
            write_type_and_arg(out, 3, bytes.len() as u64);
            out.extend_from_slice(bytes);
        }
        CborValue::Array(items) => {
            write_type_and_arg(out, 4, items.len() as u64);
            for item in items {
                encode_value_into(item, out, depth + 1)?;
            }
        }
        CborValue::Map(entries) => {
            write_type_and_arg(out, 5, entries.len() as u64);
            let mut encoded_pairs = Vec::with_capacity(entries.len());
            for (k, v) in entries {
                let mut key_bytes = Vec::new();
                encode_value_into(k, &mut key_bytes, depth + 1)?;
                let mut val_bytes = Vec::new();
                encode_value_into(v, &mut val_bytes, depth + 1)?;
                encoded_pairs.push((key_bytes, val_bytes));
            }
            // RFC 8949 §4.2.1: bytewise lexicographic order of deterministic key encodings
            encoded_pairs.sort_by(|a, b| a.0.cmp(&b.0));
            for w in encoded_pairs.windows(2) {
                if w[0].0 == w[1].0 {
                    return Err(DetCborError::DuplicateMapKey);
                }
            }
            for (kb, vb) in encoded_pairs {
                out.extend_from_slice(&kb);
                out.extend_from_slice(&vb);
            }
        }
        CborValue::Bool(false) => out.push((7 << 5) | 20),
        CborValue::Bool(true) => out.push((7 << 5) | 21),
    }
    Ok(())
}

/// Encode a `CborValue` into RFC 8949 §4.2 Deterministic CBOR bytes.
pub fn encode_det_cbor(val: &CborValue) -> Result<Vec<u8>, DetCborError> {
    let mut out = Vec::new();
    encode_value_into(val, &mut out, 0)?;
    Ok(out)
}

fn read_exact<'a>(input: &'a [u8], cursor: &mut usize, n: usize) -> Result<&'a [u8], DetCborError> {
    let end = cursor.checked_add(n).ok_or(DetCborError::LengthOverflow)?;
    if end > input.len() {
        return Err(DetCborError::UnexpectedEof);
    }
    let slice = &input[*cursor..end];
    *cursor = end;
    Ok(slice)
}

/// Decode and strictly verify shortest-form CBOR argument integer (`ai` in `0..=31`).
fn read_canonical_argument(
    input: &[u8],
    cursor: &mut usize,
    ai: u8,
) -> Result<u64, DetCborError> {
    match ai {
        0..=23 => Ok(ai as u64),
        24 => {
            let b = read_exact(input, cursor, 1)?[0] as u64;
            if b < 24 {
                return Err(DetCborError::NonMinimalInteger {
                    additional_info: ai,
                    value: b,
                });
            }
            Ok(b)
        }
        25 => {
            let s = read_exact(input, cursor, 2)?;
            let v = u16::from_be_bytes([s[0], s[1]]) as u64;
            if v <= 0xFF {
                return Err(DetCborError::NonMinimalInteger {
                    additional_info: ai,
                    value: v,
                });
            }
            Ok(v)
        }
        26 => {
            let s = read_exact(input, cursor, 4)?;
            let v = u32::from_be_bytes([s[0], s[1], s[2], s[3]]) as u64;
            if v <= 0xFFFF {
                return Err(DetCborError::NonMinimalInteger {
                    additional_info: ai,
                    value: v,
                });
            }
            Ok(v)
        }
        27 => {
            let s = read_exact(input, cursor, 8)?;
            let v = u64::from_be_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
            if v <= 0xFFFF_FFFF {
                return Err(DetCborError::NonMinimalInteger {
                    additional_info: ai,
                    value: v,
                });
            }
            Ok(v)
        }
        28..=30 => Err(DetCborError::ReservedAdditionalInfo(ai)),
        31 => Err(DetCborError::IndefiniteLengthForbidden),
        _ => unreachable!(),
    }
}

fn decode_item(
    input: &[u8],
    cursor: &mut usize,
    depth: usize,
) -> Result<CborValue, DetCborError> {
    if depth > MAX_CBOR_DEPTH {
        return Err(DetCborError::MaxDepthExceeded);
    }
    let head = read_exact(input, cursor, 1)?[0];
    let major = head >> 5;
    let ai = head & 0x1F;

    match major {
        0 => {
            let u = read_canonical_argument(input, cursor, ai)?;
            Ok(CborValue::Unsigned(u))
        }
        1 => {
            let n = read_canonical_argument(input, cursor, ai)?;
            Ok(CborValue::NegInt(n))
        }
        2 => {
            let len_u64 = read_canonical_argument(input, cursor, ai)?;
            let len = usize::try_from(len_u64).map_err(|_| DetCborError::LengthOverflow)?;
            let bytes = read_exact(input, cursor, len)?;
            Ok(CborValue::Bytes(bytes.to_vec()))
        }
        3 => {
            let len_u64 = read_canonical_argument(input, cursor, ai)?;
            let len = usize::try_from(len_u64).map_err(|_| DetCborError::LengthOverflow)?;
            let bytes = read_exact(input, cursor, len)?;
            let text = core::str::from_utf8(bytes).map_err(|_| DetCborError::InvalidUtf8Text)?;
            Ok(CborValue::Text(String::from(text)))
        }
        4 => {
            let count_u64 = read_canonical_argument(input, cursor, ai)?;
            let count = usize::try_from(count_u64).map_err(|_| DetCborError::LengthOverflow)?;
            if count > input.len().saturating_sub(*cursor) {
                return Err(DetCborError::UnexpectedEof);
            }
            let mut arr = Vec::with_capacity(count);
            for _ in 0..count {
                arr.push(decode_item(input, cursor, depth + 1)?);
            }
            Ok(CborValue::Array(arr))
        }
        5 => {
            let count_u64 = read_canonical_argument(input, cursor, ai)?;
            let count = usize::try_from(count_u64).map_err(|_| DetCborError::LengthOverflow)?;
            if count.saturating_mul(2) > input.len().saturating_sub(*cursor) {
                return Err(DetCborError::UnexpectedEof);
            }
            let mut entries = Vec::with_capacity(count);
            let mut prev_key_slice: Option<&[u8]> = None;
            for _ in 0..count {
                let key_start = *cursor;
                let key_val = decode_item(input, cursor, depth + 1)?;
                let key_slice = &input[key_start..*cursor];
                if let Some(prev) = prev_key_slice {
                    match prev.cmp(key_slice) {
                        Ordering::Less => {}
                        Ordering::Equal => return Err(DetCborError::DuplicateMapKey),
                        Ordering::Greater => return Err(DetCborError::UnsortedMapKeys),
                    }
                }
                prev_key_slice = Some(key_slice);
                let val = decode_item(input, cursor, depth + 1)?;
                entries.push((key_val, val));
            }
            Ok(CborValue::Map(entries))
        }
        6 => Err(DetCborError::TagForbidden { tag_info: ai }),
        7 => match ai {
            20 => Ok(CborValue::Bool(false)),
            21 => Ok(CborValue::Bool(true)),
            25..=27 => Err(DetCborError::FloatForbidden { initial_byte: head }),
            31 => Err(DetCborError::IndefiniteLengthForbidden),
            other => Err(DetCborError::UnsupportedSimpleValue(other)),
        },
        _ => unreachable!(),
    }
}

/// Strictly decode RFC 8949 §4.2 Deterministic CBOR bytes, rejecting non-minimal integers,
/// indefinite lengths, IEEE-754 floats, unsorted/duplicate map keys, and trailing bytes.
pub fn decode_det_cbor(input: &[u8]) -> Result<CborValue, DetCborError> {
    let mut cursor = 0usize;
    let val = decode_item(input, &mut cursor, 0)?;
    if cursor != input.len() {
        return Err(DetCborError::TrailingBytes {
            remaining: input.len() - cursor,
        });
    }
    Ok(val)
}

fn map_lookup<'a>(
    entries: &'a [(CborValue, CborValue)],
    key: &'static str,
) -> Result<&'a CborValue, DetCborError> {
    for (k, v) in entries {
        if let CborValue::Text(s) = k
            && s == key
        {
            return Ok(v);
        }
    }
    Err(DetCborError::MissingField(key))
}

// ============================================================================
// 2-Bit Lexer + VPA Redaction Token Confinement Guard (`Lsafe` / Closing `F8`)
// ============================================================================

/// Verify that a redacted byte span `[offset, offset + len)` inside a structured JSON/HTTP/XML
/// payload is strictly confined to a single scalar token (`K9`, closing `F8` backslash `0x5c`,
/// `\r\n` header injection, `, : [ ] { } < >`, and unescaped `"` boundary smuggling!).
pub fn check_redaction_span_confinement(
    full_transcript: &[u8],
    offset: usize,
    len: usize,
) -> Result<(), &'static str> {
    let end = offset.checked_add(len).ok_or("span overflow")?;
    if end > full_transcript.len() || len == 0 {
        return Err("empty or out-of-bounds redaction span");
    }

    // Track 2-bit lexer state `(in_string, escaped)` up to `offset`
    let mut in_string = false;
    let mut escaped = false;
    let mut depth: i32 = 0;

    for &b in &full_transcript[..offset] {
        if in_string {
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            } else if b == b'"' {
                in_string = false;
            }
        } else {
            match b {
                b'"' => in_string = true,
                b'{' | b'[' => depth += 1,
                b'}' | b']' => {
                    depth -= 1;
                    if depth < 0 {
                        return Err("unbalanced structural delimiter before span");
                    }
                }
                _ => {}
            }
        }
    }

    if escaped {
        return Err("redaction span begins mid-escape sequence");
    }

    // Inside the redacted span: forbid ALL structural delimiters, quotes, backslashes (byte 92!),
    // CR/LF control bytes, and XML angle brackets!
    for &b in &full_transcript[offset..end] {
        if b < 0x20
            || matches!(
                b,
                b'\\' | b'"' | b'{' | b'}' | b'[' | b']' | b',' | b':' | b'<' | b'>'
            )
        {
            return Err("smuggled delimiter, escape backslash, quote, or control byte in redacted span");
        }
    }

    Ok(())
}

// ============================================================================
// `DualPcsReceipt`: End-to-End Dual-Track Crypto Receipt & `DetCbor` Codec
// ============================================================================

#[inline]
fn encode_ext2_cbor(z: GoldilocksExt2) -> CborValue {
    CborValue::Array(vec![
        CborValue::Unsigned(z.c0.to_canonical_u64()),
        CborValue::Unsigned(z.c1.to_canonical_u64()),
    ])
}

#[inline]
fn decode_ext2_cbor(v: &CborValue) -> Result<GoldilocksExt2, DetCborError> {
    let arr = v.as_array()?;
    if arr.len() != 2 {
        return Err(DetCborError::UnexpectedFieldCount {
            expected: 2,
            actual: arr.len(),
        });
    }
    let c0 = Goldilocks::from_canonical(arr[0].as_u64()?)?;
    let c1 = Goldilocks::from_canonical(arr[1].as_u64()?)?;
    Ok(GoldilocksExt2::new(c0, c1))
}

fn encode_ring_cbor(r: &RingElem) -> CborValue {
    CborValue::Array(r.coeffs().iter().map(|&c| CborValue::from_i64(c)).collect())
}

fn decode_ring_cbor(v: &CborValue) -> Result<RingElem, DetCborError> {
    let arr = v.as_array()?;
    if arr.len() != RING_DEGREE {
        return Err(DetCborError::UnexpectedFieldCount {
            expected: RING_DEGREE,
            actual: arr.len(),
        });
    }
    let mut coeffs = [0i64; RING_DEGREE];
    for (i, item) in arr.iter().enumerate() {
        let val = item.as_i64()?;
        if !(-HALF_Q_LAT..=HALF_Q_LAT).contains(&val) {
            return Err(DetCborError::NonCanonicalLatticeCoeff(val));
        }
        coeffs[i] = val;
    }
    Ok(RingElem::from_coeffs(coeffs))
}

/// Complete Dual-Track (`Canopy` Track H + `PikkuFold`/`Akita` Track L + `GoldilocksExt2` Sumcheck)
/// proof receipt serializable via strict RFC 8949 §4.2 Deterministic CBOR for Lean C-ABI & CLI workflows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualPcsReceipt {
    pub schema_version: u64,
    pub protocol_id: String,
    pub vk_digest: [u8; 32],
    pub circuit_desc: Vec<u8>,
    pub num_vars: u32,
    pub claimed_hypercube_sum: GoldilocksExt2,
    pub sumcheck_rounds: Vec<SumcheckRoundPolyExt2>,
    pub reduced_eval_point: Vec<GoldilocksExt2>,
    pub reduced_eval_val: GoldilocksExt2,
    pub canopy_commitment: CanopyCommitment,
    pub canopy_proof: CanopyBatchedProof,
    pub lattice_commitment: LatticeCommitment,
    pub lattice_proof: AkitaFoldProof,
    /// Canonical short opening of Track L. This transparent receipt discloses its table;
    /// Akita alone proves knowledge of a short vector, not a Goldilocks MLE evaluation.
    pub lattice_opening: Vec<RingElem>,
    pub final_transcript_digest: [u8; 32],
}

impl DualPcsReceipt {
    /// Convert to canonical `CborValue` AST.
    pub fn to_cbor_value(&self) -> CborValue {
        let sc_rounds = CborValue::Array(
            self.sumcheck_rounds
                .iter()
                .map(|p| CborValue::Array(p.coeffs.iter().copied().map(encode_ext2_cbor).collect()))
                .collect(),
        );
        let eval_pt = CborValue::Array(
            self.reduced_eval_point
                .iter()
                .copied()
                .map(encode_ext2_cbor)
                .collect(),
        );

        let canopy_comm = CborValue::Map(vec![
            (
                CborValue::Text(String::from("num_vars")),
                CborValue::Unsigned(self.canopy_commitment.num_vars as u64),
            ),
            (
                CborValue::Text(String::from("root")),
                CborValue::Bytes(self.canopy_commitment.root.to_vec()),
            ),
            (
                CborValue::Text(String::from("salted")),
                CborValue::Bool(self.canopy_commitment.salted),
            ),
        ]);

        let canopy_cols = CborValue::Array(
            self.canopy_proof
                .opened_columns
                .iter()
                .map(|col| {
                    let salt_val = match col.salt {
                        Some(s) => CborValue::Bytes(s.to_vec()),
                        None => CborValue::Bytes(Vec::new()),
                    };
                    CborValue::Map(vec![
                        (
                            CborValue::Text(String::from("col_idx")),
                            CborValue::Unsigned(col.col_idx as u64),
                        ),
                        (CborValue::Text(String::from("salt")), salt_val),
                        (
                            CborValue::Text(String::from("values")),
                            CborValue::Array(
                                col.values
                                    .iter()
                                    .map(|v| CborValue::Unsigned(v.to_canonical_u64()))
                                    .collect(),
                            ),
                        ),
                    ])
                })
                .collect(),
        );

        let canopy_prf = CborValue::Map(vec![
            (
                CborValue::Text(String::from("aux_siblings")),
                CborValue::Array(
                    self.canopy_proof
                        .aux_siblings
                        .iter()
                        .map(|s| CborValue::Bytes(s.to_vec()))
                        .collect(),
                ),
            ),
            (CborValue::Text(String::from("opened_columns")), canopy_cols),
            (
                CborValue::Text(String::from("u_eval")),
                CborValue::Array(
                    self.canopy_proof
                        .u_eval
                        .iter()
                        .copied()
                        .map(encode_ext2_cbor)
                        .collect(),
                ),
            ),
            (
                CborValue::Text(String::from("u_prox")),
                CborValue::Array(
                    self.canopy_proof
                        .u_prox
                        .iter()
                        .copied()
                        .map(encode_ext2_cbor)
                        .collect(),
                ),
            ),
        ]);

        let lat_comm = CborValue::Map(vec![
            (
                CborValue::Text(String::from("cols")),
                CborValue::Unsigned(self.lattice_commitment.cols as u64),
            ),
            (
                CborValue::Text(String::from("syndrome")),
                CborValue::Array(
                    self.lattice_commitment
                        .syndrome
                        .iter()
                        .map(encode_ring_cbor)
                        .collect(),
                ),
            ),
        ]);

        let akita_rounds = CborValue::Array(
            self.lattice_proof
                .rounds
                .iter()
                .map(|r| {
                    CborValue::Map(vec![
                        (CborValue::Text(String::from("k_ll")), encode_ring_cbor(&r.k_ll)),
                        (CborValue::Text(String::from("k_mid")), encode_ring_cbor(&r.k_mid)),
                        (CborValue::Text(String::from("k_rr")), encode_ring_cbor(&r.k_rr)),
                        (
                            CborValue::Text(String::from("t_ll")),
                            CborValue::Array(r.t_ll.iter().map(encode_ring_cbor).collect()),
                        ),
                        (
                            CborValue::Text(String::from("t_mid")),
                            CborValue::Array(r.t_mid.iter().map(encode_ring_cbor).collect()),
                        ),
                        (
                            CborValue::Text(String::from("t_rr")),
                            CborValue::Array(r.t_rr.iter().map(encode_ring_cbor).collect()),
                        ),
                    ])
                })
                .collect(),
        );

        let lat_prf = CborValue::Map(vec![
            (
                CborValue::Text(String::from("final_witness")),
                encode_ring_cbor(&self.lattice_proof.final_witness),
            ),
            (
                CborValue::Text(String::from("initial_norm_bound")),
                CborValue::Unsigned(self.lattice_proof.initial_norm_bound),
            ),
            (
                CborValue::Text(String::from("kronecker_projection")),
                encode_ring_cbor(&self.lattice_proof.kronecker_projection),
            ),
            (
                CborValue::Text(String::from("opened_witness")),
                CborValue::Array(self.lattice_opening.iter().map(encode_ring_cbor).collect()),
            ),
            (CborValue::Text(String::from("rounds")), akita_rounds),
        ]);

        CborValue::Map(vec![
            (CborValue::Text(String::from("canopy_commitment")), canopy_comm),
            (CborValue::Text(String::from("canopy_proof")), canopy_prf),
            (
                CborValue::Text(String::from("circuit_desc")),
                CborValue::Bytes(self.circuit_desc.clone()),
            ),
            (
                CborValue::Text(String::from("claimed_hypercube_sum")),
                encode_ext2_cbor(self.claimed_hypercube_sum),
            ),
            (
                CborValue::Text(String::from("final_transcript_digest")),
                CborValue::Bytes(self.final_transcript_digest.to_vec()),
            ),
            (CborValue::Text(String::from("lattice_commitment")), lat_comm),
            (CborValue::Text(String::from("lattice_proof")), lat_prf),
            (
                CborValue::Text(String::from("num_vars")),
                CborValue::Unsigned(self.num_vars as u64),
            ),
            (
                CborValue::Text(String::from("protocol_id")),
                CborValue::Text(self.protocol_id.clone()),
            ),
            (CborValue::Text(String::from("reduced_eval_point")), eval_pt),
            (
                CborValue::Text(String::from("reduced_eval_val")),
                encode_ext2_cbor(self.reduced_eval_val),
            ),
            (
                CborValue::Text(String::from("schema_version")),
                CborValue::Unsigned(self.schema_version),
            ),
            (CborValue::Text(String::from("sumcheck_rounds")), sc_rounds),
            (
                CborValue::Text(String::from("vk_digest")),
                CborValue::Bytes(self.vk_digest.to_vec()),
            ),
        ])
    }

    /// Serialize `DualPcsReceipt` to RFC 8949 §4.2 Deterministic CBOR bytes.
    pub fn to_det_cbor_bytes(&self) -> Result<Vec<u8>, DetCborError> {
        encode_det_cbor(&self.to_cbor_value())
    }

    /// Strictly decode a `DualPcsReceipt` from RFC 8949 §4.2 Deterministic CBOR bytes,
    /// enforcing exact field counts (rejecting unknown smuggled map keys!) and `CanonicalLift` `< p`.
    pub fn from_det_cbor_bytes(bytes: &[u8]) -> Result<Self, DetCborError> {
        let root_val = decode_det_cbor(bytes)?;
        let root = root_val.as_map()?;
        if root.len() != 14 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 14,
                actual: root.len(),
            });
        }

        let schema_version = map_lookup(root, "schema_version")?.as_u64()?;
        if schema_version != DUAL_PCS_RECEIPT_SCHEMA_VERSION {
            return Err(DetCborError::SchemaMismatch(String::from(
                "unsupported schema_version",
            )));
        }
        let protocol_id = String::from(map_lookup(root, "protocol_id")?.as_text()?);
        let vk_digest = map_lookup(root, "vk_digest")?.as_fixed_bytes::<32>()?;
        let circuit_desc = map_lookup(root, "circuit_desc")?.as_bytes()?.to_vec();
        let num_vars = u32::try_from(map_lookup(root, "num_vars")?.as_u64()?)
            .map_err(|_| DetCborError::LengthOverflow)?;
        let claimed_hypercube_sum = decode_ext2_cbor(map_lookup(root, "claimed_hypercube_sum")?)?;

        let sc_arr = map_lookup(root, "sumcheck_rounds")?.as_array()?;
        let mut sumcheck_rounds = Vec::with_capacity(sc_arr.len());
        for poly_v in sc_arr {
            let coeff_arr = poly_v.as_array()?;
            let mut coeffs = Vec::with_capacity(coeff_arr.len());
            for c_v in coeff_arr {
                coeffs.push(decode_ext2_cbor(c_v)?);
            }
            sumcheck_rounds.push(SumcheckRoundPolyExt2 { coeffs });
        }

        let pt_arr = map_lookup(root, "reduced_eval_point")?.as_array()?;
        let mut reduced_eval_point = Vec::with_capacity(pt_arr.len());
        for z_v in pt_arr {
            reduced_eval_point.push(decode_ext2_cbor(z_v)?);
        }
        let reduced_eval_val = decode_ext2_cbor(map_lookup(root, "reduced_eval_val")?)?;
        let final_transcript_digest =
            map_lookup(root, "final_transcript_digest")?.as_fixed_bytes::<32>()?;

        // Decode CanopyCommitment
        let cc_map = map_lookup(root, "canopy_commitment")?.as_map()?;
        if cc_map.len() != 3 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 3,
                actual: cc_map.len(),
            });
        }
        let canopy_commitment = CanopyCommitment {
            num_vars: u32::try_from(map_lookup(cc_map, "num_vars")?.as_u64()?)
                .map_err(|_| DetCborError::LengthOverflow)?,
            salted: map_lookup(cc_map, "salted")?.as_bool()?,
            root: map_lookup(cc_map, "root")?.as_fixed_bytes::<32>()?,
        };

        // Decode CanopyBatchedProof
        let cp_map = map_lookup(root, "canopy_proof")?.as_map()?;
        if cp_map.len() != 4 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 4,
                actual: cp_map.len(),
            });
        }
        let u_eval: Vec<GoldilocksExt2> = map_lookup(cp_map, "u_eval")?
            .as_array()?
            .iter()
            .map(decode_ext2_cbor)
            .collect::<Result<_, _>>()?;
        let u_prox: Vec<GoldilocksExt2> = map_lookup(cp_map, "u_prox")?
            .as_array()?
            .iter()
            .map(decode_ext2_cbor)
            .collect::<Result<_, _>>()?;
        let aux_siblings: Vec<[u8; 32]> = map_lookup(cp_map, "aux_siblings")?
            .as_array()?
            .iter()
            .map(CborValue::as_fixed_bytes::<32>)
            .collect::<Result<_, _>>()?;

        let cols_arr = map_lookup(cp_map, "opened_columns")?.as_array()?;
        let mut opened_columns = Vec::with_capacity(cols_arr.len());
        for col_v in cols_arr {
            let cm = col_v.as_map()?;
            if cm.len() != 3 {
                return Err(DetCborError::UnexpectedFieldCount {
                    expected: 3,
                    actual: cm.len(),
                });
            }
            let col_idx = usize::try_from(map_lookup(cm, "col_idx")?.as_u64()?)
                .map_err(|_| DetCborError::LengthOverflow)?;
            let salt_bytes = map_lookup(cm, "salt")?.as_bytes()?;
            let salt = match salt_bytes.len() {
                0 => None,
                32 => {
                    let mut arr = [0u8; 32];
                    arr.copy_from_slice(salt_bytes);
                    Some(arr)
                }
                _ => {
                    return Err(DetCborError::SchemaMismatch(String::from(
                        "column salt must be 0 bytes (unsalted) or 32 bytes (salted)",
                    )));
                }
            };
            let values: Vec<Goldilocks> = map_lookup(cm, "values")?
                .as_array()?
                .iter()
                .map(|x| Ok(Goldilocks::from_canonical(x.as_u64()?)?))
                .collect::<Result<_, DetCborError>>()?;
            opened_columns.push(CanopyOpenedColumn {
                col_idx,
                values,
                salt,
            });
        }
        let canopy_proof = CanopyBatchedProof {
            u_eval,
            u_prox,
            opened_columns,
            aux_siblings,
        };

        // Decode LatticeCommitment
        let lc_map = map_lookup(root, "lattice_commitment")?.as_map()?;
        if lc_map.len() != 2 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 2,
                actual: lc_map.len(),
            });
        }
        let lattice_commitment = LatticeCommitment {
            cols: u32::try_from(map_lookup(lc_map, "cols")?.as_u64()?)
                .map_err(|_| DetCborError::LengthOverflow)?,
            syndrome: map_lookup(lc_map, "syndrome")?
                .as_array()?
                .iter()
                .map(decode_ring_cbor)
                .collect::<Result<_, _>>()?,
        };

        // Decode AkitaFoldProof
        let lp_map = map_lookup(root, "lattice_proof")?.as_map()?;
        if lp_map.len() != 5 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 5,
                actual: lp_map.len(),
            });
        }
        let initial_norm_bound = map_lookup(lp_map, "initial_norm_bound")?.as_u64()?;
        let kronecker_projection = decode_ring_cbor(map_lookup(lp_map, "kronecker_projection")?)?;
        let final_witness = decode_ring_cbor(map_lookup(lp_map, "final_witness")?)?;
        let lattice_opening = map_lookup(lp_map, "opened_witness")?
            .as_array()?
            .iter()
            .map(decode_ring_cbor)
            .collect::<Result<Vec<_>, _>>()?;
        let rounds_arr = map_lookup(lp_map, "rounds")?.as_array()?;
        let mut rounds = Vec::with_capacity(rounds_arr.len());
        for rv in rounds_arr {
            let rm = rv.as_map()?;
            if rm.len() != 6 {
                return Err(DetCborError::UnexpectedFieldCount {
                    expected: 6,
                    actual: rm.len(),
                });
            }
            let decode_vec_ring = |field: &'static str| -> Result<Vec<RingElem>, DetCborError> {
                map_lookup(rm, field)?
                    .as_array()?
                    .iter()
                    .map(decode_ring_cbor)
                    .collect()
            };
            rounds.push(AkitaFoldRound {
                t_ll: decode_vec_ring("t_ll")?,
                t_mid: decode_vec_ring("t_mid")?,
                t_rr: decode_vec_ring("t_rr")?,
                k_ll: decode_ring_cbor(map_lookup(rm, "k_ll")?)?,
                k_mid: decode_ring_cbor(map_lookup(rm, "k_mid")?)?,
                k_rr: decode_ring_cbor(map_lookup(rm, "k_rr")?)?,
            });
        }
        let lattice_proof = AkitaFoldProof {
            initial_norm_bound,
            kronecker_projection,
            rounds,
            final_witness,
        };

        Ok(Self {
            schema_version,
            protocol_id,
            vk_digest,
            circuit_desc,
            num_vars,
            claimed_hypercube_sum,
            sumcheck_rounds,
            reduced_eval_point,
            reduced_eval_val,
            canopy_commitment,
            canopy_proof,
            lattice_commitment,
            lattice_proof,
            lattice_opening,
            final_transcript_digest,
        })
    }
}

fn encode_dual_comm_bytes(canopy: &CanopyCommitment, lat: &LatticeCommitment) -> Vec<u8> {
    let c = canopy.to_transcript_bytes();
    let l = lat.to_transcript_bytes();
    let mut out = leb128(c.len());
    out.extend_from_slice(&c);
    out.extend_from_slice(&leb128(l.len()));
    out.extend_from_slice(&l);
    out
}

/// Prove an end-to-end Dual-Track (`Canopy` + `PikkuFold`/`Akita` + `GoldilocksExt2` Sumcheck)
/// receipt bound through the full `Unbound -> RelationBound -> InstanceBound` `FenziTranscript`!
pub fn prove_dual_pcs_receipt(
    protocol_id: &str,
    vk_digest: [u8; 32],
    circuit_desc: &[u8],
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    num_vars: usize,
    table: &[Goldilocks],
) -> Result<DualPcsReceipt, DetCborError> {
    let canopy_state = canopy_commit(canopy_params, num_vars, table, None)?;
    let ring_witness = pack_goldilocks_to_ring_witness(table, lattice_params.cols)?;
    let lattice_commitment = commit_ring_witness(lattice_params, &ring_witness)?;

    let mut sum_base = Goldilocks::ZERO;
    for &x in table {
        sum_base += x;
    }
    let claimed_hypercube_sum = GoldilocksExt2::from_base(sum_base);
    let dual_comm_bytes =
        encode_dual_comm_bytes(&canopy_state.commitment, &lattice_commitment);

    // Phase 1 -> Phase 2 -> Phase 3 (`Unbound -> RelationBound -> InstanceBound`)
    let mut tr = FenziTranscript::new(b"OBEND.DUAL_PCS.SEED/v1")
        .bind_relation(protocol_id, &vk_digest, circuit_desc)
        .bind_instance(&dual_comm_bytes, claimed_hypercube_sum, &[]);

    let (sumcheck_rounds, eval_claim) = prove_multilinear_sumcheck_ext2(table, &mut tr)?;
    debug_assert_eq!(
        mle_eval_base_at_ext2(table, &eval_claim.point)?,
        eval_claim.expected_val
    );

    // Fork into Track H (`Canopy`) & Track L (`PikkuFold`/`Akita`), absorbing reduced point explicitly
    let mut pt_bytes = leb128(eval_claim.point.len());
    for z in &eval_claim.point {
        pt_bytes.extend_from_slice(&z.to_be_bytes());
    }
    tr.absorb(b"DUAL.PCS.EVAL_POINT", &pt_bytes);
    tr.absorb_ext2(b"DUAL.PCS.EVAL_VAL", eval_claim.expected_val);

    let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
    let mut tr_l = tr.fork(DUAL_TRACK2_LABEL);

    let canopy_proof = canopy_open(canopy_params, &canopy_state, &eval_claim.point, &mut tr_h)?;
    let lattice_proof =
        akita_prove_open(lattice_params, &ring_witness, GADGET_LIMB_MAX, &mut tr_l)?;

    tr.join(&tr_h, &tr_l);

    Ok(DualPcsReceipt {
        schema_version: DUAL_PCS_RECEIPT_SCHEMA_VERSION,
        protocol_id: String::from(protocol_id),
        vk_digest,
        circuit_desc: circuit_desc.to_vec(),
        num_vars: num_vars as u32,
        claimed_hypercube_sum,
        sumcheck_rounds,
        reduced_eval_point: eval_claim.point,
        reduced_eval_val: eval_claim.expected_val,
        canopy_commitment: canopy_state.commitment,
        canopy_proof,
        lattice_commitment,
        lattice_proof,
        lattice_opening: ring_witness,
        final_transcript_digest: *tr.state(),
    })
}

/// Verify a `DualPcsReceipt` end-to-end across BOTH Track H (`Canopy`) and Track L (`Akita`),
/// returning the `Canopy` `HashInvocationStats` telemetry on acceptance.
pub fn verify_dual_pcs_receipt(
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    receipt: &DualPcsReceipt,
) -> Result<HashInvocationStats, DetCborError> {
    if receipt.num_vars > 24 {
        return Err(DetCborError::SchemaMismatch(String::from("num_vars exceeds 24")));
    }
    if receipt.schema_version != DUAL_PCS_RECEIPT_SCHEMA_VERSION {
        return Err(DetCborError::SchemaMismatch(String::from("bad schema_version")));
    }
    if receipt.canopy_commitment.num_vars != receipt.num_vars {
        return Err(DetCborError::SchemaMismatch(String::from("num_vars mismatch")));
    }
    let dual_comm_bytes =
        encode_dual_comm_bytes(&receipt.canopy_commitment, &receipt.lattice_commitment);

    let mut tr = FenziTranscript::new(b"OBEND.DUAL_PCS.SEED/v1")
        .bind_relation(&receipt.protocol_id, &receipt.vk_digest, &receipt.circuit_desc)
        .bind_instance(&dual_comm_bytes, receipt.claimed_hypercube_sum, &[]);

    let sc_claim = verify_sumcheck_ext2(
        1,
        receipt.num_vars as usize,
        receipt.claimed_hypercube_sum,
        &receipt.sumcheck_rounds,
        &mut tr,
    )?;
    if sc_claim.point != receipt.reduced_eval_point
        || sc_claim.expected_val != receipt.reduced_eval_val
    {
        return Err(DetCborError::ReducedClaimMismatch);
    }

    let mut pt_bytes = leb128(sc_claim.point.len());
    for z in &sc_claim.point {
        pt_bytes.extend_from_slice(&z.to_be_bytes());
    }
    tr.absorb(b"DUAL.PCS.EVAL_POINT", &pt_bytes);
    tr.absorb_ext2(b"DUAL.PCS.EVAL_VAL", sc_claim.expected_val);

    let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
    let mut tr_l = tr.fork(DUAL_TRACK2_LABEL);

    let hash_stats = canopy_verify(
        canopy_params,
        &receipt.canopy_commitment,
        &sc_claim.point,
        sc_claim.expected_val,
        &receipt.canopy_proof,
        &mut tr_h,
    )?;
    // Check the SAME evaluation as Track H, with canonical 16-bit limbs and zero padding.
    // A short unrelated vector (including zero) must not satisfy this gate.
    let opened_table = unpack_ring_witness_to_goldilocks(
        &receipt.lattice_opening, 1usize << receipt.num_vars)?;
    if commit_ring_witness(lattice_params, &receipt.lattice_opening)? != receipt.lattice_commitment
        || mle_eval_base_at_ext2(&opened_table, &sc_claim.point)? != sc_claim.expected_val
    {
        return Err(DetCborError::ReducedClaimMismatch);
    }
    akita_verify_open(
        lattice_params,
        &receipt.lattice_commitment,
        GADGET_LIMB_MAX,
        &receipt.lattice_proof,
        &mut tr_l,
    )?;

    tr.join(&tr_h, &tr_l);
    if tr.state() != &receipt.final_transcript_digest {
        return Err(DetCborError::FinalTranscriptDigestMismatch);
    }

    Ok(hash_stats)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Adversarial prover recomputes BOTH transcripts and valid openings after selecting
    // an unrelated lattice vector. This is stronger than corrupting a commitment in transit.
    fn prove_split_tracks(protocol_id: &str, vk_digest: [u8; 32], circuit_desc: &[u8],
        canopy_params: &CanopyParams, lattice_params: &LatticeParams,
        num_vars: usize, table: &[Goldilocks]) -> Result<DualPcsReceipt, DetCborError> {
    let canopy_state = canopy_commit(canopy_params, num_vars, table, None)?;
    let ring_witness = vec![RingElem::zero(); lattice_params.cols];
    let lattice_commitment = commit_ring_witness(lattice_params, &ring_witness)?;

    let mut sum_base = Goldilocks::ZERO;
    for &x in table {
        sum_base += x;
    }
    let claimed_hypercube_sum = GoldilocksExt2::from_base(sum_base);
    let dual_comm_bytes =
        encode_dual_comm_bytes(&canopy_state.commitment, &lattice_commitment);

    // Phase 1 -> Phase 2 -> Phase 3 (`Unbound -> RelationBound -> InstanceBound`)
    let mut tr = FenziTranscript::new(b"OBEND.DUAL_PCS.SEED/v1")
        .bind_relation(protocol_id, &vk_digest, circuit_desc)
        .bind_instance(&dual_comm_bytes, claimed_hypercube_sum, &[]);

    let (sumcheck_rounds, eval_claim) = prove_multilinear_sumcheck_ext2(table, &mut tr)?;
    debug_assert_eq!(
        mle_eval_base_at_ext2(table, &eval_claim.point)?,
        eval_claim.expected_val
    );

    // Fork into Track H (`Canopy`) & Track L (`PikkuFold`/`Akita`), absorbing reduced point explicitly
    let mut pt_bytes = leb128(eval_claim.point.len());
    for z in &eval_claim.point {
        pt_bytes.extend_from_slice(&z.to_be_bytes());
    }
    tr.absorb(b"DUAL.PCS.EVAL_POINT", &pt_bytes);
    tr.absorb_ext2(b"DUAL.PCS.EVAL_VAL", eval_claim.expected_val);

    let mut tr_h = tr.fork(DUAL_TRACK1_LABEL);
    let mut tr_l = tr.fork(DUAL_TRACK2_LABEL);

    let canopy_proof = canopy_open(canopy_params, &canopy_state, &eval_claim.point, &mut tr_h)?;
    let lattice_proof =
        akita_prove_open(lattice_params, &ring_witness, GADGET_LIMB_MAX, &mut tr_l)?;

    tr.join(&tr_h, &tr_l);

    Ok(DualPcsReceipt {
        schema_version: DUAL_PCS_RECEIPT_SCHEMA_VERSION,
        protocol_id: String::from(protocol_id),
        vk_digest,
        circuit_desc: circuit_desc.to_vec(),
        num_vars: num_vars as u32,
        claimed_hypercube_sum,
        sumcheck_rounds,
        reduced_eval_point: eval_claim.point,
        reduced_eval_val: eval_claim.expected_val,
        canopy_commitment: canopy_state.commitment,
        canopy_proof,
        lattice_commitment,
        lattice_proof,
        lattice_opening: ring_witness,
        final_transcript_digest: *tr.state(),
    })
    }

    #[test]
    fn test_unrelated_short_lattice_opening_refused_at_same_evaluation() {
        let cp = CanopyParams::default_128bit();
        let lp = LatticeParams::expand_from_seed([0x55; 32], 2, 4).unwrap();
        let table = vec![Goldilocks::ONE; 16];
        let forged = prove_split_tracks("OBEND.SPLIT_TEST/v1", [1; 32], b"split", &cp, &lp, 4, &table).unwrap();
        assert_eq!(verify_dual_pcs_receipt(&cp, &lp, &forged), Err(DetCborError::ReducedClaimMismatch));
    }

    #[test]
    fn test_rfc8949_det_cbor_strict_canonicality_and_rejections() {
        // Canonical map sorting: RFC 8949 §4.2.1 sorts by bytewise lexicographic order of encoded keys!
        // "b" (0x61 0x62) < "aa" (0x62 0x61 0x61) because 0x61 < 0x62!
        let unsorted = CborValue::Map(vec![
            (CborValue::Text(String::from("aa")), CborValue::Unsigned(1)),
            (CborValue::Text(String::from("b")), CborValue::Unsigned(2)),
            (CborValue::from_i64(-1), CborValue::Bool(true)),
            (CborValue::Unsigned(0), CborValue::Bytes(vec![])),
        ]);
        let bytes = encode_det_cbor(&unsorted).unwrap();
        let decoded = decode_det_cbor(&bytes).unwrap();
        let reencoded = encode_det_cbor(&decoded).unwrap();
        assert_eq!(bytes, reencoded, "re-encoding must be byte-for-byte identical");

        // Reject CBOR Null (0xf6 = major 7, ai 22) to match Lean `Obend.Codec.DetCbor`
        assert_eq!(
            decode_det_cbor(&[0xf6]),
            Err(DetCborError::UnsupportedSimpleValue(22))
        );

        // Reject non-minimal integer: 5 encoded as [0x18, 0x05] instead of [0x05]
        assert!(matches!(
            decode_det_cbor(&[0x18, 0x05]),
            Err(DetCborError::NonMinimalInteger {
                additional_info: 24,
                value: 5
            })
        ));
        // Reject non-minimal 2-byte integer: 255 encoded as [0x19, 0x00, 0xFF]
        assert!(matches!(
            decode_det_cbor(&[0x19, 0x00, 0xFF]),
            Err(DetCborError::NonMinimalInteger {
                additional_info: 25,
                value: 255
            })
        ));

        // Reject unsorted map keys: { "aa": 1, "b": 2 } raw => a2 62 61 61 01 61 62 02
        let raw_unsorted_map = [0xa2, 0x62, b'a', b'a', 0x01, 0x61, b'b', 0x02];
        assert_eq!(
            decode_det_cbor(&raw_unsorted_map),
            Err(DetCborError::UnsortedMapKeys)
        );

        // Reject duplicate map keys: { "a": 1, "a": 2 } => a2 61 61 01 61 61 02
        let raw_dup_map = [0xa2, 0x61, b'a', 0x01, 0x61, b'a', 0x02];
        assert_eq!(decode_det_cbor(&raw_dup_map), Err(DetCborError::DuplicateMapKey));

        // Reject IEEE-754 floats (half 0xf9, single 0xfa, double 0xfb)
        assert!(matches!(
            decode_det_cbor(&[0xf9, 0x3c, 0x00]),
            Err(DetCborError::FloatForbidden { initial_byte: 0xf9 })
        ));
        assert!(matches!(
            decode_det_cbor(&[0xfa, 0x3f, 0x80, 0x00, 0x00]),
            Err(DetCborError::FloatForbidden { initial_byte: 0xfa })
        ));
        assert!(matches!(
            decode_det_cbor(&[0xfb, 0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
            Err(DetCborError::FloatForbidden { initial_byte: 0xfb })
        ));

        // Reject indefinite-length array (0x9f ... 0xff)
        assert_eq!(
            decode_det_cbor(&[0x9f, 0x01, 0xff]),
            Err(DetCborError::IndefiniteLengthForbidden)
        );

        // Reject trailing bytes
        assert_eq!(
            decode_det_cbor(&[0x01, 0x00]),
            Err(DetCborError::TrailingBytes { remaining: 1 })
        );
    }

    #[test]
    fn test_dual_pcs_receipt_det_cbor_roundtrip_and_verification() {
        let canopy_params = CanopyParams::new(
            crate::canopy::DomainKind::PrimeField,
            crate::canopy::ProximityRegime::UniqueDecodingRadius,
            4,
            256,
        )
        .unwrap();
        let lattice_params = LatticeParams::expand_from_seed([0x55u8; 32], 3, 8).unwrap();
        let num_vars = 6usize; // 64 Goldilocks elements = 256 limbs = 4 RingElems (padded to 8)
        let table: Vec<Goldilocks> = (0..(1usize << num_vars))
            .map(|i| Goldilocks::from_u64_reduced((i as u64) * 97 + 11))
            .collect();

        let receipt = prove_dual_pcs_receipt(
            "OBEND.DUAL_PCS.STRANGER_WORKFLOW/v1",
            [0x99u8; 32],
            b"symbolic-zkvm-r1cs-desc",
            &canopy_params,
            &lattice_params,
            num_vars,
            &table,
        )
        .unwrap();

        let wire_bytes = receipt.to_det_cbor_bytes().unwrap();
        let decoded = DualPcsReceipt::from_det_cbor_bytes(&wire_bytes).unwrap();
        assert_eq!(decoded, receipt);
        assert_eq!(decoded.to_det_cbor_bytes().unwrap(), wire_bytes);

        verify_dual_pcs_receipt(&canopy_params, &lattice_params, &decoded).unwrap();
    }
}
