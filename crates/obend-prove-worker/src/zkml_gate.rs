#![forbid(unsafe_code)]
//! Honest `UD-100` (`UDR` / `JBR` vs. withdrawn `CBR-130`) zkML suite parameter floor gate and
//! base-field `Goldilocks` native `MXFP4` (`E2M1` + `2^sh`) `EinSumcheck` + BCS-Merkle Chunk PIOP.
//!
//! Aligned byte-for-byte with `Obend.SymbolicZk.EinSumcheckMxfp4`, `Obend.SymbolicZk.ProvenZkmlGate`,
//! `Obend.Crypto.Transcript`, `Obend.Crypto.Sumcheck`, and `Obend.Crypto.PCS`
//! (`#![forbid(unsafe_code)]`, zero external crate dependencies):
//! 1. **Honest `UD-100` Suite Parameter Accounting (`ZkmlSuiteProfile::check_proven_floor`)**:
//!    prices Reed–Solomon / BaseFold / WHIR / `zkml-ir-v2` suite parameter profiles (`log_arity >= 1`,
//!    `num_queries >= 1` with explicit `pinned_num_queries` equality, extension-field LogUp ceiling,
//!    and BCS digest ceiling) at `>= 100_000` milli-bits across `(lb=6, q=86, pow=16)` (`100.022`b)
//!    and wide-leaf `(lb=2, q=148, pow=0, log_arity=4)` (`100.344`b), refusing withdrawn `CBR-130`.
//! 2. **Executable Base-Field `Goldilocks` Native 3-Operand `MXFP4` `EinSumcheck` Chunk PIOP**:
//!    verifies `D[i,j] = Σ_{k,b} X[i,b,k] · Q[b,k,j] · S[k,j]` over base-field `Goldilocks`
//!    (`p = 2^64 - 2^32 + 1`) with signed `E2M1` mantissas `{0, ±1, ±2, ±3, ±4, ±6, ±8, ±12}`,
//!    power-of-two block scales `2^{sh}` (`sh <= 30`), exact sumcheck round degrees
//!    `(2^logB, 3^logK, 3^logJ)` under `b -> k -> j` (never degree 4: Lean's
//!    `verifyMxfp4ChunkIop_sound` proves a constructive failure-event disjunction with `0`
//!    probability axioms; under uniform squeeze bytes, uniform field challenges bound the algebraic
//!    root-hit events by `(logI + logJ + 2·logB + 3·logK + 3·logJ) / p`, while 128-bit modular
//!    squeezing shifts per-point mass to `<= ceil(2^128 / p) / 2^128`), rate-1 binary
//!    `cSHAKE256` Merkle butterfly fold-walk openings (not RS codewords; static weight-domain
//!    validity is enforced at manifest/witness construction), and `windowed_find_map_first` minimal
//!    PoW witness `w` (`w - 1` provably invalid).

use std::fmt;
use std::sync::Arc;

use crate::grinder::{
    default_grind_window, sha256, windowed_find_map_first_cancellable, MAX_DEFAULT_GRIND_THREADS,
};
use crate::service::{CancelToken, CancellableBackend, ProveService, ProveServiceConfig};
pub use obend_primitives::goldilocks::{Goldilocks, GOLDILOCKS_PRIME};

// ---------------------------------------------------------------------------
// Constants & Domain Tags
// ---------------------------------------------------------------------------

/// Canonical SP 800-185 `cSHAKE256` customization tag for zkML streaming chunk commitments.
pub const ZKML_CHUNK_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_CHUNK/v1";
/// Canonical `cSHAKE256` customization tag for outer `CandidateComputation` artifact-to-chain bindings.
pub const ZKML_CANDIDATE_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_CANDIDATE/v1";
/// Canonical `cSHAKE256` customization tag for zkML binary Merkle trees.
pub const ZKML_MERKLE_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_MERKLE/v1";
/// Canonical `cSHAKE256` customization tag for static `MXFP4` model weight manifests.
pub const ZKML_WEIGHTS_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_WEIGHTS/v1";
/// Canonical `cSHAKE256` customization tag for `ZkmlSuiteProfile` parameter digests.
pub const ZKML_SUITE_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_SUITE/v1";
/// Canonical Fenzi Fiat–Shamir protocol ID for the Goldilocks `MXFP4` `EinSumcheck` Chunk PIOP.
pub const ZKML_IOP_PROTOCOL_ID: &[u8] = b"OBEND.SHE.ZKML_IOP/v1";

const FS_SEED_TAG: &[u8] = b"OBEND.CRYPTO.FS.SEED/v1";
const FS_BIND_TAG: &[u8] = b"OBEND.CRYPTO.FS.BIND/v1";
const FS_INSTANCE_TAG: &[u8] = b"OBEND.CRYPTO.FS.INSTANCE/v1";
const FS_ABSORB_TAG: &[u8] = b"OBEND.CRYPTO.FS.ABSORB/v1";
const FS_SQUEEZE_TAG: &[u8] = b"OBEND.CRYPTO.FS.SQUEEZE/v1";
const FS_RATCHET_TAG: &[u8] = b"OBEND.CRYPTO.FS.RATCHET/v1";

const SUMCHECK_ROUND_LABEL: &[u8] = b"SUMCHECK.ROUND";
const ZKML_D_CLAIM_LABEL: &[u8] = b"ZKML.D.CLAIM";
const ZKML_FOLD_ROOTS_LABEL: &[u8] = b"ZKML.FOLD.ROOTS";
const ZKML_POW_NONCE_LABEL: &[u8] = b"ZKML.POW.NONCE";

/// Minimum required unconditional soundness floor in milli-bits (`100_000` = `100.000` bits).
pub const PROVEN_MIN_MILLI_BITS: u64 = 100_000;
/// Milli-bits per whole bit.
pub const MILLI_BITS_PER_BIT: u64 = 1_000;

/// Canonical Goldilocks prime modulus (`2^64 - 2^32 + 1 = 0xFFFF_FFFF_0000_0001`).
pub const GOLDILOCKS_MODULUS: u64 = GOLDILOCKS_PRIME;
/// Bit-width of the Goldilocks prime (`ceil(log2(p)) = 64`).
pub const GOLDILOCKS_MODULUS_BITS: u32 = 64;

/// BabyBear prime modulus (`15 * 2^27 + 1 = 2_013_265_921`).
pub const BABYBEAR_MODULUS: u64 = 2_013_265_921;
/// Bit-width of the BabyBear prime (`ceil(log2(p)) = 31`).
pub const BABYBEAR_MODULUS_BITS: u32 = 31;

/// KoalaBear prime modulus (`127 * 2^24 + 1 = 2_130_706_433`).
pub const KOALABEAR_MODULUS: u64 = 2_130_706_433;
/// Bit-width of the KoalaBear prime (`ceil(log2(p)) = 31`).
pub const KOALABEAR_MODULUS_BITS: u32 = 31;

/// Default maximum nonce span searched by [`StreamingZkmlBackend`] when `grind_span == 0`.
pub const DEFAULT_ZKML_GRIND_SPAN: u64 = 1u64 << 28;

/// Minimum serialized byte floor of one [`ZkmlChunkReceipt`] record (7 × 32B digests + 2 × 8B indices + framing).
pub const SERIALIZED_CHUNK_RECEIPT_BYTES: usize = 272;

/// Canonical 15-element signed `E2M1` (`MXFP4`, `2x`-scaled integer) mantissa domain.
pub const E2M1_MANTISSA_DOMAIN: [i64; 15] = [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12];

/// Maximum supported `MXFP4` power-of-two block scale shift (`2^30 < p_GL`).
pub const MAX_MXFP4_SCALE_SHIFT: u32 = 30;
/// Hard per-tensor hypercube variable bound (`< 20`, capping each table at `<= 2^19 = 524,288` felts).
pub const MAX_ZKML_HYPERCUBE_VARS: usize = 20;
/// Hard per-chunk query count cap preventing unbounded challenge/opening DoS.
pub const MAX_ZKML_NUM_QUERIES: usize = 1_024;
/// Hard sumcheck round count cap (`log_b + log_k + log_j < 60`).
pub const MAX_ZKML_SUMCHECK_ROUNDS: usize = 60;
/// Hard multi-layer manifest cap.
pub const MAX_ZKML_MODEL_LAYERS: usize = 1_024;

const UDR_QUERY_MILLI_BITS_TABLE: [u64; 12] =
    [0, 415, 678, 830, 912, 955, 977, 988, 994, 997, 998, 999];

// ---------------------------------------------------------------------------
// cSHAKE256 + Canonical LEB128 Framing
// ---------------------------------------------------------------------------

pub use obend_keccak::cshake256_32;
use obend_keccak::{keccak_f1600, Cshake256, SHAKE256_RATE_BYTES};

/// Encodes a u64 in at most ten canonical unsigned LEB128 bytes.
fn leb128_bytes(mut value: u64, buf: &mut [u8; 10]) -> &[u8] {
    let mut i = 0;
    while value >= 128 {
        buf[i] = (value as u8 & 0x7f) | 0x80;
        value >>= 7;
        i += 1;
    }
    buf[i] = value as u8;
    &buf[..=i]
}

/// Appends canonical unsigned LEB128 encoding of `value`, matching `Obend.Crypto.leb128`.
pub fn encode_leb128(value: u64, out: &mut Vec<u8>) {
    out.extend_from_slice(leb128_bytes(value, &mut [0; 10]));
}

fn leb128_vec(value: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(10);
    encode_leb128(value, &mut out);
    out
}

/// Decodes canonical unsigned LEB128, rejecting truncation, u64 overflow, and non-minimal zero padding.
pub fn decode_leb128(bytes: &[u8], cursor: &mut usize) -> Result<u64, ZkmlGateRefusal> {
    let mut acc = 0u64;
    let mut shift = 0u32;
    loop {
        if *cursor >= bytes.len() {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "truncated LEB128 varint",
            });
        }
        let byte = bytes[*cursor];
        *cursor += 1;
        let low = (byte & 0x7f) as u64;
        if shift == 63 && low > 1 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "LEB128 varint overflows u64",
            });
        }
        if byte < 0x80 {
            if shift > 0 && low == 0 {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason: "non-canonical overlong LEB128 varint",
                });
            }
            return Ok(acc | (low << shift));
        }
        acc |= low << shift;
        shift += 7;
        if shift > 63 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "LEB128 varint exceeds 10 bytes",
            });
        }
    }
}

/// Canonical bijective signed integer encoding matching Lean `encodeSignedInt`:
/// `z >= 0 => 0x00 || leb128(z)`, `z < 0 => 0x01 || leb128(-1 - z)` (`Int.negSucc`).
pub fn encode_signed_int(z: i64) -> Vec<u8> {
    let mut out = Vec::with_capacity(11);
    if z >= 0 {
        out.push(0x00);
        encode_leb128(z as u64, &mut out);
    } else {
        out.push(0x01);
        let neg_succ = ((-1i128) - (z as i128)) as u64;
        encode_leb128(neg_succ, &mut out);
    }
    out
}

pub fn decode_signed_int(bytes: &[u8]) -> Result<i64, ZkmlGateRefusal> {
    if bytes.is_empty() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "empty signed integer field",
        });
    }
    let tag = bytes[0];
    let mut cursor = 1usize;
    let mag = decode_leb128(bytes, &mut cursor)?;
    if cursor != bytes.len() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "trailing bytes in signed integer field",
        });
    }
    match tag {
        0x00 => i64::try_from(mag).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "positive signed integer overflows i64",
        }),
        0x01 => {
            let v = -1i128 - (mag as i128);
            i64::try_from(v).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "negative signed integer underflows i64",
            })
        }
        _ => Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "invalid sign tag in signed integer field",
        }),
    }
}

/// Appends one self-delimiting LEB128 length-prefixed field (`leb128(field.len()) || field`).
pub fn push_framed_field(out: &mut Vec<u8>, field: &[u8]) {
    encode_leb128(field.len() as u64, out);
    out.extend_from_slice(field);
}

fn encode_zkml_fields(fields: &[&[u8]]) -> Vec<u8> {
    let total: usize = fields.iter().map(|f| 2 + f.len()).sum();
    let mut out = Vec::with_capacity(total);
    for f in fields {
        push_framed_field(&mut out, f);
    }
    out
}

fn read_framed_field<'a>(bytes: &'a [u8], cursor: &mut usize) -> Result<&'a [u8], ZkmlGateRefusal> {
    let len_u64 = decode_leb128(bytes, cursor)?;
    let len = usize::try_from(len_u64).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
        reason: "framed field length overflows usize",
    })?;
    let end = cursor
        .checked_add(len)
        .ok_or(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "framed field length overflow",
        })?;
    if end > bytes.len() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "framed field truncated",
        });
    }
    let slice = &bytes[*cursor..end];
    *cursor = end;
    Ok(slice)
}

fn read_bounded_framed_fields(
    bytes: &[u8],
    max_fields: usize,
) -> Result<Vec<&[u8]>, ZkmlGateRefusal> {
    let mut cursor = 0usize;
    let mut out = Vec::with_capacity(max_fields.min(16));
    while cursor < bytes.len() {
        if out.len() >= max_fields {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "framed field count exceeds protocol arity bound",
            });
        }
        out.push(read_framed_field(bytes, &mut cursor)?);
    }
    Ok(out)
}

/// Checks whether the first `bits` low bits (little-endian in `digest[0..8]`) of `digest` are zero.
#[inline]
pub fn digest_has_low_zero_bits(digest: &[u8; 32], bits: u32) -> bool {
    let sample = u64::from_le_bytes([
        digest[0], digest[1], digest[2], digest[3], digest[4], digest[5], digest[6], digest[7],
    ]);
    low_bits_zero(sample, bits)
}

/// Whether the low `bits` bits of `sample` are zero; more than 64 bits is never satisfied.
fn low_bits_zero(sample: u64, bits: u32) -> bool {
    match bits {
        0 => true,
        1..=63 => sample & ((1u64 << bits) - 1) == 0,
        64 => sample == 0,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// 1. Honest UD-100 (UDR / JBR vs. Withdrawn CBR-130) Soundness Gate
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SecurityRegime {
    ProvenUdr100,
    ProvenJbr100,
    WithdrawnCapacityBound,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ZkmlProtocolMode {
    IrV2Fri,
    BaseFoldRs,
    EinSumcheckMxfp4,
}

impl ZkmlProtocolMode {
    #[inline]
    const fn tag_byte(self) -> u8 {
        match self {
            ZkmlProtocolMode::IrV2Fri => 1,
            ZkmlProtocolMode::BaseFoldRs => 2,
            ZkmlProtocolMode::EinSumcheckMxfp4 => 3,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZkmlSuiteProfile {
    pub field_modulus_bits: u32,
    pub ext_degree: u32,
    pub log_blowup: u32,
    pub num_queries: u32,
    pub grind_bits: u32,
    pub log_trace_height: u32,
    pub digest_bits: u32,
    pub log_arity: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkmlSoundnessReport {
    pub regime: SecurityRegime,
    pub regime_query_grind_milli_bits: u64,
    pub udr_milli_bits: u64,
    pub jbr_milli_bits: u64,
    pub legacy_withdrawn_cbr_milli_bits: u64,
    pub logup_ext_ceiling_milli_bits: u64,
    pub bcs_digest_ceiling_milli_bits: u64,
    pub effective_proven_milli_bits: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkmlGateRefusal {
    WithdrawnCbrRegime {
        legacy_cbr_milli_bits: u64,
        udr_milli_bits: u64,
    },
    UnpinnedOrZeroAritySuite {
        reason: &'static str,
    },
    InsufficientProvenBits {
        regime: SecurityRegime,
        achieved_milli_bits: u64,
        required_milli_bits: u64,
    },
    LogUpExtensionWall {
        ext_degree: u32,
        field_modulus_bits: u32,
        log_trace_height: u32,
        realized_milli_bits: u64,
        required_milli_bits: u64,
    },
    BrokenChunkCarry {
        chunk_idx: u64,
        expected_state_in: [u8; 32],
        actual_state_in: [u8; 32],
    },
    WeightRootMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    InvalidChunkPow {
        chunk_idx: u64,
        required_bits: u32,
        pow_nonce: u64,
    },
    InvalidChunkIopProof {
        chunk_idx: u64,
        reason: &'static str,
    },
    PolicyFloorMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    SuiteDigestMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    EmptyChunkChain,
    ChunkIndexMismatch {
        expected: u64,
        actual: u64,
    },
    ChunkCommitmentMismatch {
        chunk_idx: u64,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    CandidateBindingMismatch {
        reason: &'static str,
    },
    Cancelled,
}

impl fmt::Display for ZkmlGateRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ZkmlGateRefusal::WithdrawnCbrRegime {
                legacy_cbr_milli_bits,
                udr_milli_bits,
            } => write!(
                f,
                "withdrawn CapacityBound regime refused (legacy_cbr={legacy_cbr_milli_bits} mbit, actual_udr={udr_milli_bits} mbit)"
            ),
            ZkmlGateRefusal::UnpinnedOrZeroAritySuite { reason } => {
                write!(f, "unpinned or zero-arity zkML suite refused: {reason}")
            }
            ZkmlGateRefusal::InsufficientProvenBits {
                regime,
                achieved_milli_bits,
                required_milli_bits,
            } => write!(
                f,
                "insufficient proven soundness in {regime:?}: {achieved_milli_bits} < {required_milli_bits} milli-bits"
            ),
            ZkmlGateRefusal::LogUpExtensionWall {
                ext_degree,
                field_modulus_bits,
                log_trace_height,
                realized_milli_bits,
                required_milli_bits,
            } => write!(
                f,
                "LogUp extension wall hit (ext_degree={ext_degree}, field_bits={field_modulus_bits}, log_trace={log_trace_height}): {realized_milli_bits} < {required_milli_bits} milli-bits"
            ),
            ZkmlGateRefusal::BrokenChunkCarry { chunk_idx, .. } => {
                write!(f, "broken layer activation carry at chunk {chunk_idx}")
            }
            ZkmlGateRefusal::WeightRootMismatch { chunk_idx, .. } => match chunk_idx {
                Some(idx) => write!(f, "model_weights_root mismatch at chunk {idx}"),
                None => write!(f, "model_weights_root mismatch"),
            },
            ZkmlGateRefusal::InvalidChunkPow {
                chunk_idx,
                required_bits,
                pow_nonce,
            } => write!(
                f,
                "invalid chunk PoW at chunk {chunk_idx}: nonce {pow_nonce} fails {required_bits}-bit target"
            ),
            ZkmlGateRefusal::InvalidChunkIopProof { chunk_idx, reason } => {
                write!(f, "invalid MXFP4 EinSumcheck chunk IOP proof at chunk {chunk_idx}: {reason}")
            }
            ZkmlGateRefusal::PolicyFloorMismatch { chunk_idx, .. } => match chunk_idx {
                Some(idx) => write!(f, "policy_floor_digest mismatch at chunk {idx}"),
                None => write!(f, "policy_floor_digest mismatch"),
            },
            ZkmlGateRefusal::SuiteDigestMismatch { chunk_idx, .. } => match chunk_idx {
                Some(idx) => write!(f, "suite_digest mismatch at chunk {idx}"),
                None => write!(f, "suite_digest mismatch"),
            },
            ZkmlGateRefusal::EmptyChunkChain => write!(f, "empty zkML chunk chain"),
            ZkmlGateRefusal::ChunkIndexMismatch { expected, actual } => {
                write!(f, "chunk index mismatch: expected {expected}, got {actual}")
            }
            ZkmlGateRefusal::ChunkCommitmentMismatch { chunk_idx, .. } => {
                write!(f, "chunk commitment mismatch at chunk {chunk_idx}")
            }
            ZkmlGateRefusal::CandidateBindingMismatch { reason } => {
                write!(f, "candidate computation binding mismatch: {reason}")
            }
            ZkmlGateRefusal::Cancelled => write!(f, "streaming zkML prove job cancelled"),
        }
    }
}

impl std::error::Error for ZkmlGateRefusal {}

#[inline]
pub const fn udr_query_milli_bits(log_blowup: u32) -> u64 {
    if (log_blowup as usize) < UDR_QUERY_MILLI_BITS_TABLE.len() {
        UDR_QUERY_MILLI_BITS_TABLE[log_blowup as usize]
    } else {
        999
    }
}

#[inline]
pub const fn jbr_query_milli_bits(log_blowup: u32) -> u64 {
    (log_blowup as u64).saturating_mul(500)
}

#[inline]
pub const fn legacy_cbr_query_milli_bits(log_blowup: u32) -> u64 {
    (log_blowup as u64).saturating_mul(MILLI_BITS_PER_BIT)
}

impl ZkmlSuiteProfile {
    pub const fn deployed_ir2_babybear_ext4_legacy() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 19,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
            log_arity: 1,
        }
    }

    pub const fn proven_udr100_babybear_ext4() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
            log_arity: 1,
        }
    }

    pub const fn proven_udr100_babybear_ext5() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 5,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            log_trace_height: 25,
            digest_bits: 256,
            log_arity: 1,
        }
    }

    pub const fn proven_jbr100_babybear_ext4() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 28,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
            log_arity: 1,
        }
    }

    pub const fn proven_udr100_goldilocks_ext2() -> Self {
        Self {
            field_modulus_bits: GOLDILOCKS_MODULUS_BITS,
            ext_degree: 2,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
            log_arity: 1,
        }
    }

    /// Wide-leaf `UD-100` profile `(lb=2, q=148, pow=0, log_arity=4)` (`100.344` proven UDR bits).
    pub const fn wide_leaf_udr100_goldilocks_ext2() -> Self {
        Self {
            field_modulus_bits: GOLDILOCKS_MODULUS_BITS,
            ext_degree: 2,
            log_blowup: 2,
            num_queries: 148,
            grind_bits: 0,
            log_trace_height: 20,
            digest_bits: 256,
            log_arity: 4,
        }
    }

    #[inline]
    pub const fn udr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(udr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    #[inline]
    pub const fn jbr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(jbr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    #[inline]
    pub const fn legacy_withdrawn_cbr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(legacy_cbr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    /// Conservative LogUp extension-field ceiling using `floor(log2(p)) = field_modulus_bits - 1`
    /// (since every odd prime of bit-width `b` satisfies `2^{b-1} < p < 2^b`, preventing
    /// boundary overcounts such as BabyBear `b = 31` where `4 * log2(2^31 - 2^27 + 1) = 123.628 < 124`).
    #[inline]
    pub const fn logup_ext_ceiling_milli_bits(&self) -> u64 {
        let floor_log2_p = (self.field_modulus_bits as u64).saturating_sub(1);
        let ext_bits = floor_log2_p.saturating_mul(self.ext_degree as u64);
        ext_bits
            .saturating_sub(self.log_trace_height as u64)
            .saturating_mul(MILLI_BITS_PER_BIT)
    }

    #[inline]
    pub const fn bcs_digest_ceiling_milli_bits(&self) -> u64 {
        ((self.digest_bits / 2) as u64).saturating_mul(MILLI_BITS_PER_BIT)
    }

    /// Canonical 8-field `cSHAKE256("OBEND.SHE.ZKML_SUITE/v1", ...)` digest matching
    /// `ZkmlSuiteProfile.digest` in `EinSumcheckMxfp4.lean`.
    pub fn profile_digest(&self) -> [u8; 32] {
        let fb = leb128_vec(self.field_modulus_bits as u64);
        let ed = leb128_vec(self.ext_degree as u64);
        let lb = leb128_vec(self.log_blowup as u64);
        let nq = leb128_vec(self.num_queries as u64);
        let gb = leb128_vec(self.grind_bits as u64);
        let th = leb128_vec(self.log_trace_height as u64);
        let db = leb128_vec(self.digest_bits as u64);
        let la = leb128_vec(self.log_arity as u64);
        let pre = encode_zkml_fields(&[&fb, &ed, &lb, &nq, &gb, &th, &db, &la]);
        cshake256_32(ZKML_SUITE_DOMAIN_TAG, &pre)
    }

    pub const fn check_proven_floor(
        &self,
        regime: SecurityRegime,
    ) -> Result<ZkmlSoundnessReport, ZkmlGateRefusal> {
        if self.log_arity == 0 {
            return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
                reason: "log_arity == 0 is refused (must be >= 1)",
            });
        }
        if self.num_queries == 0 {
            return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
                reason: "num_queries == 0 is refused (must be >= 1)",
            });
        }

        let udr = self.udr_milli_bits();
        let jbr = self.jbr_milli_bits();
        let cbr = self.legacy_withdrawn_cbr_milli_bits();

        let regime_query_grind = match regime {
            SecurityRegime::WithdrawnCapacityBound => {
                return Err(ZkmlGateRefusal::WithdrawnCbrRegime {
                    legacy_cbr_milli_bits: cbr,
                    udr_milli_bits: udr,
                });
            }
            SecurityRegime::ProvenUdr100 => udr,
            SecurityRegime::ProvenJbr100 => jbr,
        };

        let logup_ceiling = self.logup_ext_ceiling_milli_bits();
        if logup_ceiling < PROVEN_MIN_MILLI_BITS {
            return Err(ZkmlGateRefusal::LogUpExtensionWall {
                ext_degree: self.ext_degree,
                field_modulus_bits: self.field_modulus_bits,
                log_trace_height: self.log_trace_height,
                realized_milli_bits: logup_ceiling,
                required_milli_bits: PROVEN_MIN_MILLI_BITS,
            });
        }

        let bcs_ceiling = self.bcs_digest_ceiling_milli_bits();
        if bcs_ceiling < PROVEN_MIN_MILLI_BITS {
            return Err(ZkmlGateRefusal::InsufficientProvenBits {
                regime,
                achieved_milli_bits: bcs_ceiling,
                required_milli_bits: PROVEN_MIN_MILLI_BITS,
            });
        }

        if regime_query_grind < PROVEN_MIN_MILLI_BITS {
            return Err(ZkmlGateRefusal::InsufficientProvenBits {
                regime,
                achieved_milli_bits: regime_query_grind,
                required_milli_bits: PROVEN_MIN_MILLI_BITS,
            });
        }

        let min_ab = if regime_query_grind < logup_ceiling {
            regime_query_grind
        } else {
            logup_ceiling
        };
        let effective = if min_ab < bcs_ceiling {
            min_ab
        } else {
            bcs_ceiling
        };

        Ok(ZkmlSoundnessReport {
            regime,
            regime_query_grind_milli_bits: regime_query_grind,
            udr_milli_bits: udr,
            jbr_milli_bits: jbr,
            legacy_withdrawn_cbr_milli_bits: cbr,
            logup_ext_ceiling_milli_bits: logup_ceiling,
            bcs_digest_ceiling_milli_bits: bcs_ceiling,
            effective_proven_milli_bits: effective,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkmlSuiteArtifact {
    pub suite_id: String,
    pub source_repo: String,
    pub source_commit: String,
    pub artifact_content_digest: [u8; 32],
    pub statement_codec_version: u32,
    pub proof_codec_version: u32,
    pub transcript_codec_version: u32,
    pub base_field_modulus: u64,
    pub base_field_codec_id: String,
    pub ext_degree: u32,
    pub defining_polynomial: String,
    pub ext_basis: String,
    pub poseidon2_width: u32,
    pub poseidon2_rate: u32,
    pub poseidon2_capacity: u32,
    pub poseidon2_sbox_alpha: u32,
    pub poseidon2_full_rounds: u32,
    pub poseidon2_partial_rounds: u32,
    pub round_constants_digest: [u8; 32],
    pub merkle_arity: u32,
    pub protocol_mode: ZkmlProtocolMode,
    pub fiat_shamir_alphabet_id: String,
    pub checker_id: String,
    pub checker_version: u32,
    pub checker_content_digest: [u8; 32],
    pub profile: ZkmlSuiteProfile,
}

impl ZkmlSuiteArtifact {
    pub fn babybear_fri(suite_id: impl Into<String>, profile: ZkmlSuiteProfile) -> Self {
        let ext_poly = match profile.ext_degree {
            4 => "X^4 - 11",
            5 => "X^5 - 2",
            _ => "custom",
        };
        let ext_basis = match profile.ext_degree {
            4 => "[1, X, X^2, X^3]",
            5 => "[1, X, X^2, X^3, X^4]",
            _ => "monomial",
        };
        Self {
            suite_id: suite_id.into(),
            source_repo: "breadstuffs".to_string(),
            source_commit: "e496fb48d6aaf374d4c0302c95c0fcc69bb8051d".to_string(),
            artifact_content_digest: sha256(b"dregg.ir2.babybear.poseidon2-w16.fri.v1"),
            statement_codec_version: 1,
            proof_codec_version: 1,
            transcript_codec_version: 1,
            base_field_modulus: BABYBEAR_MODULUS,
            base_field_codec_id: "babybear-canonical-u32-le".to_string(),
            ext_degree: profile.ext_degree,
            defining_polynomial: ext_poly.to_string(),
            ext_basis: ext_basis.to_string(),
            poseidon2_width: 16,
            poseidon2_rate: 8,
            poseidon2_capacity: 8,
            poseidon2_sbox_alpha: 7,
            poseidon2_full_rounds: 8,
            poseidon2_partial_rounds: 13,
            round_constants_digest: sha256(b"babybear-poseidon2-w16-rc-v1"),
            merkle_arity: 1u32 << profile.log_arity.min(16),
            protocol_mode: ZkmlProtocolMode::IrV2Fri,
            fiat_shamir_alphabet_id: "bcs-cshake256-leb128-v1".to_string(),
            checker_id: "obend.zkml.proven_gate".to_string(),
            checker_version: 3,
            checker_content_digest: sha256(b"obend.zkml.proven_gate.einsumcheck_mxfp4.v3"),
            profile,
        }
    }

    pub fn goldilocks_einsumcheck_mxfp4(
        suite_id: impl Into<String>,
        profile: ZkmlSuiteProfile,
    ) -> Self {
        Self {
            suite_id: suite_id.into(),
            source_repo: "obend".to_string(),
            source_commit: "proven-zkml-goldilocks-einsumcheck-mxfp4-v1".to_string(),
            artifact_content_digest: sha256(b"obend.she.zkml.goldilocks.einsumcheck_mxfp4.v1"),
            statement_codec_version: 1,
            proof_codec_version: 1,
            transcript_codec_version: 1,
            base_field_modulus: GOLDILOCKS_MODULUS,
            base_field_codec_id: "goldilocks-canonical-u64-be".to_string(),
            ext_degree: profile.ext_degree,
            defining_polynomial: "X (base Goldilocks p = 2^64 - 2^32 + 1)".to_string(),
            ext_basis: "[1]".to_string(),
            poseidon2_width: 0,
            poseidon2_rate: 0,
            poseidon2_capacity: 0,
            poseidon2_sbox_alpha: 0,
            poseidon2_full_rounds: 0,
            poseidon2_partial_rounds: 0,
            round_constants_digest: sha256(b"cshake256-obend-she-zkml-merkle-v1"),
            merkle_arity: 1u32 << profile.log_arity.min(16),
            protocol_mode: ZkmlProtocolMode::EinSumcheckMxfp4,
            fiat_shamir_alphabet_id: "fenzi-cshake256-leb128-v1".to_string(),
            checker_id: "obend.zkml.proven_gate".to_string(),
            checker_version: 3,
            checker_content_digest: sha256(b"obend.zkml.proven_gate.einsumcheck_mxfp4.v3"),
            profile,
        }
    }

    pub fn suite_digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(520);
        push_framed_field(&mut buf, self.suite_id.as_bytes());
        push_framed_field(&mut buf, self.source_repo.as_bytes());
        push_framed_field(&mut buf, self.source_commit.as_bytes());
        push_framed_field(&mut buf, &self.artifact_content_digest);
        push_framed_field(&mut buf, &self.statement_codec_version.to_be_bytes());
        push_framed_field(&mut buf, &self.proof_codec_version.to_be_bytes());
        push_framed_field(&mut buf, &self.transcript_codec_version.to_be_bytes());
        push_framed_field(&mut buf, &self.base_field_modulus.to_be_bytes());
        push_framed_field(&mut buf, self.base_field_codec_id.as_bytes());
        push_framed_field(&mut buf, &self.ext_degree.to_be_bytes());
        push_framed_field(&mut buf, self.defining_polynomial.as_bytes());
        push_framed_field(&mut buf, self.ext_basis.as_bytes());
        push_framed_field(&mut buf, &self.poseidon2_width.to_be_bytes());
        push_framed_field(&mut buf, &self.poseidon2_rate.to_be_bytes());
        push_framed_field(&mut buf, &self.poseidon2_capacity.to_be_bytes());
        push_framed_field(&mut buf, &self.poseidon2_sbox_alpha.to_be_bytes());
        push_framed_field(&mut buf, &self.poseidon2_full_rounds.to_be_bytes());
        push_framed_field(&mut buf, &self.poseidon2_partial_rounds.to_be_bytes());
        push_framed_field(&mut buf, &self.round_constants_digest);
        push_framed_field(&mut buf, &self.merkle_arity.to_be_bytes());
        push_framed_field(&mut buf, &[self.protocol_mode.tag_byte()]);
        push_framed_field(&mut buf, self.fiat_shamir_alphabet_id.as_bytes());
        push_framed_field(&mut buf, self.checker_id.as_bytes());
        push_framed_field(&mut buf, &self.checker_version.to_be_bytes());
        push_framed_field(&mut buf, &self.checker_content_digest);
        push_framed_field(&mut buf, &self.profile.field_modulus_bits.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.ext_degree.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.log_blowup.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.num_queries.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.grind_bits.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.log_trace_height.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.digest_bits.to_be_bytes());
        push_framed_field(&mut buf, &self.profile.log_arity.to_be_bytes());
        sha256(&buf)
    }

    pub fn check_proven_floor(
        &self,
        regime: SecurityRegime,
    ) -> Result<ZkmlSoundnessReport, ZkmlGateRefusal> {
        if self.ext_degree != self.profile.ext_degree {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "artifact ext_degree disagrees with profile ext_degree",
            });
        }
        if self.base_field_modulus < 2
            || (64 - self.base_field_modulus.leading_zeros()) != self.profile.field_modulus_bits
        {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "artifact base_field_modulus bit-width disagrees with profile field_modulus_bits",
            });
        }
        if self.merkle_arity < 2 {
            return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
                reason: "artifact merkle_arity < 2 refused",
            });
        }
        self.profile.check_proven_floor(regime)
    }
}

// ---------------------------------------------------------------------------
// 2. Canonical Goldilocks Field, E2M1 / 2^sh Domain, Merkle & Transcript
// ---------------------------------------------------------------------------

#[inline]
pub fn is_valid_e2m1_mantissa(q: i64) -> bool {
    E2M1_MANTISSA_DOMAIN.contains(&q)
}

#[inline]
pub const fn is_valid_mxfp4_shift(sh: u32) -> bool {
    sh <= MAX_MXFP4_SCALE_SHIFT
}

#[inline]
pub const fn int_to_goldilocks(z: i64) -> Goldilocks {
    if z >= 0 {
        Goldilocks::from_u64_reduced(z as u64)
    } else {
        Goldilocks::from_u64_reduced(z.unsigned_abs()).const_neg()
    }
}

#[inline]
pub const fn shift_to_goldilocks(sh: u32) -> Goldilocks {
    Goldilocks::from_u64_reduced(1u64 << sh)
}

#[inline]
pub fn gl_horner(coeffs: &[Goldilocks], x: Goldilocks) -> Goldilocks {
    let mut acc = Goldilocks::ZERO;
    for &c in coeffs.iter().rev() {
        acc = c + x * acc;
    }
    acc
}

fn decode_gl_be8(bytes: &[u8]) -> Result<Goldilocks, ZkmlGateRefusal> {
    if bytes.len() != 8 {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "Goldilocks scalar field must be 8 bytes",
        });
    }
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    Goldilocks::from_be_bytes_canonical(buf).map_err(|_| {
        ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "non-canonical Goldilocks scalar >= modulus",
        }
    })
}

pub fn encode_goldilocks_vec(xs: &[Goldilocks]) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + xs.len() * 8);
    encode_leb128(xs.len() as u64, &mut out);
    for &x in xs {
        out.extend_from_slice(&x.to_be_bytes());
    }
    out
}

pub fn decode_goldilocks_vec_bounded(
    bytes: &[u8],
    max_elems: usize,
) -> Result<Vec<Goldilocks>, ZkmlGateRefusal> {
    let mut cursor = 0usize;
    let count_u64 = decode_leb128(bytes, &mut cursor)?;
    let count =
        usize::try_from(count_u64).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "Goldilocks vector length overflows usize",
        })?;
    if count > max_elems {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "Goldilocks vector length exceeds protocol bound",
        });
    }
    let expected = count
        .checked_mul(8)
        .and_then(|n| n.checked_add(cursor))
        .ok_or(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "Goldilocks vector byte length overflow",
        })?;
    if expected != bytes.len() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "Goldilocks vector byte length mismatch",
        });
    }
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let elem = decode_gl_be8(&bytes[cursor..cursor + 8])?;
        cursor += 8;
        out.push(elem);
    }
    Ok(out)
}

pub fn decode_goldilocks_vec(bytes: &[u8]) -> Result<Vec<Goldilocks>, ZkmlGateRefusal> {
    decode_goldilocks_vec_bounded(bytes, 1usize << MAX_ZKML_HYPERCUBE_VARS)
}

fn encode_digest32_list(ds: &[[u8; 32]]) -> Vec<u8> {
    let refs: Vec<&[u8]> = ds.iter().map(|d| &d[..]).collect();
    encode_zkml_fields(&refs)
}

fn decode_digest32_list(bytes: &[u8]) -> Result<Vec<[u8; 32]>, ZkmlGateRefusal> {
    let fields = read_bounded_framed_fields(bytes, MAX_ZKML_HYPERCUBE_VARS)?;
    let mut out = Vec::with_capacity(fields.len());
    for f in fields {
        if f.len() != 32 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "Merkle digest in list is not 32 bytes",
            });
        }
        let mut arr = [0u8; 32];
        arr.copy_from_slice(f);
        out.push(arr);
    }
    Ok(out)
}

/// Succinct verifier key for one native `MXFP4` contraction layer (`OBEND.SHE.ZKML_WEIGHTS/v1`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Mxfp4LayerKey {
    pub log_i: usize,
    pub log_j: usize,
    pub log_k: usize,
    pub log_b: usize,
    pub q_merkle_root: [u8; 32],
    pub s_merkle_root: [u8; 32],
}

impl Mxfp4LayerKey {
    pub fn valid_dims(&self) -> bool {
        let Some(ij) = self.log_i.checked_add(self.log_j) else {
            return false;
        };
        let Some(ibk) = self
            .log_i
            .checked_add(self.log_b)
            .and_then(|v| v.checked_add(self.log_k))
        else {
            return false;
        };
        let Some(bkj) = self
            .log_b
            .checked_add(self.log_k)
            .and_then(|v| v.checked_add(self.log_j))
        else {
            return false;
        };
        self.log_i >= 1
            && self.log_j >= 1
            && self.log_k >= 1
            && self.log_b >= 1
            && ij < MAX_ZKML_HYPERCUBE_VARS
            && ibk < MAX_ZKML_HYPERCUBE_VARS
            && bkj < MAX_ZKML_HYPERCUBE_VARS
    }

    pub fn encode(&self) -> Vec<u8> {
        let li = leb128_vec(self.log_i as u64);
        let lj = leb128_vec(self.log_j as u64);
        let lk = leb128_vec(self.log_k as u64);
        let lb = leb128_vec(self.log_b as u64);
        encode_zkml_fields(&[&li, &lj, &lk, &lb, &self.q_merkle_root, &self.s_merkle_root])
    }
}

/// Verifier-pinned multi-layer `MXFP4` model manifest (`OBEND.SHE.ZKML_WEIGHTS/v1`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Mxfp4ModelManifest {
    pub layers: Vec<Mxfp4LayerKey>,
}

impl Mxfp4ModelManifest {
    pub fn valid(&self) -> bool {
        !self.layers.is_empty()
            && self.layers.len() <= MAX_ZKML_MODEL_LAYERS
            && self.layers.iter().all(Mxfp4LayerKey::valid_dims)
    }

    pub fn root(&self) -> [u8; 32] {
        let enc_layers: Vec<Vec<u8>> = self.layers.iter().map(Mxfp4LayerKey::encode).collect();
        let refs: Vec<&[u8]> = enc_layers.iter().map(Vec::as_slice).collect();
        cshake256_32(ZKML_WEIGHTS_DOMAIN_TAG, &encode_zkml_fields(&refs))
    }
}

fn zkml_leaf_32(tag: u8, idx: usize, payload: &[u8]) -> [u8; 32] {
    let mut pre = Vec::with_capacity(12 + payload.len());
    pre.push(tag);
    encode_leb128(idx as u64, &mut pre);
    pre.extend_from_slice(payload);
    cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &pre)
}

pub fn hash_tensor_leaf(idx: usize, x: Goldilocks) -> [u8; 32] {
    zkml_leaf_32(0x03, idx, &x.to_be_bytes())
}

pub fn hash_mantissa_leaf(idx: usize, q: i64) -> [u8; 32] {
    zkml_leaf_32(0x06, idx, &encode_signed_int(q))
}

pub fn hash_shift_leaf(idx: usize, sh: u32) -> [u8; 32] {
    zkml_leaf_32(0x07, idx, &leb128_vec(sh as u64))
}

pub fn hash_fold_pair_leaf(
    layer_idx: usize,
    pair_idx: usize,
    lo: Goldilocks,
    hi: Goldilocks,
) -> [u8; 32] {
    let pair_bytes = encode_goldilocks_vec(&[lo, hi]);
    let mut pre = Vec::with_capacity(24 + pair_bytes.len());
    pre.push(0x05);
    encode_leb128(layer_idx as u64, &mut pre);
    encode_leb128(pair_idx as u64, &mut pre);
    pre.extend_from_slice(&pair_bytes);
    cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &pre)
}

fn hash_merkle_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut pre = [0u8; 65];
    pre[0] = 0x01;
    pre[1..33].copy_from_slice(left);
    pre[33..65].copy_from_slice(right);
    cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &pre)
}

/// Precomputed `O(N)` binary `OBEND.SHE.ZKML_MERKLE/v1` tree enabling `O(log N)` sibling-path
/// lookups per query with zero subtree rehashing.
struct CachedMerkleTree {
    levels: Vec<Vec<[u8; 32]>>,
}

impl CachedMerkleTree {
    fn build(leaves: Vec<[u8; 32]>) -> Self {
        if leaves.is_empty() {
            return Self {
                levels: vec![vec![cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &[0x02])]],
            };
        }
        debug_assert!(leaves.len().is_power_of_two());
        let mut levels = Vec::with_capacity(leaves.len().trailing_zeros() as usize + 1);
        levels.push(leaves);
        while levels.last().map_or(0, Vec::len) > 1 {
            let prev = levels.last().expect("non-empty");
            let mut next = Vec::with_capacity(prev.len() / 2);
            let mut i = 0usize;
            while i + 1 < prev.len() {
                next.push(hash_merkle_node(&prev[i], &prev[i + 1]));
                i += 2;
            }
            levels.push(next);
        }
        Self { levels }
    }

    #[inline]
    fn root(&self) -> [u8; 32] {
        self.levels
            .last()
            .and_then(|top| top.first().copied())
            .unwrap_or_else(|| cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &[0x02]))
    }

    /// Root-to-leaf sibling path identical to [`zkml_merkle_path`] in `O(log N)` array reads.
    fn open_path(&self, idx: usize) -> Vec<[u8; 32]> {
        let depth = self.levels.len().saturating_sub(1);
        let mut path = Vec::with_capacity(depth);
        for d in (0..depth).rev() {
            let pos = idx >> d;
            let sib = pos ^ 1;
            path.push(self.levels[d][sib]);
        }
        path
    }
}

pub fn zkml_merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return cshake256_32(ZKML_MERKLE_DOMAIN_TAG, &[0x02]);
    }
    if leaves.len() == 1 {
        return leaves[0];
    }
    let half = leaves.len() / 2;
    let l = zkml_merkle_root(&leaves[..half]);
    let r = zkml_merkle_root(&leaves[half..]);
    hash_merkle_node(&l, &r)
}

pub fn zkml_merkle_path(leaves: &[[u8; 32]], idx: usize) -> Vec<[u8; 32]> {
    if leaves.len() < 2 {
        return Vec::new();
    }
    let half = leaves.len() / 2;
    if idx < half {
        let mut p = Vec::with_capacity(16);
        p.push(zkml_merkle_root(&leaves[half..]));
        p.extend(zkml_merkle_path(&leaves[..half], idx));
        p
    } else {
        let mut p = Vec::with_capacity(16);
        p.push(zkml_merkle_root(&leaves[..half]));
        p.extend(zkml_merkle_path(&leaves[half..], idx - half));
        p
    }
}

pub fn climb_zkml_merkle(
    tree_size: usize,
    idx: usize,
    leaf: [u8; 32],
    path: &[[u8; 32]],
) -> Option<[u8; 32]> {
    if path.is_empty() {
        return (tree_size == 1 && idx == 0).then_some(leaf);
    }
    if tree_size < 2 || idx >= tree_size {
        return None;
    }
    let half = tree_size / 2;
    let sib = path[0];
    if idx < half {
        climb_zkml_merkle(half, idx, leaf, &path[1..]).map(|l| hash_merkle_node(&l, &sib))
    } else {
        climb_zkml_merkle(tree_size - half, idx - half, leaf, &path[1..])
            .map(|r| hash_merkle_node(&sib, &r))
    }
}

pub fn mxfp4_tensor_root(xs: &[Goldilocks]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> = xs
        .iter()
        .enumerate()
        .map(|(i, &x)| hash_tensor_leaf(i, x))
        .collect();
    zkml_merkle_root(&leaves)
}

pub fn mxfp4_mantissa_root(qs: &[i64]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> = qs
        .iter()
        .enumerate()
        .map(|(i, &q)| hash_mantissa_leaf(i, q))
        .collect();
    zkml_merkle_root(&leaves)
}

pub fn mxfp4_shift_root(ss: &[u32]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> = ss
        .iter()
        .enumerate()
        .map(|(i, &sh)| hash_shift_leaf(i, sh))
        .collect();
    zkml_merkle_root(&leaves)
}

/// Phase-exact mirror of `Obend.Crypto.Transcript` (`Fenzi ePrint 2026/1838`).
#[derive(Clone, Debug)]
struct FsTranscript {
    state: [u8; 32],
    step_count: u64,
}

impl FsTranscript {
    fn new_instance_bound(
        protocol_id: &[u8],
        rel_bytes: &[u8],
        pub_io_bytes: &[u8],
        inst_root: &[u8; 32],
    ) -> Self {
        let seed_state = cshake256_32(FS_SEED_TAG, b"");
        let mut bind_pre =
            Vec::with_capacity(64 + protocol_id.len() + rel_bytes.len() + pub_io_bytes.len());
        push_framed_field(&mut bind_pre, &seed_state);
        push_framed_field(&mut bind_pre, protocol_id);
        push_framed_field(&mut bind_pre, rel_bytes);
        push_framed_field(&mut bind_pre, pub_io_bytes);
        let rel_state = cshake256_32(FS_BIND_TAG, &bind_pre);

        let step1 = leb128_vec(1);
        let inst_pre = encode_zkml_fields(&[&rel_state, &step1, inst_root]);
        let inst_state = cshake256_32(FS_INSTANCE_TAG, &inst_pre);
        Self {
            state: inst_state,
            step_count: 2,
        }
    }

    fn absorbed_state(&self, label: &[u8], msg_bytes: &[u8]) -> [u8; 32] {
        let mut third = Vec::with_capacity(10 + msg_bytes.len());
        encode_leb128(self.step_count, &mut third);
        third.extend_from_slice(msg_bytes);
        let frame = encode_zkml_fields(&[&self.state, label, &third]);
        cshake256_32(FS_ABSORB_TAG, &frame)
    }

    fn absorb_msg(&mut self, label: &[u8], msg_bytes: &[u8]) {
        self.state = self.absorbed_state(label, msg_bytes);
        self.step_count += 1;
    }

    fn squeeze_challenge_256(&mut self) -> [u8; 32] {
        let mut payload = Vec::with_capacity(44);
        push_framed_field(&mut payload, &self.state);
        encode_leb128(self.step_count, &mut payload);
        let out = cshake256_32(FS_SQUEEZE_TAG, &payload);

        let mut ratchet = Vec::with_capacity(68);
        push_framed_field(&mut ratchet, &self.state);
        push_framed_field(&mut ratchet, &out);
        self.state = cshake256_32(FS_RATCHET_TAG, &ratchet);
        self.step_count += 1;
        out
    }

    fn squeeze_goldilocks(&mut self) -> Goldilocks {
        let out = self.squeeze_challenge_256();
        let mut hi16 = [0u8; 16];
        hi16.copy_from_slice(&out[..16]);
        Goldilocks::from_u128_reduced(u128::from_be_bytes(hi16))
    }

    fn squeeze_goldilocks_vec(&mut self, n: usize) -> Vec<Goldilocks> {
        (0..n).map(|_| self.squeeze_goldilocks()).collect()
    }

    fn squeeze_raw_queries(&mut self, num_queries: usize) -> Vec<u64> {
        (0..num_queries)
            .map(|_| {
                let bytes = self.squeeze_challenge_256();
                u64::from_le_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ])
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// 3. Characteristic-Free Quadratic/Cubic Sumcheck, MXFP4 Contraction & Fold Walk
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RoundPoly {
    pub coeffs: Vec<Goldilocks>,
}

impl RoundPoly {
    #[inline]
    pub fn eval(&self, x: Goldilocks) -> Goldilocks {
        gl_horner(&self.coeffs, x)
    }

    #[inline]
    pub fn deg_le(&self, max_deg: usize) -> bool {
        self.coeffs.len() <= max_deg + 1
    }

    fn encode_transcript_msg(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2 + self.coeffs.len() * 9);
        encode_leb128(self.coeffs.len() as u64, &mut out);
        for &c in &self.coeffs {
            push_framed_field(&mut out, &c.to_be_bytes());
        }
        out
    }
}

fn encode_round_poly_list(ps: &[RoundPoly]) -> Vec<u8> {
    let enc: Vec<Vec<u8>> = ps
        .iter()
        .map(|p| encode_goldilocks_vec(&p.coeffs))
        .collect();
    let refs: Vec<&[u8]> = enc.iter().map(Vec::as_slice).collect();
    encode_zkml_fields(&refs)
}

fn decode_round_poly_list(bytes: &[u8]) -> Result<Vec<RoundPoly>, ZkmlGateRefusal> {
    let fields = read_bounded_framed_fields(bytes, MAX_ZKML_SUMCHECK_ROUNDS)?;
    fields
        .into_iter()
        .map(|f| {
            // Every MXFP4 EinSumcheck round has degree <= 3 (at most 4 coefficients), enforced pre-allocation:
            let coeffs = decode_goldilocks_vec_bounded(f, 4)?;
            Ok(RoundPoly { coeffs })
        })
        .collect()
}

pub fn fold_first_var(tbl: &[Goldilocks], r0: Goldilocks) -> Vec<Goldilocks> {
    let mut out = Vec::with_capacity(tbl.len().div_ceil(2));
    let mut i = 0usize;
    while i + 1 < tbl.len() {
        let lo = tbl[i];
        let hi = tbl[i + 1];
        out.push(lo + r0 * (hi - lo));
        i += 2;
    }
    if i < tbl.len() {
        let lo = tbl[i];
        out.push(lo + r0 * (Goldilocks::ZERO - lo));
    }
    out
}

pub fn fold_vars(tbl: &[Goldilocks], rs: &[Goldilocks]) -> Vec<Goldilocks> {
    let mut cur = tbl.to_vec();
    for &r in rs {
        cur = fold_first_var(&cur, r);
    }
    cur
}

pub fn mle_eval(tbl: &[Goldilocks], rs: &[Goldilocks]) -> Goldilocks {
    let eqs = eq_table(rs);
    tbl.iter()
        .zip(eqs.iter())
        .fold(Goldilocks::ZERO, |acc, (&v, &w)| acc + v * w)
}

pub fn eq_table(xs: &[Goldilocks]) -> Vec<Goldilocks> {
    let mut cur = vec![Goldilocks::ONE];
    for &x in xs.iter().rev() {
        let one_minus_x = Goldilocks::ONE - x;
        let mut next = Vec::with_capacity(cur.len() * 2);
        for &w in &cur {
            next.push(one_minus_x * w);
            next.push(x * w);
        }
        cur = next;
    }
    cur
}

pub fn eq_poly_vec(xs: &[Goldilocks], ys: &[Goldilocks]) -> Goldilocks {
    if xs.len() != ys.len() {
        return Goldilocks::ZERO;
    }
    let mut acc = Goldilocks::ONE;
    for (&x, &y) in xs.iter().zip(ys.iter()) {
        acc *= (Goldilocks::ONE - x) * (Goldilocks::ONE - y) + x * y;
    }
    acc
}

/// Characteristic-free degree-2 round polynomial matching `quadPairRoundPoly` in Lean.
pub fn quad_pair_round_poly(a: &[Goldilocks], b: &[Goldilocks]) -> RoundPoly {
    let mut c0 = Goldilocks::ZERO;
    let mut c1 = Goldilocks::ZERO;
    let mut c2 = Goldilocks::ZERO;
    let pairs = a.len().min(b.len()) / 2;
    for g in (0..pairs).rev() {
        let a0 = a[2 * g];
        let a1 = a[2 * g + 1];
        let b0 = b[2 * g];
        let b1 = b[2 * g + 1];
        let da = a1 - a0;
        let db = b1 - b0;
        c0 += a0 * b0;
        c1 += a0 * db + da * b0;
        c2 += da * db;
    }
    RoundPoly {
        coeffs: vec![c0, c1, c2],
    }
}

/// Characteristic-free degree-3 round polynomial matching `cubicTripleRoundPoly` in Lean.
pub fn cubic_triple_round_poly(a: &[Goldilocks], b: &[Goldilocks], c: &[Goldilocks]) -> RoundPoly {
    let mut d0 = Goldilocks::ZERO;
    let mut d1 = Goldilocks::ZERO;
    let mut d2 = Goldilocks::ZERO;
    let mut d3 = Goldilocks::ZERO;
    let pairs = a.len().min(b.len()).min(c.len()) / 2;
    for g in (0..pairs).rev() {
        let a0 = a[2 * g];
        let a1 = a[2 * g + 1];
        let b0 = b[2 * g];
        let b1 = b[2 * g + 1];
        let c0 = c[2 * g];
        let c1 = c[2 * g + 1];
        let da = a1 - a0;
        let db = b1 - b0;
        let dc = c1 - c0;
        let u0 = a0 * b0;
        let u1 = a0 * db + da * b0;
        let u2 = da * db;
        d0 += u0 * c0;
        d1 += u0 * dc + u1 * c0;
        d2 += u1 * dc + u2 * c0;
        d3 += u2 * dc;
    }
    RoundPoly {
        coeffs: vec![d0, d1, d2, d3],
    }
}

pub fn mxfp4_deg_schedule(log_b: usize, log_k: usize, log_j: usize) -> Vec<usize> {
    let mut s = Vec::with_capacity(log_b + log_k + log_j);
    s.extend(std::iter::repeat_n(2, log_b));
    s.extend(std::iter::repeat_n(3, log_k));
    s.extend(std::iter::repeat_n(3, log_j));
    s
}

/// Native 3-operand `MXFP4` contraction `D[i, j] = Σ_{k, b} X[i, b, k] · Q[b, k, j] · S[k, j]`
/// matching `mxfp4ContractTable` in `EinSumcheckMxfp4.lean`.
pub fn mxfp4_contract_table(
    log_i: usize,
    log_j: usize,
    log_k: usize,
    log_b: usize,
    x_tbl: &[Goldilocks],
    q_ints: &[i64],
    s_shifts: &[u32],
) -> Vec<Goldilocks> {
    let cap_i = 1usize << log_i;
    let cap_j = 1usize << log_j;
    let cap_k = 1usize << log_k;
    let cap_b = 1usize << log_b;
    let mut out = vec![Goldilocks::ZERO; cap_i * cap_j];
    for j in 0..cap_j {
        for i in 0..cap_i {
            let mut acc = Goldilocks::ZERO;
            for k in 0..cap_k {
                let s_kj = shift_to_goldilocks(s_shifts[k + cap_k * j]);
                for b in 0..cap_b {
                    let x_val = x_tbl[i + cap_i * (b + cap_b * k)];
                    let q_val = int_to_goldilocks(q_ints[b + cap_b * (k + cap_k * j)]);
                    acc += s_kj * q_val * x_val;
                }
            }
            out[i + cap_i * j] = acc;
        }
    }
    out
}

fn verify_scheduled_sumcheck(
    deg_schedule: &[usize],
    mut claimed_sum: Goldilocks,
    rounds: &[RoundPoly],
    tr: &mut FsTranscript,
) -> Option<(Vec<Goldilocks>, Goldilocks)> {
    if rounds.len() != deg_schedule.len() {
        return None;
    }
    let mut chals = Vec::with_capacity(deg_schedule.len());
    for (&max_deg, poly) in deg_schedule.iter().zip(rounds.iter()) {
        if !poly.deg_le(max_deg) {
            return None;
        }
        let sum01 = poly.eval(Goldilocks::ZERO) + poly.eval(Goldilocks::ONE);
        if sum01 != claimed_sum {
            return None;
        }
        tr.absorb_msg(SUMCHECK_ROUND_LABEL, &poly.encode_transcript_msg());
        let r = tr.squeeze_goldilocks();
        claimed_sum = poly.eval(r);
        chals.push(r);
    }
    Some((chals, claimed_sum))
}

#[allow(clippy::too_many_arguments)]
fn prove_mxfp4_sumcheck(
    log_i: usize,
    log_j: usize,
    log_k: usize,
    log_b: usize,
    x_tbl: &[Goldilocks],
    q_tbl: &[Goldilocks],
    s_tbl: &[Goldilocks],
    r_i: &[Goldilocks],
    r_j: &[Goldilocks],
    tr: &mut FsTranscript,
) -> (
    Vec<RoundPoly>,
    Vec<Goldilocks>,
    Vec<Goldilocks>,
    Vec<Goldilocks>,
) {
    let cap_j = 1usize << log_j;
    let cap_k = 1usize << log_k;
    let cap_b = 1usize << log_b;
    let _ = log_i;

    let x_bk = fold_vars(x_tbl, r_i);
    let eq_j = eq_table(r_j);

    // Phase 1 (`b`-rounds, deg <= 2):
    let mut a_b = Vec::with_capacity(cap_b * cap_k * cap_j);
    for _ in 0..cap_j {
        a_b.extend_from_slice(&x_bk);
    }
    let mut s_eq_kj = Vec::with_capacity(cap_k * cap_j);
    for (j, &ej) in eq_j.iter().enumerate() {
        for k in 0..cap_k {
            s_eq_kj.push(ej * s_tbl[k + cap_k * j]);
        }
    }
    let mut b_b = Vec::with_capacity(cap_b * cap_k * cap_j);
    for (kj, &w) in s_eq_kj.iter().enumerate() {
        let base = kj * cap_b;
        for b in 0..cap_b {
            b_b.push(w * q_tbl[base + b]);
        }
    }

    let mut rounds = Vec::with_capacity(log_b + log_k + log_j);
    let mut r_b = Vec::with_capacity(log_b);
    for _ in 0..log_b {
        let p = quad_pair_round_poly(&a_b, &b_b);
        tr.absorb_msg(SUMCHECK_ROUND_LABEL, &p.encode_transcript_msg());
        let r = tr.squeeze_goldilocks();
        a_b = fold_first_var(&a_b, r);
        b_b = fold_first_var(&b_b, r);
        rounds.push(p);
        r_b.push(r);
    }

    // Phase 2 (`k`-rounds, deg <= 3):
    let x_k = fold_vars(&x_bk, &r_b);
    let mut a_k = Vec::with_capacity(cap_k * cap_j);
    for _ in 0..cap_j {
        a_k.extend_from_slice(&x_k);
    }
    let mut b_k = fold_vars(q_tbl, &r_b);
    let mut c_k = s_eq_kj;
    let mut r_k = Vec::with_capacity(log_k);
    for _ in 0..log_k {
        let p = cubic_triple_round_poly(&a_k, &b_k, &c_k);
        tr.absorb_msg(SUMCHECK_ROUND_LABEL, &p.encode_transcript_msg());
        let r = tr.squeeze_goldilocks();
        a_k = fold_first_var(&a_k, r);
        b_k = fold_first_var(&b_k, r);
        c_k = fold_first_var(&c_k, r);
        rounds.push(p);
        r_k.push(r);
    }

    // Phase 3 (`j`-rounds, deg <= 3):
    let mut full_x_pt = Vec::with_capacity(r_i.len() + r_b.len() + r_k.len());
    full_x_pt.extend_from_slice(r_i);
    full_x_pt.extend_from_slice(&r_b);
    full_x_pt.extend_from_slice(&r_k);
    let x_star = mle_eval(x_tbl, &full_x_pt);

    let mut a_j: Vec<Goldilocks> = eq_j.iter().map(|&e| x_star * e).collect();
    let mut b_j = b_k;
    let mut c_j = fold_vars(s_tbl, &r_k);
    let mut r_jp = Vec::with_capacity(log_j);
    for _ in 0..log_j {
        let p = cubic_triple_round_poly(&a_j, &b_j, &c_j);
        tr.absorb_msg(SUMCHECK_ROUND_LABEL, &p.encode_transcript_msg());
        let r = tr.squeeze_goldilocks();
        a_j = fold_first_var(&a_j, r);
        b_j = fold_first_var(&b_j, r);
        c_j = fold_first_var(&c_j, r);
        rounds.push(p);
        r_jp.push(r);
    }

    (rounds, r_b, r_k, r_jp)
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FoldLayerStep {
    pub lo: Goldilocks,
    pub hi: Goldilocks,
    pub merkle_path: Vec<[u8; 32]>,
}

impl FoldLayerStep {
    pub fn encode(&self) -> Vec<u8> {
        let pair = encode_goldilocks_vec(&[self.lo, self.hi]);
        let path = encode_digest32_list(&self.merkle_path);
        encode_zkml_fields(&[&pair, &path])
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, ZkmlGateRefusal> {
        let fs = read_bounded_framed_fields(bytes, 2)?;
        if fs.len() != 2 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "FoldLayerStep must have 2 framed fields",
            });
        }
        let pair = decode_goldilocks_vec_bounded(fs[0], 2)?;
        if pair.len() != 2 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "FoldLayerStep pair must have 2 Goldilocks elements",
            });
        }
        Ok(Self {
            lo: pair[0],
            hi: pair[1],
            merkle_path: decode_digest32_list(fs[1])?,
        })
    }
}

fn encode_fold_steps(steps: &[FoldLayerStep]) -> Vec<u8> {
    let enc: Vec<Vec<u8>> = steps.iter().map(FoldLayerStep::encode).collect();
    let refs: Vec<&[u8]> = enc.iter().map(Vec::as_slice).collect();
    encode_zkml_fields(&refs)
}

fn decode_fold_steps(bytes: &[u8]) -> Result<Vec<FoldLayerStep>, ZkmlGateRefusal> {
    let fs = read_bounded_framed_fields(bytes, MAX_ZKML_HYPERCUBE_VARS)?;
    fs.into_iter().map(FoldLayerStep::decode).collect()
}

fn build_fold_layer_leaves(layer_idx: usize, rem: usize, tbl: &[Goldilocks]) -> Vec<[u8; 32]> {
    let pairs = 1usize << rem;
    (0..pairs)
        .map(|p| {
            let lo = tbl.get(2 * p).copied().unwrap_or(Goldilocks::ZERO);
            let hi = tbl.get(2 * p + 1).copied().unwrap_or(Goldilocks::ZERO);
            hash_fold_pair_leaf(layer_idx, p, lo, hi)
        })
        .collect()
}

struct PrecomputedFoldChain {
    roots: Vec<[u8; 32]>,
    layers: Vec<(Vec<Goldilocks>, CachedMerkleTree)>,
}

fn build_precomputed_fold_chain(
    num_vars: usize,
    tbl: &[Goldilocks],
    chals: &[Goldilocks],
) -> PrecomputedFoldChain {
    let mut cur = tbl.to_vec();
    let mut roots = Vec::with_capacity(num_vars);
    let mut layers = Vec::with_capacity(num_vars);
    for (layer_idx, &r) in chals.iter().take(num_vars).enumerate() {
        let rem = num_vars - 1 - layer_idx;
        let tree = CachedMerkleTree::build(build_fold_layer_leaves(layer_idx, rem, &cur));
        roots.push(tree.root());
        let next = fold_first_var(&cur, r);
        layers.push((cur, tree));
        cur = next;
    }
    PrecomputedFoldChain { roots, layers }
}

fn open_precomputed_fold_walk(chain: &PrecomputedFoldChain, mut idx: usize) -> Vec<FoldLayerStep> {
    let mut steps = Vec::with_capacity(chain.layers.len());
    for (cur, tree) in &chain.layers {
        let pair_idx = idx / 2;
        let lo = cur.get(2 * pair_idx).copied().unwrap_or(Goldilocks::ZERO);
        let hi = cur
            .get(2 * pair_idx + 1)
            .copied()
            .unwrap_or(Goldilocks::ZERO);
        let merkle_path = tree.open_path(pair_idx);
        steps.push(FoldLayerStep {
            lo,
            hi,
            merkle_path,
        });
        idx = pair_idx;
    }
    steps
}

fn verify_fold_walk(
    num_vars: usize,
    mut idx: usize,
    mut cur_val: Goldilocks,
    expected_final: Goldilocks,
    chals: &[Goldilocks],
    roots: &[[u8; 32]],
    steps: &[FoldLayerStep],
) -> bool {
    if chals.len() != num_vars || roots.len() != num_vars || steps.len() != num_vars {
        return false;
    }
    for layer_idx in 0..num_vars {
        let rem = num_vars - 1 - layer_idx;
        let st = &steps[layer_idx];
        let expected_side = if idx.is_multiple_of(2) { st.lo } else { st.hi };
        if cur_val != expected_side {
            return false;
        }
        let pair_idx = idx / 2;
        let leaf = hash_fold_pair_leaf(layer_idx, pair_idx, st.lo, st.hi);
        if climb_zkml_merkle(1usize << rem, pair_idx, leaf, &st.merkle_path)
            != Some(roots[layer_idx])
        {
            return false;
        }
        let r = chals[layer_idx];
        cur_val = st.lo + r * (st.hi - st.lo);
        idx = pair_idx;
    }
    idx == 0 && cur_val == expected_final
}

// ---------------------------------------------------------------------------
// 4. Succinct Wire Proof, Chunk Receipt, Windowed PoW Grinder & Verifiers
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Mxfp4QueryOpening {
    pub d_val: Goldilocks,
    pub d_path: Vec<[u8; 32]>,
    pub d_fold_steps: Vec<FoldLayerStep>,
    pub x_val: Goldilocks,
    pub x_path: Vec<[u8; 32]>,
    pub x_fold_steps: Vec<FoldLayerStep>,
    pub q_mantissa: i64,
    pub q_path: Vec<[u8; 32]>,
    pub q_fold_steps: Vec<FoldLayerStep>,
    pub s_shift: u32,
    pub s_path: Vec<[u8; 32]>,
    pub s_fold_steps: Vec<FoldLayerStep>,
}

impl Mxfp4QueryOpening {
    pub fn encode(&self) -> Vec<u8> {
        let dv = self.d_val.to_be_bytes();
        let dp = encode_digest32_list(&self.d_path);
        let df = encode_fold_steps(&self.d_fold_steps);
        let xv = self.x_val.to_be_bytes();
        let xp = encode_digest32_list(&self.x_path);
        let xf = encode_fold_steps(&self.x_fold_steps);
        let qm = encode_signed_int(self.q_mantissa);
        let qp = encode_digest32_list(&self.q_path);
        let qf = encode_fold_steps(&self.q_fold_steps);
        let ss = leb128_vec(self.s_shift as u64);
        let sp = encode_digest32_list(&self.s_path);
        let sf = encode_fold_steps(&self.s_fold_steps);
        encode_zkml_fields(&[&dv, &dp, &df, &xv, &xp, &xf, &qm, &qp, &qf, &ss, &sp, &sf])
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, ZkmlGateRefusal> {
        let fs = read_bounded_framed_fields(bytes, 12)?;
        if fs.len() != 12 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "Mxfp4QueryOpening must have 12 framed fields",
            });
        }
        let mut s_cur = 0usize;
        let s_u64 = decode_leb128(fs[9], &mut s_cur)?;
        if s_cur != fs[9].len() {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "trailing bytes in Mxfp4QueryOpening s_shift",
            });
        }
        let s_shift =
            u32::try_from(s_u64).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "s_shift overflows u32",
            })?;
        Ok(Self {
            d_val: decode_gl_be8(fs[0])?,
            d_path: decode_digest32_list(fs[1])?,
            d_fold_steps: decode_fold_steps(fs[2])?,
            x_val: decode_gl_be8(fs[3])?,
            x_path: decode_digest32_list(fs[4])?,
            x_fold_steps: decode_fold_steps(fs[5])?,
            q_mantissa: decode_signed_int(fs[6])?,
            q_path: decode_digest32_list(fs[7])?,
            q_fold_steps: decode_fold_steps(fs[8])?,
            s_shift,
            s_path: decode_digest32_list(fs[10])?,
            s_fold_steps: decode_fold_steps(fs[11])?,
        })
    }
}

/// Transparent succinct Goldilocks `MXFP4` `EinSumcheck` + BCS-Merkle chunk IOP proof
/// (zero per-chunk raw weights; round degrees `(2^logB, 3^logK, 3^logJ)`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SuccinctMxfp4IopProof {
    pub log_i: usize,
    pub log_j: usize,
    pub log_k: usize,
    pub log_b: usize,
    pub d_claim: Goldilocks,
    pub sumcheck_rounds: Vec<RoundPoly>,
    pub x_claim: Goldilocks,
    pub q_claim: Goldilocks,
    pub s_claim: Goldilocks,
    pub d_fold_roots: Vec<[u8; 32]>,
    pub x_fold_roots: Vec<[u8; 32]>,
    pub q_fold_roots: Vec<[u8; 32]>,
    pub s_fold_roots: Vec<[u8; 32]>,
    pub pow_nonce: u64,
    pub query_openings: Vec<Mxfp4QueryOpening>,
}

impl SuccinctMxfp4IopProof {
    pub fn encode(&self) -> Vec<u8> {
        let li = leb128_vec(self.log_i as u64);
        let lj = leb128_vec(self.log_j as u64);
        let lk = leb128_vec(self.log_k as u64);
        let lb = leb128_vec(self.log_b as u64);
        let dc = self.d_claim.to_be_bytes();
        let sr = encode_round_poly_list(&self.sumcheck_rounds);
        let xc = self.x_claim.to_be_bytes();
        let qc = self.q_claim.to_be_bytes();
        let sc = self.s_claim.to_be_bytes();
        let df = encode_digest32_list(&self.d_fold_roots);
        let xf = encode_digest32_list(&self.x_fold_roots);
        let qf = encode_digest32_list(&self.q_fold_roots);
        let sf = encode_digest32_list(&self.s_fold_roots);
        let pn = self.pow_nonce.to_be_bytes();
        let qo_enc: Vec<Vec<u8>> = self
            .query_openings
            .iter()
            .map(Mxfp4QueryOpening::encode)
            .collect();
        let qo_refs: Vec<&[u8]> = qo_enc.iter().map(Vec::as_slice).collect();
        let qo = encode_zkml_fields(&qo_refs);
        encode_zkml_fields(&[
            &li, &lj, &lk, &lb, &dc, &sr, &xc, &qc, &sc, &df, &xf, &qf, &sf, &pn, &qo,
        ])
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, ZkmlGateRefusal> {
        let fs = read_bounded_framed_fields(bytes, 15)?;
        if fs.len() != 15 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "SuccinctMxfp4IopProof must have 15 framed fields",
            });
        }
        let parse_dim = |b: &[u8]| -> Result<usize, ZkmlGateRefusal> {
            let mut c = 0usize;
            let v = decode_leb128(b, &mut c)?;
            if c != b.len() {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason: "trailing bytes in dimension field",
                });
            }
            usize::try_from(v).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "dimension overflows usize",
            })
        };
        if fs[13].len() != 8 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "pow_nonce must be 8 bytes",
            });
        }
        let mut pn_buf = [0u8; 8];
        pn_buf.copy_from_slice(fs[13]);
        let qo_fs = read_bounded_framed_fields(fs[14], MAX_ZKML_NUM_QUERIES)?;
        let mut query_openings = Vec::with_capacity(qo_fs.len());
        for qf in qo_fs {
            query_openings.push(Mxfp4QueryOpening::decode(qf)?);
        }
        Ok(Self {
            log_i: parse_dim(fs[0])?,
            log_j: parse_dim(fs[1])?,
            log_k: parse_dim(fs[2])?,
            log_b: parse_dim(fs[3])?,
            d_claim: decode_gl_be8(fs[4])?,
            sumcheck_rounds: decode_round_poly_list(fs[5])?,
            x_claim: decode_gl_be8(fs[6])?,
            q_claim: decode_gl_be8(fs[7])?,
            s_claim: decode_gl_be8(fs[8])?,
            d_fold_roots: decode_digest32_list(fs[9])?,
            x_fold_roots: decode_digest32_list(fs[10])?,
            q_fold_roots: decode_digest32_list(fs[11])?,
            s_fold_roots: decode_digest32_list(fs[12])?,
            pow_nonce: u64::from_be_bytes(pn_buf),
            query_openings,
        })
    }

    fn encode_post_fold_payload(&self) -> Vec<u8> {
        let xc = self.x_claim.to_be_bytes();
        let qc = self.q_claim.to_be_bytes();
        let sc = self.s_claim.to_be_bytes();
        let df = encode_digest32_list(&self.d_fold_roots);
        let xf = encode_digest32_list(&self.x_fold_roots);
        let qf = encode_digest32_list(&self.q_fold_roots);
        let sf = encode_digest32_list(&self.s_fold_roots);
        encode_zkml_fields(&[&xc, &qc, &sc, &df, &xf, &qf, &sf])
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ZkmlChunkReceipt {
    pub model_weights_root: [u8; 32],
    pub policy_floor_digest: [u8; 32],
    pub suite_digest: [u8; 32],
    pub chunk_idx: u64,
    pub layer_idx: u64,
    pub state_in_commit: [u8; 32],
    pub state_out_commit: [u8; 32],
    pub q_merkle_root: [u8; 32],
    pub s_merkle_root: [u8; 32],
    pub iop_proof: SuccinctMxfp4IopProof,
    pub chunk_commitment: [u8; 32],
}

#[allow(clippy::too_many_arguments)]
pub fn encode_zkml_chunk_preimage(
    model_weights_root: &[u8; 32],
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    layer_idx: u64,
    state_in_commit: &[u8; 32],
    state_out_commit: &[u8; 32],
    q_merkle_root: &[u8; 32],
    s_merkle_root: &[u8; 32],
    iop_proof: &SuccinctMxfp4IopProof,
) -> Vec<u8> {
    let cidx = chunk_idx.to_be_bytes();
    let lidx = layer_idx.to_be_bytes();
    let iop_bytes = iop_proof.encode();
    encode_zkml_fields(&[
        model_weights_root,
        policy_floor_digest,
        suite_digest,
        &cidx,
        &lidx,
        state_in_commit,
        state_out_commit,
        q_merkle_root,
        s_merkle_root,
        &iop_bytes,
    ])
}

#[allow(clippy::too_many_arguments)]
pub fn compute_zkml_chunk_commitment(
    model_weights_root: &[u8; 32],
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    layer_idx: u64,
    state_in_commit: &[u8; 32],
    state_out_commit: &[u8; 32],
    q_merkle_root: &[u8; 32],
    s_merkle_root: &[u8; 32],
    iop_proof: &SuccinctMxfp4IopProof,
) -> [u8; 32] {
    let pre = encode_zkml_chunk_preimage(
        model_weights_root,
        policy_floor_digest,
        suite_digest,
        chunk_idx,
        layer_idx,
        state_in_commit,
        state_out_commit,
        q_merkle_root,
        s_merkle_root,
        iop_proof,
    );
    cshake256_32(ZKML_CHUNK_DOMAIN_TAG, &pre)
}

impl ZkmlChunkReceipt {
    pub fn encode_preimage(&self) -> Vec<u8> {
        encode_zkml_chunk_preimage(
            &self.model_weights_root,
            &self.policy_floor_digest,
            &self.suite_digest,
            self.chunk_idx,
            self.layer_idx,
            &self.state_in_commit,
            &self.state_out_commit,
            &self.q_merkle_root,
            &self.s_merkle_root,
            &self.iop_proof,
        )
    }

    pub fn recompute_commitment(&self) -> [u8; 32] {
        cshake256_32(ZKML_CHUNK_DOMAIN_TAG, &self.encode_preimage())
    }

    pub fn encode_bytes(&self, out: &mut Vec<u8>) {
        let pre = self.encode_preimage();
        let rec = encode_zkml_fields(&[&pre, &self.chunk_commitment]);
        push_framed_field(out, &rec);
    }

    pub fn decode_bytes(bytes: &[u8]) -> Result<Self, ZkmlGateRefusal> {
        let outer = read_bounded_framed_fields(bytes, 2)?;
        if outer.len() != 2 || outer[1].len() != 32 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "ZkmlChunkReceipt must wrap (preimage, 32-byte chunk_commitment)",
            });
        }
        let fs = read_bounded_framed_fields(outer[0], 10)?;
        if fs.len() != 10 {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "ZkmlChunkReceipt preimage must have 10 framed fields",
            });
        }
        let arr32 = |b: &[u8]| -> Result<[u8; 32], ZkmlGateRefusal> {
            if b.len() != 32 {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason: "chunk header digest must be 32 bytes",
                });
            }
            let mut a = [0u8; 32];
            a.copy_from_slice(b);
            Ok(a)
        };
        let arr_u64 = |b: &[u8]| -> Result<u64, ZkmlGateRefusal> {
            if b.len() != 8 {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason: "chunk u64 index must be 8 bytes",
                });
            }
            let mut a = [0u8; 8];
            a.copy_from_slice(b);
            Ok(u64::from_be_bytes(a))
        };
        let mut chunk_commitment = [0u8; 32];
        chunk_commitment.copy_from_slice(outer[1]);
        Ok(Self {
            model_weights_root: arr32(fs[0])?,
            policy_floor_digest: arr32(fs[1])?,
            suite_digest: arr32(fs[2])?,
            chunk_idx: arr_u64(fs[3])?,
            layer_idx: arr_u64(fs[4])?,
            state_in_commit: arr32(fs[5])?,
            state_out_commit: arr32(fs[6])?,
            q_merkle_root: arr32(fs[7])?,
            s_merkle_root: arr32(fs[8])?,
            iop_proof: SuccinctMxfp4IopProof::decode(fs[9])?,
            chunk_commitment,
        })
    }
}

/// Service-enforced upper bound on per-job PoW grinder worker threads (`1..=MAX_DEFAULT_GRIND_THREADS`),
/// preventing job-supplied `grind_threads` from exhausting host OS threads while preserving `1T == NT` parity.
pub const MAX_ZKML_GRIND_THREADS: usize = MAX_DEFAULT_GRIND_THREADS;

/// Evaluates `FsTranscript::absorb_msg(label, nonce)` for many nonces at one transcript position.
///
/// When the frame and its padding fit one rate block, the `FS_ABSORB_TAG` prefix permutation and
/// every frame byte except the nonce are computed once, so a candidate costs one permutation and
/// no allocation. A longer frame goes through the transcript.
enum NonceAbsorber<'a> {
    OneBlock {
        /// The absorbed tag state xored with the padded frame, its nonce bytes zero.
        seeded: [u64; 25],
        lane: usize,
        shift: u32,
    },
    General {
        transcript: FsTranscript,
        label: &'a [u8],
    },
}

impl<'a> NonceAbsorber<'a> {
    fn new(state: &[u8; 32], step_count: u64, label: &'a [u8]) -> Self {
        let mut step_buf = [0; 10];
        let step = leb128_bytes(step_count, &mut step_buf);
        let third_len = step.len() + 8;
        // A fitting label is shorter than 128, so all three field lengths take one byte.
        let fixed_len = 3 + state.len() + third_len;
        if label.len() >= SHAKE256_RATE_BYTES - fixed_len {
            return Self::General {
                transcript: FsTranscript {
                    state: *state,
                    step_count,
                },
                label,
            };
        }
        let mut sponge = Cshake256::customized(FS_ABSORB_TAG);
        sponge.absorb(&[state.len() as u8]);
        sponge.absorb(state);
        sponge.absorb(&[label.len() as u8]);
        sponge.absorb(label);
        sponge.absorb(&[third_len as u8]);
        sponge.absorb(step);
        let nonce_at = sponge.position();
        sponge.absorb(&[0; 8]);
        Self::OneBlock {
            seeded: sponge.padded_lanes(),
            lane: nonce_at / 8,
            shift: 8 * (nonce_at % 8) as u32,
        }
    }

    /// The 32-byte digest `absorb_msg` would store, as four little-endian lanes.
    fn digest_lanes(&self, nonce: u64) -> [u64; 4] {
        match self {
            Self::OneBlock {
                seeded,
                lane,
                shift,
            } => {
                let mut st = *seeded;
                // The frame holds the nonce big-endian and lanes read bytes little-endian.
                let word = nonce.swap_bytes();
                st[*lane] ^= word << shift;
                if *shift != 0 {
                    st[*lane + 1] ^= word >> (64 - shift);
                }
                keccak_f1600(&mut st);
                [st[0], st[1], st[2], st[3]]
            }
            Self::General { transcript, label } => {
                digest_lanes(&transcript.absorbed_state(label, &nonce.to_be_bytes()))
            }
        }
    }
}

/// A 32-byte digest as its four little-endian lanes.
fn digest_lanes(digest: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (word, bytes) in out.iter_mut().zip(digest.as_chunks::<8>().0) {
        *word = u64::from_le_bytes(*bytes);
    }
    out
}

/// Deterministic `1T == NT` post-commit PoW grinder returning the exact lowest matching nonce `w`
/// (matching `grindChunkPowWindowed` in `EinSumcheckMxfp4.lean`, where `w - 1` is provably invalid).
pub fn grind_zkml_chunk_pow(
    post_fold_state: &[u8; 32],
    post_fold_step_count: u64,
    grind_bits: u32,
    span: u64,
    threads: usize,
    cancel: &CancelToken,
) -> Option<u64> {
    if span == 0 || grind_bits > 64 {
        return None;
    }
    if grind_bits == 0 {
        return (!cancel.is_cancelled()).then_some(0);
    }
    let window = default_grind_window(grind_bits as usize, 1);
    let capped_threads = threads.clamp(1, MAX_ZKML_GRIND_THREADS);
    let absorber = NonceAbsorber::new(post_fold_state, post_fold_step_count, ZKML_POW_NONCE_LABEL);
    windowed_find_map_first_cancellable(span, window, capped_threads, cancel, |cand| {
        low_bits_zero(absorber.digest_lanes(cand)[0], grind_bits).then_some(cand)
    })
    .map(|(_, nonce)| nonce)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mxfp4ChunkWitness {
    model: Mxfp4ModelManifest,
    layer_idx: u64,
    log_i: usize,
    log_j: usize,
    log_k: usize,
    log_b: usize,
    x_tbl: Vec<Goldilocks>,
    q_ints: Vec<i64>,
    s_shifts: Vec<u32>,
    d_tbl: Vec<Goldilocks>,
}

impl Mxfp4ChunkWitness {
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        model: Mxfp4ModelManifest,
        layer_idx: u64,
        log_i: usize,
        log_j: usize,
        log_k: usize,
        log_b: usize,
        x_tbl: Vec<Goldilocks>,
        q_ints: Vec<i64>,
        s_shifts: Vec<u32>,
    ) -> Result<Self, &'static str> {
        let ij = log_i.checked_add(log_j).ok_or("log_i + log_j overflow")?;
        let ibk = log_i
            .checked_add(log_b)
            .and_then(|v| v.checked_add(log_k))
            .ok_or("log_i + log_b + log_k overflow")?;
        let bkj = log_b
            .checked_add(log_k)
            .and_then(|v| v.checked_add(log_j))
            .ok_or("log_b + log_k + log_j overflow")?;
        if log_i == 0
            || log_j == 0
            || log_k == 0
            || log_b == 0
            || ij >= MAX_ZKML_HYPERCUBE_VARS
            || ibk >= MAX_ZKML_HYPERCUBE_VARS
            || bkj >= MAX_ZKML_HYPERCUBE_VARS
        {
            return Err("invalid MXFP4 contraction hypercube dimensions");
        }
        if !model.valid() {
            return Err("invalid Mxfp4ModelManifest");
        }
        let expected_x = 1usize << ibk;
        let expected_q = 1usize << bkj;
        let expected_s = 1usize << (log_k + log_j);
        if x_tbl.len() != expected_x {
            return Err("x_tbl length mismatch");
        }
        if q_ints.len() != expected_q || !q_ints.iter().all(|&q| is_valid_e2m1_mantissa(q)) {
            return Err("q_ints length or E2M1 domain membership failure");
        }
        if s_shifts.len() != expected_s || !s_shifts.iter().all(|&sh| is_valid_mxfp4_shift(sh)) {
            return Err("s_shifts length or max shift bound failure");
        }
        let q_root = mxfp4_mantissa_root(&q_ints);
        let s_root = mxfp4_shift_root(&s_shifts);
        let layer_usize = usize::try_from(layer_idx).map_err(|_| "layer_idx overflows usize")?;
        let lk = model
            .layers
            .get(layer_usize)
            .ok_or("layer_idx out of range in Mxfp4ModelManifest")?;
        if lk.log_i != log_i
            || lk.log_j != log_j
            || lk.log_k != log_k
            || lk.log_b != log_b
            || lk.q_merkle_root != q_root
            || lk.s_merkle_root != s_root
        {
            return Err("layer key in manifest disagrees with witness Q/S roots or dimensions");
        }
        let d_tbl = mxfp4_contract_table(log_i, log_j, log_k, log_b, &x_tbl, &q_ints, &s_shifts);
        Ok(Self {
            model,
            layer_idx,
            log_i,
            log_j,
            log_k,
            log_b,
            x_tbl,
            q_ints,
            s_shifts,
            d_tbl,
        })
    }

    pub fn model(&self) -> &Mxfp4ModelManifest {
        &self.model
    }

    pub fn layer_idx(&self) -> u64 {
        self.layer_idx
    }

    pub fn log_i(&self) -> usize {
        self.log_i
    }

    pub fn log_j(&self) -> usize {
        self.log_j
    }

    pub fn log_k(&self) -> usize {
        self.log_k
    }

    pub fn log_b(&self) -> usize {
        self.log_b
    }

    pub fn x_tbl(&self) -> &[Goldilocks] {
        &self.x_tbl
    }

    pub fn q_ints(&self) -> &[i64] {
        &self.q_ints
    }

    pub fn s_shifts(&self) -> &[u32] {
        &self.s_shifts
    }

    pub fn d_tbl(&self) -> &[Goldilocks] {
        &self.d_tbl
    }

    pub fn weights_root(&self) -> [u8; 32] {
        self.model.root()
    }

    pub fn state_in_commit(&self) -> [u8; 32] {
        mxfp4_tensor_root(&self.x_tbl)
    }

    pub fn state_out_commit(&self) -> [u8; 32] {
        mxfp4_tensor_root(&self.d_tbl)
    }

    pub fn q_merkle_root(&self) -> [u8; 32] {
        mxfp4_mantissa_root(&self.q_ints)
    }

    pub fn s_merkle_root(&self) -> [u8; 32] {
        mxfp4_shift_root(&self.s_shifts)
    }
}

#[allow(clippy::too_many_arguments)]
fn setup_mxfp4_transcript(
    profile: &ZkmlSuiteProfile,
    log_i: usize,
    log_j: usize,
    log_k: usize,
    log_b: usize,
    w_root: &[u8; 32],
    pol: &[u8; 32],
    suite_d: &[u8; 32],
    chunk_idx: u64,
    layer_idx: u64,
    s_in: &[u8; 32],
    s_out: &[u8; 32],
    q_root: &[u8; 32],
    s_root: &[u8; 32],
    d_claim: Goldilocks,
) -> (Vec<Goldilocks>, Vec<Goldilocks>, FsTranscript) {
    let li = leb128_vec(log_i as u64);
    let lj = leb128_vec(log_j as u64);
    let lk = leb128_vec(log_k as u64);
    let lb = leb128_vec(log_b as u64);
    let fbits = leb128_vec(profile.field_modulus_bits as u64);
    let edeg = leb128_vec(profile.ext_degree as u64);
    let blow = leb128_vec(profile.log_blowup as u64);
    let nq = leb128_vec(profile.num_queries as u64);
    let gb = leb128_vec(profile.grind_bits as u64);
    let lth = leb128_vec(profile.log_trace_height as u64);
    let dbits = leb128_vec(profile.digest_bits as u64);
    let la = leb128_vec(profile.log_arity as u64);
    let rel_bytes = encode_zkml_fields(&[
        &li, &lj, &lk, &lb, &fbits, &edeg, &blow, &nq, &gb, &lth, &dbits, &la,
    ]);

    let cidx = chunk_idx.to_be_bytes();
    let lidx = layer_idx.to_be_bytes();
    let pub_io = encode_zkml_fields(&[
        w_root, pol, suite_d, &cidx, &lidx, s_in, s_out, q_root, s_root,
    ]);

    let mut tr = FsTranscript::new_instance_bound(ZKML_IOP_PROTOCOL_ID, &rel_bytes, &pub_io, s_out);
    let r_i = tr.squeeze_goldilocks_vec(log_i);
    let r_j = tr.squeeze_goldilocks_vec(log_j);
    tr.absorb_msg(ZKML_D_CLAIM_LABEL, &d_claim.to_be_bytes());
    (r_i, r_j, tr)
}

#[allow(clippy::too_many_arguments)]
pub fn prove_mxfp4_chunk_iop(
    profile: &ZkmlSuiteProfile,
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    w: &Mxfp4ChunkWitness,
    grind_span: u64,
    grind_threads: usize,
    cancel: &CancelToken,
) -> Result<ZkmlChunkReceipt, ZkmlGateRefusal> {
    if cancel.is_cancelled() {
        return Err(ZkmlGateRefusal::Cancelled);
    }
    if profile.num_queries == 0
        || (profile.num_queries as usize) > MAX_ZKML_NUM_QUERIES
        || profile.log_arity == 0
    {
        return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
            reason: "profile num_queries out of bounds 1..=MAX_ZKML_NUM_QUERIES or log_arity == 0",
        });
    }
    let w_root = w.weights_root();
    let s_in = w.state_in_commit();
    let s_out = w.state_out_commit();
    let q_root = w.q_merkle_root();
    let s_root = w.s_merkle_root();
    let q_tbl: Vec<Goldilocks> = w.q_ints.iter().map(|&q| int_to_goldilocks(q)).collect();
    let s_tbl: Vec<Goldilocks> = w
        .s_shifts
        .iter()
        .map(|&sh| shift_to_goldilocks(sh))
        .collect();

    // Squeeze `(r_i, r_j)` first to compute `d_claim = mle_eval(d_tbl, r_i ++ r_j)`:
    let (r_i_pre, r_j_pre, _) = setup_mxfp4_transcript(
        profile,
        w.log_i,
        w.log_j,
        w.log_k,
        w.log_b,
        &w_root,
        policy_floor_digest,
        suite_digest,
        chunk_idx,
        w.layer_idx,
        &s_in,
        &s_out,
        &q_root,
        &s_root,
        Goldilocks::ZERO,
    );
    let mut pt_d = Vec::with_capacity(w.log_i + w.log_j);
    pt_d.extend_from_slice(&r_i_pre);
    pt_d.extend_from_slice(&r_j_pre);
    let d_claim = mle_eval(&w.d_tbl, &pt_d);

    let (r_i, r_j, mut tr) = setup_mxfp4_transcript(
        profile,
        w.log_i,
        w.log_j,
        w.log_k,
        w.log_b,
        &w_root,
        policy_floor_digest,
        suite_digest,
        chunk_idx,
        w.layer_idx,
        &s_in,
        &s_out,
        &q_root,
        &s_root,
        d_claim,
    );
    let (sumcheck_rounds, r_b, r_k, r_jp) = prove_mxfp4_sumcheck(
        w.log_i, w.log_j, w.log_k, w.log_b, &w.x_tbl, &q_tbl, &s_tbl, &r_i, &r_j, &mut tr,
    );

    let mut pt_x = Vec::with_capacity(w.log_i + w.log_b + w.log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&r_b);
    pt_x.extend_from_slice(&r_k);
    let mut pt_q = Vec::with_capacity(w.log_b + w.log_k + w.log_j);
    pt_q.extend_from_slice(&r_b);
    pt_q.extend_from_slice(&r_k);
    pt_q.extend_from_slice(&r_jp);
    let mut pt_s = Vec::with_capacity(w.log_k + w.log_j);
    pt_s.extend_from_slice(&r_k);
    pt_s.extend_from_slice(&r_jp);

    let x_claim = mle_eval(&w.x_tbl, &pt_x);
    let q_claim = mle_eval(&q_tbl, &pt_q);
    let s_claim = mle_eval(&s_tbl, &pt_s);

    let v_d = w.log_i + w.log_j;
    let v_x = w.log_i + w.log_b + w.log_k;
    let v_q = w.log_b + w.log_k + w.log_j;
    let v_s = w.log_k + w.log_j;

    let d_chain = build_precomputed_fold_chain(v_d, &w.d_tbl, &pt_d);
    let x_chain = build_precomputed_fold_chain(v_x, &w.x_tbl, &pt_x);
    let q_chain = build_precomputed_fold_chain(v_q, &q_tbl, &pt_q);
    let s_chain = build_precomputed_fold_chain(v_s, &s_tbl, &pt_s);

    let mut iop_proof = SuccinctMxfp4IopProof {
        log_i: w.log_i,
        log_j: w.log_j,
        log_k: w.log_k,
        log_b: w.log_b,
        d_claim,
        sumcheck_rounds,
        x_claim,
        q_claim,
        s_claim,
        d_fold_roots: d_chain.roots.clone(),
        x_fold_roots: x_chain.roots.clone(),
        q_fold_roots: q_chain.roots.clone(),
        s_fold_roots: s_chain.roots.clone(),
        pow_nonce: 0,
        query_openings: Vec::new(),
    };

    if profile.num_queries == 0 || (profile.num_queries as usize) > MAX_ZKML_NUM_QUERIES {
        return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
            reason: "profile num_queries out of bounds 1..=MAX_ZKML_NUM_QUERIES",
        });
    }

    tr.absorb_msg(ZKML_FOLD_ROOTS_LABEL, &iop_proof.encode_post_fold_payload());
    let pow_nonce = grind_zkml_chunk_pow(
        &tr.state,
        tr.step_count,
        profile.grind_bits,
        grind_span,
        grind_threads,
        cancel,
    )
    .ok_or_else(|| {
        if cancel.is_cancelled() {
            ZkmlGateRefusal::Cancelled
        } else {
            ZkmlGateRefusal::InvalidChunkPow {
                chunk_idx,
                required_bits: profile.grind_bits,
                pow_nonce: u64::MAX,
            }
        }
    })?;
    iop_proof.pow_nonce = pow_nonce;

    tr.absorb_msg(ZKML_POW_NONCE_LABEL, &pow_nonce.to_be_bytes());
    let raw_queries = tr.squeeze_raw_queries(profile.num_queries as usize);

    let d_tree = CachedMerkleTree::build(
        w.d_tbl
            .iter()
            .enumerate()
            .map(|(i, &d)| hash_tensor_leaf(i, d))
            .collect(),
    );
    let x_tree = CachedMerkleTree::build(
        w.x_tbl
            .iter()
            .enumerate()
            .map(|(i, &x)| hash_tensor_leaf(i, x))
            .collect(),
    );
    let q_tree = CachedMerkleTree::build(
        w.q_ints
            .iter()
            .enumerate()
            .map(|(i, &q)| hash_mantissa_leaf(i, q))
            .collect(),
    );
    let s_tree = CachedMerkleTree::build(
        w.s_shifts
            .iter()
            .enumerate()
            .map(|(i, &sh)| hash_shift_leaf(i, sh))
            .collect(),
    );

    let n_d = 1usize << v_d;
    let n_x = 1usize << v_x;
    let n_q = 1usize << v_q;
    let n_s = 1usize << v_s;

    let mut openings = Vec::with_capacity(raw_queries.len());
    for q_raw in raw_queries {
        if cancel.is_cancelled() {
            return Err(ZkmlGateRefusal::Cancelled);
        }
        let i_d = (q_raw % (n_d as u64)) as usize;
        let i_x = (q_raw % (n_x as u64)) as usize;
        let i_q = (q_raw % (n_q as u64)) as usize;
        let i_s = (q_raw % (n_s as u64)) as usize;
        openings.push(Mxfp4QueryOpening {
            d_val: w.d_tbl[i_d],
            d_path: d_tree.open_path(i_d),
            d_fold_steps: open_precomputed_fold_walk(&d_chain, i_d),
            x_val: w.x_tbl[i_x],
            x_path: x_tree.open_path(i_x),
            x_fold_steps: open_precomputed_fold_walk(&x_chain, i_x),
            q_mantissa: w.q_ints[i_q],
            q_path: q_tree.open_path(i_q),
            q_fold_steps: open_precomputed_fold_walk(&q_chain, i_q),
            s_shift: w.s_shifts[i_s],
            s_path: s_tree.open_path(i_s),
            s_fold_steps: open_precomputed_fold_walk(&s_chain, i_s),
        });
    }
    iop_proof.query_openings = openings;

    let chunk_commitment = compute_zkml_chunk_commitment(
        &w_root,
        policy_floor_digest,
        suite_digest,
        chunk_idx,
        w.layer_idx,
        &s_in,
        &s_out,
        &q_root,
        &s_root,
        &iop_proof,
    );

    Ok(ZkmlChunkReceipt {
        model_weights_root: w_root,
        policy_floor_digest: *policy_floor_digest,
        suite_digest: *suite_digest,
        chunk_idx,
        layer_idx: w.layer_idx,
        state_in_commit: s_in,
        state_out_commit: s_out,
        q_merkle_root: q_root,
        s_merkle_root: s_root,
        iop_proof,
        chunk_commitment,
    })
}

/// Verifies a succinct Goldilocks `MXFP4` `EinSumcheck` + BCS-Merkle chunk receipt byte-for-byte
/// identically to `verifyMxfp4ChunkIop` in `ProvenZkmlGate.lean`.
pub fn verify_mxfp4_chunk_iop(
    profile: &ZkmlSuiteProfile,
    model: &Mxfp4ModelManifest,
    required_pow_bits: u32,
    receipt: &ZkmlChunkReceipt,
) -> Result<(), ZkmlGateRefusal> {
    if !model.valid() {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: receipt.chunk_idx,
            reason: "invalid Mxfp4ModelManifest",
        });
    }
    let expected_w_root = model.root();
    verify_mxfp4_chunk_iop_prevalidated(
        profile,
        model,
        &expected_w_root,
        required_pow_bits,
        receipt,
    )
}

fn verify_mxfp4_chunk_iop_prevalidated(
    profile: &ZkmlSuiteProfile,
    model: &Mxfp4ModelManifest,
    expected_w_root: &[u8; 32],
    required_pow_bits: u32,
    receipt: &ZkmlChunkReceipt,
) -> Result<(), ZkmlGateRefusal> {
    let idx = receipt.chunk_idx;
    let p = &receipt.iop_proof;

    if profile.num_queries == 0
        || (profile.num_queries as usize) > MAX_ZKML_NUM_QUERIES
        || profile.log_arity == 0
    {
        return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
            reason: "profile num_queries out of bounds or log_arity == 0",
        });
    }
    if p.query_openings.len() != profile.num_queries as usize {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "query_openings length != profile.num_queries",
        });
    }
    if receipt.model_weights_root != *expected_w_root {
        return Err(ZkmlGateRefusal::WeightRootMismatch {
            chunk_idx: Some(idx),
            expected: *expected_w_root,
            actual: receipt.model_weights_root,
        });
    }
    let layer_usize =
        usize::try_from(receipt.layer_idx).map_err(|_| ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "layer_idx overflows usize",
        })?;
    let lk = model
        .layers
        .get(layer_usize)
        .ok_or(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "layer_idx out of bounds in Mxfp4ModelManifest",
        })?;
    if lk.log_i != p.log_i
        || lk.log_j != p.log_j
        || lk.log_k != p.log_k
        || lk.log_b != p.log_b
        || lk.q_merkle_root != receipt.q_merkle_root
        || lk.s_merkle_root != receipt.s_merkle_root
    {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "chunk proof layer dimensions or Q/S roots disagree with manifest",
        });
    }

    let v_d = p.log_i + p.log_j;
    let v_x = p.log_i + p.log_b + p.log_k;
    let v_q = p.log_b + p.log_k + p.log_j;
    let v_s = p.log_k + p.log_j;
    if p.d_fold_roots.len() != v_d
        || p.x_fold_roots.len() != v_x
        || p.q_fold_roots.len() != v_q
        || p.s_fold_roots.len() != v_s
    {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "fold_roots length mismatch against hypercube dimensions",
        });
    }

    let (r_i, r_j, mut tr) = setup_mxfp4_transcript(
        profile,
        p.log_i,
        p.log_j,
        p.log_k,
        p.log_b,
        &receipt.model_weights_root,
        &receipt.policy_floor_digest,
        &receipt.suite_digest,
        receipt.chunk_idx,
        receipt.layer_idx,
        &receipt.state_in_commit,
        &receipt.state_out_commit,
        &receipt.q_merkle_root,
        &receipt.s_merkle_root,
        p.d_claim,
    );

    let sched = mxfp4_deg_schedule(p.log_b, p.log_k, p.log_j);
    let (all_chals, final_val) =
        verify_scheduled_sumcheck(&sched, p.d_claim, &p.sumcheck_rounds, &mut tr).ok_or(
            ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "MXFP4 (2^logB, 3^logK, 3^logJ) scheduled sumcheck verification failed",
            },
        )?;

    let r_b = &all_chals[..p.log_b];
    let r_k = &all_chals[p.log_b..p.log_b + p.log_k];
    let r_jp = &all_chals[p.log_b + p.log_k..];

    let expected_final = eq_poly_vec(&r_j, r_jp) * p.x_claim * p.q_claim * p.s_claim;
    if final_val != expected_final {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason:
                "terminal EinSumcheck identity eq(r_j, r_j') * x_claim * q_claim * s_claim mismatch",
        });
    }

    tr.absorb_msg(ZKML_FOLD_ROOTS_LABEL, &p.encode_post_fold_payload());
    if profile.grind_bits > required_pow_bits
        || required_pow_bits > 64
        || (required_pow_bits == 0 && p.pow_nonce != 0)
    {
        return Err(ZkmlGateRefusal::InvalidChunkPow {
            chunk_idx: idx,
            required_bits: required_pow_bits,
            pow_nonce: p.pow_nonce,
        });
    }
    tr.absorb_msg(ZKML_POW_NONCE_LABEL, &p.pow_nonce.to_be_bytes());
    if !digest_has_low_zero_bits(&tr.state, required_pow_bits) {
        return Err(ZkmlGateRefusal::InvalidChunkPow {
            chunk_idx: idx,
            required_bits: required_pow_bits,
            pow_nonce: p.pow_nonce,
        });
    }

    let raw_queries = tr.squeeze_raw_queries(profile.num_queries as usize);
    if p.query_openings.len() != raw_queries.len() {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "query_openings length != num_queries",
        });
    }

    let mut pt_d = Vec::with_capacity(v_d);
    pt_d.extend_from_slice(&r_i);
    pt_d.extend_from_slice(&r_j);
    let mut pt_x = Vec::with_capacity(v_x);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(r_b);
    pt_x.extend_from_slice(r_k);
    let mut pt_q = Vec::with_capacity(v_q);
    pt_q.extend_from_slice(r_b);
    pt_q.extend_from_slice(r_k);
    pt_q.extend_from_slice(r_jp);
    let mut pt_s = Vec::with_capacity(v_s);
    pt_s.extend_from_slice(r_k);
    pt_s.extend_from_slice(r_jp);

    let n_d = 1usize << v_d;
    let n_x = 1usize << v_x;
    let n_q = 1usize << v_q;
    let n_s = 1usize << v_s;

    for (q_raw, op) in raw_queries.into_iter().zip(p.query_openings.iter()) {
        if !is_valid_e2m1_mantissa(op.q_mantissa) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "opened Q leaf violates signed E2M1 mantissa domain",
            });
        }
        if !is_valid_mxfp4_shift(op.s_shift) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "opened S leaf violates max MXFP4 power-of-two shift bound",
            });
        }

        let i_d = (q_raw % (n_d as u64)) as usize;
        let i_x = (q_raw % (n_x as u64)) as usize;
        let i_q = (q_raw % (n_q as u64)) as usize;
        let i_s = (q_raw % (n_s as u64)) as usize;

        if climb_zkml_merkle(n_d, i_d, hash_tensor_leaf(i_d, op.d_val), &op.d_path)
            != Some(receipt.state_out_commit)
        {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "D output tensor Merkle opening failed",
            });
        }
        if climb_zkml_merkle(n_x, i_x, hash_tensor_leaf(i_x, op.x_val), &op.x_path)
            != Some(receipt.state_in_commit)
        {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "X input activation Merkle opening failed",
            });
        }
        if climb_zkml_merkle(n_q, i_q, hash_mantissa_leaf(i_q, op.q_mantissa), &op.q_path)
            != Some(receipt.q_merkle_root)
        {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "Q E2M1 mantissa Merkle opening failed",
            });
        }
        if climb_zkml_merkle(n_s, i_s, hash_shift_leaf(i_s, op.s_shift), &op.s_path)
            != Some(receipt.s_merkle_root)
        {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "S block shift Merkle opening failed",
            });
        }

        if !verify_fold_walk(
            v_d,
            i_d,
            op.d_val,
            p.d_claim,
            &pt_d,
            &p.d_fold_roots,
            &op.d_fold_steps,
        ) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "D butterfly fold walk failed",
            });
        }
        if !verify_fold_walk(
            v_x,
            i_x,
            op.x_val,
            p.x_claim,
            &pt_x,
            &p.x_fold_roots,
            &op.x_fold_steps,
        ) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "X butterfly fold walk failed",
            });
        }
        if !verify_fold_walk(
            v_q,
            i_q,
            int_to_goldilocks(op.q_mantissa),
            p.q_claim,
            &pt_q,
            &p.q_fold_roots,
            &op.q_fold_steps,
        ) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "Q butterfly fold walk failed",
            });
        }
        if !verify_fold_walk(
            v_s,
            i_s,
            shift_to_goldilocks(op.s_shift),
            p.s_claim,
            &pt_s,
            &p.s_fold_roots,
            &op.s_fold_steps,
        ) {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "S butterfly fold walk failed",
            });
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// 5. Streaming Chain Serialization, Verifiers & ProveService Backend
// ---------------------------------------------------------------------------

pub fn fold_chunk_roots(commits: &[[u8; 32]]) -> [u8; 32] {
    let mut pre = Vec::with_capacity(8 + commits.len() * 32);
    pre.extend_from_slice(&(commits.len() as u64).to_be_bytes());
    for c in commits {
        pre.extend_from_slice(c);
    }
    sha256(&pre)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingChunkInput {
    pub chunk_idx: u64,
    pub state_in_commit: [u8; 32],
    pub state_out_commit: [u8; 32],
    pub witness: Mxfp4ChunkWitness,
}

impl StreamingChunkInput {
    pub fn from_witness(chunk_idx: u64, witness: Mxfp4ChunkWitness) -> Self {
        Self {
            chunk_idx,
            state_in_commit: witness.state_in_commit(),
            state_out_commit: witness.state_out_commit(),
            witness,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingZkmlJob {
    pub request_id: [u8; 32],
    pub model_id: String,
    pub model_weights_root: [u8; 32],
    pub policy_floor_digest: [u8; 32],
    pub suite: ZkmlSuiteArtifact,
    pub requested_regime: SecurityRegime,
    pub pinned_num_queries: Option<u32>,
    pub initial_state_commit: [u8; 32],
    pub chunks: Vec<StreamingChunkInput>,
    pub grind_threads: usize,
    pub grind_span: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateComputation {
    pub request_id: [u8; 32],
    pub model_id: String,
    pub model_weights_root: [u8; 32],
    pub policy_floor_digest: [u8; 32],
    pub initial_state_commit: [u8; 32],
    pub final_state_commit: [u8; 32],
    pub canonical_input_root: [u8; 32],
    pub canonical_output_root: [u8; 32],
    pub suite_id: String,
    pub suite_digest: [u8; 32],
    pub checker_id: String,
    pub pinned_num_queries: Option<u32>,
    pub soundness_report: ZkmlSoundnessReport,
    pub chunk_receipts: Vec<ZkmlChunkReceipt>,
    pub proof_bytes: Vec<u8>,
}

impl CandidateComputation {
    /// Domain-separated `OBEND.SHE.ZKML_CANDIDATE/v1` `cSHAKE256` statement digest binding the outer
    /// `ZkmlSuiteArtifact::suite_digest()` (including `suite_id`, `checker_id`, and `checker_content_digest`)
    /// together with `request_id`, `model_weights_root`, `policy_floor_digest`, boundary state commitments,
    /// folded I/O roots, `pinned_num_queries`, and every chunk receipt's `OBEND.SHE.ZKML_CHUNK/v1` commitment.
    pub fn outer_statement_digest(&self) -> [u8; 32] {
        let pin_tag = match self.pinned_num_queries {
            Some(q) => {
                let mut v = vec![0x01u8];
                encode_leb128(q as u64, &mut v);
                v
            }
            None => vec![0x00u8],
        };
        let commits: Vec<&[u8]> = self
            .chunk_receipts
            .iter()
            .map(|r| r.chunk_commitment.as_slice())
            .collect();
        let commits_enc = encode_zkml_fields(&commits);
        let pre = encode_zkml_fields(&[
            &self.request_id,
            self.model_id.as_bytes(),
            &self.model_weights_root,
            &self.policy_floor_digest,
            &self.initial_state_commit,
            &self.final_state_commit,
            &self.canonical_input_root,
            &self.canonical_output_root,
            self.suite_id.as_bytes(),
            &self.suite_digest,
            self.checker_id.as_bytes(),
            &pin_tag,
            &commits_enc,
        ]);
        cshake256_32(ZKML_CANDIDATE_DOMAIN_TAG, &pre)
    }
}

pub fn encode_chunk_chain_bytes(receipts: &[ZkmlChunkReceipt]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + receipts.len() * 1024);
    out.extend_from_slice(&(receipts.len() as u64).to_be_bytes());
    for receipt in receipts {
        receipt.encode_bytes(&mut out);
    }
    out
}

pub fn decode_chunk_chain_bytes(bytes: &[u8]) -> Result<Vec<ZkmlChunkReceipt>, ZkmlGateRefusal> {
    if bytes.len() < 8 {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "proof_bytes shorter than 8-byte chunk count header",
        });
    }
    let count = u64::from_be_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ]);
    let count_usize =
        usize::try_from(count).map_err(|_| ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "chunk count overflows usize",
        })?;
    if count_usize > MAX_ZKML_MODEL_LAYERS {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "chunk count exceeds MAX_ZKML_MODEL_LAYERS (1024)",
        });
    }
    let remaining = bytes.len() - 8;
    if count_usize > remaining / SERIALIZED_CHUNK_RECEIPT_BYTES {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "chunk count exceeds remaining payload capacity",
        });
    }
    let mut cursor = 8usize;
    let mut receipts = Vec::with_capacity(count_usize);
    for _ in 0..count_usize {
        let rec_bytes = read_framed_field(bytes, &mut cursor)?;
        receipts.push(ZkmlChunkReceipt::decode_bytes(rec_bytes)?);
    }
    if cursor != bytes.len() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "trailing garbage after chunk receipt chain",
        });
    }
    Ok(receipts)
}

/// Bounded `O(q log^2 N)` structural validation of all proof vectors inside a typed
/// [`ZkmlChunkReceipt`] BEFORE [`ZkmlChunkReceipt::recompute_commitment`] serializes or hashes
/// (`model.valid()` is checked once at chain entry to avoid `O(L^2)` manifest walks).
fn check_chunk_iop_bounded_shape_prevalidated(
    profile: &ZkmlSuiteProfile,
    model: &Mxfp4ModelManifest,
    receipt: &ZkmlChunkReceipt,
) -> Result<(), ZkmlGateRefusal> {
    let idx = receipt.chunk_idx;
    if profile.num_queries == 0
        || (profile.num_queries as usize) > MAX_ZKML_NUM_QUERIES
        || profile.log_arity == 0
    {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "invalid suite query/arity bounds",
        });
    }
    let layer_usize =
        usize::try_from(receipt.layer_idx).map_err(|_| ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "layer_idx overflows usize",
        })?;
    let lk = model
        .layers
        .get(layer_usize)
        .ok_or(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "layer_idx out of bounds in Mxfp4ModelManifest",
        })?;
    let p = &receipt.iop_proof;
    if lk.log_i != p.log_i
        || lk.log_j != p.log_j
        || lk.log_k != p.log_k
        || lk.log_b != p.log_b
        || lk.q_merkle_root != receipt.q_merkle_root
        || lk.s_merkle_root != receipt.s_merkle_root
    {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "chunk proof layer dimensions or Q/S roots disagree with manifest",
        });
    }
    let v_d = p.log_i + p.log_j;
    let v_x = p.log_i + p.log_b + p.log_k;
    let v_q = p.log_b + p.log_k + p.log_j;
    let v_s = p.log_k + p.log_j;
    if p.sumcheck_rounds.len() != v_q
        || p.sumcheck_rounds.iter().any(|r| r.coeffs.len() > 4)
        || p.d_fold_roots.len() != v_d
        || p.x_fold_roots.len() != v_x
        || p.q_fold_roots.len() != v_q
        || p.s_fold_roots.len() != v_s
        || p.query_openings.len() != profile.num_queries as usize
    {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: idx,
            reason: "chunk proof vector length exceeds protocol dimension bounds",
        });
    }
    let check_steps = |steps: &[FoldLayerStep], v: usize| -> bool {
        steps.len() == v
            && steps
                .iter()
                .all(|st| st.merkle_path.len() <= MAX_ZKML_HYPERCUBE_VARS)
    };
    for op in &p.query_openings {
        if op.d_path.len() != v_d
            || op.x_path.len() != v_x
            || op.q_path.len() != v_q
            || op.s_path.len() != v_s
            || !check_steps(&op.d_fold_steps, v_d)
            || !check_steps(&op.x_fold_steps, v_x)
            || !check_steps(&op.q_fold_steps, v_q)
            || !check_steps(&op.s_fold_steps, v_s)
        {
            return Err(ZkmlGateRefusal::InvalidChunkIopProof {
                chunk_idx: idx,
                reason: "query opening path or fold_steps length mismatch",
            });
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn verify_zkml_chunk_chain(
    profile: &ZkmlSuiteProfile,
    expected_model: &Mxfp4ModelManifest,
    receipts: &[ZkmlChunkReceipt],
    expected_weights_root: &[u8; 32],
    expected_policy_floor_digest: &[u8; 32],
    expected_suite_digest: &[u8; 32],
    initial_state_commit: &[u8; 32],
    required_grind_bits: u32,
    pinned_num_queries: Option<u32>,
) -> Result<[u8; 32], ZkmlGateRefusal> {
    if pinned_num_queries != Some(profile.num_queries) {
        return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
            reason: "pinned_num_queries missing or mismatches suite profile.num_queries",
        });
    }
    let canonical_profile_digest = profile.profile_digest();
    if *expected_suite_digest != canonical_profile_digest {
        return Err(ZkmlGateRefusal::SuiteDigestMismatch {
            chunk_idx: None,
            expected: canonical_profile_digest,
            actual: *expected_suite_digest,
        });
    }
    if receipts.is_empty() {
        return Err(ZkmlGateRefusal::EmptyChunkChain);
    }
    if !expected_model.valid() {
        return Err(ZkmlGateRefusal::InvalidChunkIopProof {
            chunk_idx: 0,
            reason: "invalid Mxfp4ModelManifest",
        });
    }
    if receipts.len() != expected_model.layers.len() {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "chunk receipt chain length must equal Mxfp4ModelManifest layer count",
        });
    }
    let actual_model_root = expected_model.root();
    if actual_model_root != *expected_weights_root {
        return Err(ZkmlGateRefusal::WeightRootMismatch {
            chunk_idx: None,
            expected: *expected_weights_root,
            actual: actual_model_root,
        });
    }

    let mut expected_state_in = *initial_state_commit;
    for (idx, receipt) in receipts.iter().enumerate() {
        let expected_idx = idx as u64;
        if receipt.chunk_idx != expected_idx {
            return Err(ZkmlGateRefusal::ChunkIndexMismatch {
                expected: expected_idx,
                actual: receipt.chunk_idx,
            });
        }
        if receipt.layer_idx != expected_idx {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "chunk layer_idx must follow sequential manifest layer order 0..L",
            });
        }
        if receipt.model_weights_root != *expected_weights_root {
            return Err(ZkmlGateRefusal::WeightRootMismatch {
                chunk_idx: Some(expected_idx),
                expected: *expected_weights_root,
                actual: receipt.model_weights_root,
            });
        }
        if receipt.policy_floor_digest != *expected_policy_floor_digest {
            return Err(ZkmlGateRefusal::PolicyFloorMismatch {
                chunk_idx: Some(expected_idx),
                expected: *expected_policy_floor_digest,
                actual: receipt.policy_floor_digest,
            });
        }
        if receipt.suite_digest != *expected_suite_digest {
            return Err(ZkmlGateRefusal::SuiteDigestMismatch {
                chunk_idx: Some(expected_idx),
                expected: *expected_suite_digest,
                actual: receipt.suite_digest,
            });
        }
        if receipt.state_in_commit != expected_state_in {
            return Err(ZkmlGateRefusal::BrokenChunkCarry {
                chunk_idx: expected_idx,
                expected_state_in,
                actual_state_in: receipt.state_in_commit,
            });
        }

        check_chunk_iop_bounded_shape_prevalidated(profile, expected_model, receipt)?;

        let recomputed = receipt.recompute_commitment();
        if receipt.chunk_commitment != recomputed {
            return Err(ZkmlGateRefusal::ChunkCommitmentMismatch {
                chunk_idx: expected_idx,
                expected: recomputed,
                actual: receipt.chunk_commitment,
            });
        }

        verify_mxfp4_chunk_iop_prevalidated(
            profile,
            expected_model,
            &actual_model_root,
            required_grind_bits,
            receipt,
        )?;
        expected_state_in = receipt.state_out_commit;
    }

    Ok(expected_state_in)
}

/// Fail-closed end-to-end verification of a [`CandidateComputation`]:
/// 1. Evaluates the configured `UD-100` (`ProvenUdr100`) suite-parameter floor on
///    `expected_suite` (returning the suite-parameter [`ZkmlSoundnessReport`]);
/// 2. Checks outer [`CandidateComputation`] metadata equality (`suite_id`, `checker_id`, and
///    `expected_suite.suite_digest()`) against the caller's pinned `expected_suite` (outer metadata
///    check; use [`CandidateComputation::outer_statement_digest`] when signing/binding the outer
///    artifact provenance and chunk commitment chain together), while the chunk PIOP transcripts and
///    `OBEND.SHE.ZKML_CHUNK/v1` receipts cryptographically authenticate the canonical 8-field
///    `OBEND.SHE.ZKML_SUITE/v1` `profile_digest()` (matching Lean `ValidZkmlChunkChainSpec`);
/// 3. Executes the base-field `Goldilocks` `(2^logB, 3^logK, 3^logJ)` `EinSumcheck` + rate-1
///    uncoded binary `OBEND.SHE.ZKML_MERKLE/v1` fold-walk chunk PIOP across all `0..L` model layers.
#[allow(clippy::too_many_arguments)]
pub fn verify_candidate_computation(
    candidate: &CandidateComputation,
    expected_request_id: &[u8; 32],
    expected_initial_state_commit: &[u8; 32],
    expected_model: &Mxfp4ModelManifest,
    expected_weights_root: &[u8; 32],
    expected_policy_floor_digest: &[u8; 32],
    expected_suite: &ZkmlSuiteArtifact,
    requested_regime: SecurityRegime,
) -> Result<ZkmlSoundnessReport, ZkmlGateRefusal> {
    let report = expected_suite.check_proven_floor(requested_regime)?;
    if requested_regime != SecurityRegime::ProvenUdr100 {
        return Err(ZkmlGateRefusal::InsufficientProvenBits {
            regime: requested_regime,
            achieved_milli_bits: expected_suite.profile.udr_milli_bits(),
            required_milli_bits: PROVEN_MIN_MILLI_BITS,
        });
    }

    if candidate.request_id != *expected_request_id {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "request_id mismatch",
        });
    }
    if candidate.initial_state_commit != *expected_initial_state_commit {
        return Err(ZkmlGateRefusal::BrokenChunkCarry {
            chunk_idx: 0,
            expected_state_in: *expected_initial_state_commit,
            actual_state_in: candidate.initial_state_commit,
        });
    }
    if candidate.model_weights_root != *expected_weights_root {
        return Err(ZkmlGateRefusal::WeightRootMismatch {
            chunk_idx: None,
            expected: *expected_weights_root,
            actual: candidate.model_weights_root,
        });
    }
    if candidate.policy_floor_digest != *expected_policy_floor_digest {
        return Err(ZkmlGateRefusal::PolicyFloorMismatch {
            chunk_idx: None,
            expected: *expected_policy_floor_digest,
            actual: candidate.policy_floor_digest,
        });
    }

    let expected_suite_digest = expected_suite.suite_digest();
    if candidate.suite_digest != expected_suite_digest
        || candidate.suite_id != expected_suite.suite_id
        || candidate.checker_id != expected_suite.checker_id
    {
        return Err(ZkmlGateRefusal::SuiteDigestMismatch {
            chunk_idx: None,
            expected: expected_suite_digest,
            actual: candidate.suite_digest,
        });
    }

    let decoded = decode_chunk_chain_bytes(&candidate.proof_bytes)?;
    if decoded != candidate.chunk_receipts {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "proof_bytes does not match chunk_receipts",
        });
    }

    let expected_profile_digest = expected_suite.profile.profile_digest();
    let final_state = verify_zkml_chunk_chain(
        &expected_suite.profile,
        expected_model,
        &decoded,
        expected_weights_root,
        expected_policy_floor_digest,
        &expected_profile_digest,
        &candidate.initial_state_commit,
        expected_suite.profile.grind_bits,
        candidate.pinned_num_queries,
    )?;

    if candidate.final_state_commit != final_state {
        return Err(ZkmlGateRefusal::BrokenChunkCarry {
            chunk_idx: decoded.len() as u64,
            expected_state_in: final_state,
            actual_state_in: candidate.final_state_commit,
        });
    }

    let inputs: Vec<[u8; 32]> = decoded.iter().map(|r| r.state_in_commit).collect();
    let outputs: Vec<[u8; 32]> = decoded.iter().map(|r| r.state_out_commit).collect();
    if candidate.canonical_input_root != fold_chunk_roots(&inputs) {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "canonical_input_root mismatch",
        });
    }
    if candidate.canonical_output_root != fold_chunk_roots(&outputs) {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "canonical_output_root mismatch",
        });
    }
    if candidate.soundness_report != report {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "soundness_report does not match recomputed floor gate report",
        });
    }

    Ok(report)
}

#[derive(Clone, Debug)]
pub struct StreamingZkmlBackend {
    pinned_weights_root: Option<[u8; 32]>,
    pinned_policy_floor_digest: Option<[u8; 32]>,
    max_grind_threads: usize,
}

impl Default for StreamingZkmlBackend {
    fn default() -> Self {
        Self {
            pinned_weights_root: None,
            pinned_policy_floor_digest: None,
            max_grind_threads: MAX_ZKML_GRIND_THREADS,
        }
    }
}

impl StreamingZkmlBackend {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn pinned(model_weights_root: [u8; 32], policy_floor_digest: [u8; 32]) -> Self {
        Self {
            pinned_weights_root: Some(model_weights_root),
            pinned_policy_floor_digest: Some(policy_floor_digest),
            max_grind_threads: MAX_ZKML_GRIND_THREADS,
        }
    }

    /// Override the worker-enforced ceiling on per-job PoW grinder threads (`1..=MAX_ZKML_GRIND_THREADS`).
    pub fn with_max_grind_threads(mut self, max_threads: usize) -> Self {
        self.max_grind_threads = max_threads.clamp(1, MAX_ZKML_GRIND_THREADS);
        self
    }

    pub fn prove_job(
        &self,
        job: &StreamingZkmlJob,
        cancel: &CancelToken,
    ) -> Result<CandidateComputation, ZkmlGateRefusal> {
        if cancel.is_cancelled() {
            return Err(ZkmlGateRefusal::Cancelled);
        }

        if let Some(expected_weights) = self.pinned_weights_root {
            if job.model_weights_root != expected_weights {
                return Err(ZkmlGateRefusal::WeightRootMismatch {
                    chunk_idx: None,
                    expected: expected_weights,
                    actual: job.model_weights_root,
                });
            }
        }
        if let Some(expected_policy) = self.pinned_policy_floor_digest {
            if job.policy_floor_digest != expected_policy {
                return Err(ZkmlGateRefusal::PolicyFloorMismatch {
                    chunk_idx: None,
                    expected: expected_policy,
                    actual: job.policy_floor_digest,
                });
            }
        }

        let report = job.suite.check_proven_floor(job.requested_regime)?;
        if job.requested_regime != SecurityRegime::ProvenUdr100 {
            return Err(ZkmlGateRefusal::InsufficientProvenBits {
                regime: job.requested_regime,
                achieved_milli_bits: job.suite.profile.udr_milli_bits(),
                required_milli_bits: PROVEN_MIN_MILLI_BITS,
            });
        }
        if job.pinned_num_queries != Some(job.suite.profile.num_queries) {
            return Err(ZkmlGateRefusal::UnpinnedOrZeroAritySuite {
                reason: "job pinned_num_queries missing or mismatches suite profile.num_queries",
            });
        }
        if job.chunks.is_empty() {
            return Err(ZkmlGateRefusal::EmptyChunkChain);
        }
        let expected_layers = job.chunks[0].witness.model().layers.len();
        if job.chunks.len() != expected_layers {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "job chunk count must equal Mxfp4ModelManifest layer count",
            });
        }

        let mut expected_state_in = job.initial_state_commit;
        for (idx, chunk) in job.chunks.iter().enumerate() {
            let expected_idx = idx as u64;
            if chunk.chunk_idx != expected_idx {
                return Err(ZkmlGateRefusal::ChunkIndexMismatch {
                    expected: expected_idx,
                    actual: chunk.chunk_idx,
                });
            }
            if chunk.witness.layer_idx() != expected_idx {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason:
                        "chunk witness layer_idx must follow sequential manifest layer order 0..L",
                });
            }
            if chunk.state_in_commit != expected_state_in {
                return Err(ZkmlGateRefusal::BrokenChunkCarry {
                    chunk_idx: expected_idx,
                    expected_state_in,
                    actual_state_in: chunk.state_in_commit,
                });
            }
            if chunk.witness.weights_root() != job.model_weights_root {
                return Err(ZkmlGateRefusal::WeightRootMismatch {
                    chunk_idx: Some(expected_idx),
                    expected: job.model_weights_root,
                    actual: chunk.witness.weights_root(),
                });
            }
            if chunk.witness.state_in_commit() != chunk.state_in_commit
                || chunk.witness.state_out_commit() != chunk.state_out_commit
            {
                return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                    reason: "StreamingChunkInput commitments disagree with Mxfp4ChunkWitness",
                });
            }
            expected_state_in = chunk.state_out_commit;
        }

        let suite_digest = job.suite.suite_digest();
        let profile_digest = job.suite.profile.profile_digest();
        let mut receipts = Vec::with_capacity(job.chunks.len());
        let mut input_commits = Vec::with_capacity(job.chunks.len());
        let mut output_commits = Vec::with_capacity(job.chunks.len());

        let effective_span = if job.grind_span == 0 {
            DEFAULT_ZKML_GRIND_SPAN
        } else {
            job.grind_span
        };
        let effective_threads = job.grind_threads.clamp(1, self.max_grind_threads);
        for chunk in &job.chunks {
            if cancel.is_cancelled() {
                return Err(ZkmlGateRefusal::Cancelled);
            }
            let receipt = prove_mxfp4_chunk_iop(
                &job.suite.profile,
                &job.policy_floor_digest,
                &profile_digest,
                chunk.chunk_idx,
                &chunk.witness,
                effective_span,
                effective_threads,
                cancel,
            )?;
            input_commits.push(receipt.state_in_commit);
            output_commits.push(receipt.state_out_commit);
            receipts.push(receipt);
        }

        let proof_bytes = encode_chunk_chain_bytes(&receipts);
        let final_state_commit = expected_state_in;

        Ok(CandidateComputation {
            request_id: job.request_id,
            model_id: job.model_id.clone(),
            model_weights_root: job.model_weights_root,
            policy_floor_digest: job.policy_floor_digest,
            initial_state_commit: job.initial_state_commit,
            final_state_commit,
            canonical_input_root: fold_chunk_roots(&input_commits),
            canonical_output_root: fold_chunk_roots(&output_commits),
            suite_id: job.suite.suite_id.clone(),
            suite_digest,
            checker_id: job.suite.checker_id.clone(),
            pinned_num_queries: job.pinned_num_queries,
            soundness_report: report,
            chunk_receipts: receipts,
            proof_bytes,
        })
    }

    pub fn into_cancellable_backend(
        self,
    ) -> CancellableBackend<StreamingZkmlJob, CandidateComputation> {
        Arc::new(move |job: StreamingZkmlJob, cancel: &CancelToken| {
            self.prove_job(&job, cancel).map_err(|err| err.to_string())
        })
    }
}

pub fn spawn_streaming_zkml_service(
    backend: StreamingZkmlBackend,
    config: ProveServiceConfig,
) -> ProveService<StreamingZkmlJob, CandidateComputation> {
    ProveService::spawn_cancellable(backend.into_cancellable_backend(), config)
}

#[cfg(test)]
mod nonce_absorber_tests {
    use super::*;

    struct SplitMix(u64);

    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn digest(&mut self) -> [u8; 32] {
            let mut out = [0u8; 32];
            for chunk in out.as_chunks_mut::<8>().0 {
                *chunk = self.next().to_le_bytes();
            }
            out
        }

        /// A step count whose LEB128 width varies across the whole `u64` range.
        fn step_count(&mut self) -> u64 {
            let shift = self.next() % 64;
            self.next() >> shift
        }
    }

    fn transcript_lanes(state: &[u8; 32], step_count: u64, label: &[u8], nonce: u64) -> [u64; 4] {
        let mut tr = FsTranscript {
            state: *state,
            step_count,
        };
        tr.absorb_msg(label, &nonce.to_be_bytes());
        digest_lanes(&tr.state)
    }

    fn leb_width(value: u64) -> usize {
        leb128_vec(value).len()
    }

    #[test]
    fn grind_absorber_matches_absorb_msg_on_random_tuples() {
        let mut rng = SplitMix(0x5eed);
        for _ in 0..10_000 {
            let state = rng.digest();
            let step_count = rng.step_count();
            let nonce = rng.next();
            let absorber = NonceAbsorber::new(&state, step_count, ZKML_POW_NONCE_LABEL);
            assert!(matches!(absorber, NonceAbsorber::OneBlock { .. }));
            assert_eq!(
                absorber.digest_lanes(nonce),
                transcript_lanes(&state, step_count, ZKML_POW_NONCE_LABEL, nonce)
            );
        }
    }

    #[test]
    fn grind_absorber_covers_every_nonce_alignment_and_the_block_boundary() {
        let mut rng = SplitMix(0xa119);
        let mut shifts_seen = [false; 8];
        let (mut at_135, mut at_136) = (false, false);
        for label_len in 0..=110usize {
            let label = vec![0xa5u8; label_len];
            for width in 1..=10u32 {
                let step_count = 1u64 << (7 * (width - 1));
                assert_eq!(leb_width(step_count), width as usize);
                let frame_len =
                    1 + 32 + leb_width(label_len as u64) + label_len + 1 + width as usize + 8;
                let state = rng.digest();
                let nonce = rng.next();
                let absorber = NonceAbsorber::new(&state, step_count, &label);
                match &absorber {
                    NonceAbsorber::OneBlock { shift, .. } => {
                        assert!(frame_len <= 135);
                        shifts_seen[(*shift / 8) as usize] = true;
                    }
                    NonceAbsorber::General { .. } => assert!(frame_len >= 136),
                }
                at_135 |= frame_len == 135;
                at_136 |= frame_len == 136;
                assert_eq!(
                    absorber.digest_lanes(nonce),
                    transcript_lanes(&state, step_count, &label, nonce)
                );
            }
        }
        assert!(at_135 && at_136 && shifts_seen.iter().all(|&seen| seen));
    }

    #[test]
    fn grind_absorber_covers_leb128_endpoints() {
        let state = [0xff; 32];
        let mut steps = vec![0, u64::MAX];
        for shift in (7..64).step_by(7) {
            steps.extend([(1u64 << shift) - 1, 1u64 << shift]);
        }
        for step in steps {
            for label in [ZKML_POW_NONCE_LABEL, &[0x5a; 128], &[0x5a; 272]] {
                let absorber = NonceAbsorber::new(&state, step, label);
                let tr = FsTranscript {
                    state,
                    step_count: step,
                };
                for nonce in [0u64, 0x0123_4567_89ab_cdef, u64::MAX] {
                    assert_eq!(
                        absorber.digest_lanes(nonce),
                        digest_lanes(&tr.absorbed_state(label, &nonce.to_be_bytes()))
                    );
                }
            }
        }
    }

    #[test]
    fn grind_padding_combines_domain_and_final_bit_in_last_byte() {
        let mut sponge = Cshake256::customized(FS_ABSORB_TAG);
        sponge.absorb(&[0xa5; SHAKE256_RATE_BYTES - 1]);
        let mut expected = *sponge.lanes();
        expected[16] ^= 0x84 << 56;
        assert_eq!(sponge.padded_lanes(), expected);
    }

    #[test]
    fn grind_word_absorb_matches_bytewise_absorb_across_splits() {
        let mut rng = SplitMix(0xb10c);
        for _ in 0..2_000 {
            let len = (rng.next() % 500) as usize;
            let msg: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
            let mut bytewise = Cshake256::customized(FS_ABSORB_TAG);
            for &b in &msg {
                bytewise.absorb(&[b]);
            }
            let mut split = Cshake256::customized(FS_ABSORB_TAG);
            let mut rest = msg.as_slice();
            while !rest.is_empty() {
                let take = 1 + (rng.next() as usize) % rest.len().min(150);
                let (head, tail) = rest.split_at(take);
                split.absorb(head);
                rest = tail;
            }
            assert_eq!(split.finalize_32(), bytewise.finalize_32());
        }
    }

    #[test]
    fn grind_returns_the_lowest_nonce_of_a_direct_scan() {
        let mut rng = SplitMix(0x90d);
        for (bits, rounds) in [(1u32, 6), (4, 6), (8, 6), (12, 4), (16, 2)] {
            for _ in 0..rounds {
                let state = rng.digest();
                let step_count = rng.step_count();
                let direct = (0..1u64 << 22)
                    .find(|&nonce| {
                        let mut tr = FsTranscript { state, step_count };
                        tr.absorb_msg(ZKML_POW_NONCE_LABEL, &nonce.to_be_bytes());
                        digest_has_low_zero_bits(&tr.state, bits)
                    })
                    .expect("a witness below 2^22");
                for threads in [1, 4] {
                    let cancel = CancelToken::new();
                    assert_eq!(
                        grind_zkml_chunk_pow(&state, step_count, bits, 1 << 22, threads, &cancel),
                        Some(direct)
                    );
                }
            }
        }
    }

    #[test]
    fn grind_low_bit_predicate_boundaries() {
        assert!(low_bits_zero(u64::MAX, 0));
        assert!(low_bits_zero(0, 64));
        assert!(!low_bits_zero(1 << 63, 64));
        assert!(!low_bits_zero(0, 65));
        for k in 0..64u32 {
            let sample = 1u64 << k;
            assert!(low_bits_zero(sample, k));
            assert!(!low_bits_zero(sample, k + 1));
        }
    }
}
