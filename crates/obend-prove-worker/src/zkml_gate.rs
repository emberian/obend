#![forbid(unsafe_code)]
//! Unconditional `UDR`/`JBR` zkML soundness floor gate and streaming recurrent Gated-DeltaNet /
//! SSM chunk-carry `ProveService` backend.
//!
//! Closes *Rainbows End* SHE Gap #4 in pure-`std` Rust (`#![forbid(unsafe_code)]`, zero external
//! dependencies), aligned byte-for-byte with `Obend.SymbolicZk.ProvenZkmlGate`:
//!
//! 1. **Unconditional Soundness Accounting (`ZkmlSuiteProfile`, `SecurityRegime`)**:
//!    - Computes exact integer milli-bit (`1_000` = `1.000` bit) soundness under:
//!      - Unconditional Unique-Decoding Regime (`udr_milli_bits`),
//!      - Proven Johnson-Bound Regime (`jbr_milli_bits`),
//!      - Legacy Withdrawn Capacity-Bound Regime (`legacy_withdrawn_cbr_milli_bits`, unconditionally
//!        refused by [`ZkmlSuiteProfile::check_proven_floor`]),
//!      - Extension-field LogUp ceiling (`logup_ext_ceiling_milli_bits`), and
//!      - BCS Merkle digest birthday ceiling (`bcs_digest_ceiling_milli_bits`).
//!    - Refuses any suite relying on [`SecurityRegime::WithdrawnCapacityBound`] or scoring
//!      `< 100_000` milli-bits (`100` bits) in the requested proven regime. In particular, the
//!      legacy deployed BabyBear Ext4 `(lb=6, q=19, pow=16)` profile (`34_563` milli-bits UDR,
//!      `73_000` JBR, `130_000` withdrawn CBR) is refused, while `(lb=6, q=86, pow=16)` (`100_022`
//!      milli-bits UDR) and proven `Ext5` profiles pass.
//! 2. **Byte-Exact `OBEND.SHE.ZKML_CHUNK/v1` `cSHAKE256` Chunk Commitments**:
//!    - Pure-Rust NIST FIPS 202 / SP 800-185 `cSHAKE256` (`N = ""`, `S = "OBEND.SHE.ZKML_CHUNK/v1"`,
//!      32-byte output) over self-delimiting LEB128-length-framed fields (`encodeListField`),
//!      matching `Obend.Digest.Cshake256.cshake256Bytes` and `Obend.SymbolicZk.ProvenZkmlGate`.
//! 3. **Streaming Recurrent GDN / SSM Chunk-Carry `ProveService` Backend (`StreamingZkmlBackend`)**:
//!    - Wires [`CancellableBackend`] onto [`ProveService`] and deterministic `c = 1/4`
//!      [`windowed_find_map_first_cancellable`] PoW grinding so `1T == NT` produces bit-identical
//!      [`CandidateComputation`] receipts with verified recurrent carry
//!      (`state_out_commit[i] == state_in_commit[i+1]`), pinned `model_weights_root` and
//!      `policy_floor_digest`, and prompt cooperative epoch cancellation.
//!    - Per `CROSS_REPO_CONTRACTS.md`, native execution emits candidate bytes and receipts only;
//!      all verification fails closed via [`verify_candidate_computation`].

use std::fmt;
use std::sync::Arc;

use crate::grinder::{
    default_grind_window, sha256, windowed_find_map_first_cancellable,
};
use crate::service::{CancelToken, CancellableBackend, ProveService, ProveServiceConfig};

// ---------------------------------------------------------------------------
// Constants & Domain Tags
// ---------------------------------------------------------------------------

/// Canonical SP 800-185 `cSHAKE256` customization tag for zkML streaming chunk commitments.
/// Must stay byte-identical to `Obend.SymbolicZk.ProvenZkmlGate`.
pub const ZKML_CHUNK_DOMAIN_TAG: &[u8] = b"OBEND.SHE.ZKML_CHUNK/v1";

/// Minimum required unconditional soundness floor in milli-bits (`100_000` = `100.000` bits).
pub const PROVEN_MIN_MILLI_BITS: u64 = 100_000;

/// Milli-bits per whole bit.
pub const MILLI_BITS_PER_BIT: u64 = 1_000;

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

/// Serialized byte width of one [`ZkmlChunkReceipt`] inside `CandidateComputation::proof_bytes`.
/// `8 * 32` (roots/commitments + `chunk_commitment`) + `2 * 8` (`chunk_idx`, `pow_nonce`) = `272` bytes.
pub const SERIALIZED_CHUNK_RECEIPT_BYTES: usize = 272;

/// Pre-computed integer floor of `1000 * (1 - log2(1 + 2^(-lb)))` for `lb = 0..=11`.
/// For all `lb >= 12`, `floor(1000 * (1 - log2(1 + 2^(-lb)))) = 999`.
///
/// Crucially, for every `lb >= 1`:
/// `udr_query_milli_bits(lb) <= 999 < lb * 500` (for `lb >= 2`, and `415 < 500` for `lb == 1`)
/// `< lb * 1000` (`legacy_withdrawn_cbr`).
const UDR_QUERY_MILLI_BITS_TABLE: [u64; 12] = [
    0,   // lb = 0 (rho = 1)
    415, // lb = 1 (rho = 1/2):   1 - log2(3/2)   = 0.415037...
    678, // lb = 2 (rho = 1/4):   1 - log2(5/4)   = 0.678071...
    830, // lb = 3 (rho = 1/8):   1 - log2(9/8)   = 0.830075...
    912, // lb = 4 (rho = 1/16):  1 - log2(17/16) = 0.912537...
    955, // lb = 5 (rho = 1/32):  1 - log2(33/32) = 0.955605...
    977, // lb = 6 (rho = 1/64):  1 - log2(65/64) = 0.977632...
    988, // lb = 7 (rho = 1/128): 1 - log2(129/128) = 0.988772...
    994, // lb = 8 (rho = 1/256): 1 - log2(257/256) = 0.994375...
    997, // lb = 9 (rho = 1/512)
    998, // lb = 10 (rho = 1/1024)
    999, // lb = 11 (rho = 1/2048)
];

// ---------------------------------------------------------------------------
// Pure-Std NIST FIPS 202 / SP 800-185 cSHAKE256 + LEB128 Framing
// ---------------------------------------------------------------------------

const KECCAK_RATE_BYTES: usize = 136;

const KECCAK_RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

const KECCAK_ROT: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

fn keccak_f1600(state: &mut [u64; 25]) {
    for &rc in &KECCAK_RC {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                state[x + 5 * y] ^= d;
            }
        }
        let mut b = [0u64; 25];
        for y in 0..5 {
            for x in 0..5 {
                let idx = x + 5 * y;
                b[y + 5 * ((2 * x + 3 * y) % 5)] = state[idx].rotate_left(KECCAK_ROT[idx]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }
        state[0] ^= rc;
    }
}

fn left_encode(value: u64, out: &mut [u8; 9]) -> usize {
    let n = ((64 - value.leading_zeros()).max(1) as usize).div_ceil(8);
    out[0] = n as u8;
    for i in 0..n {
        out[i + 1] = (value >> (8 * (n - i - 1))) as u8;
    }
    n + 1
}

#[derive(Clone)]
struct CshakeSponge {
    lanes: [u64; 25],
    pos: usize,
    suffix: u8,
}

impl CshakeSponge {
    fn new(customization: &[u8]) -> Self {
        let mut s = Self {
            lanes: [0u64; 25],
            pos: 0,
            suffix: if customization.is_empty() { 0x1f } else { 0x04 },
        };
        if !customization.is_empty() {
            s.absorb_left_encode(KECCAK_RATE_BYTES as u64);
            s.absorb_encode_string(&[]);
            s.absorb_encode_string(customization);
            while s.pos != 0 {
                s.absorb(&[0]);
            }
        }
        s
    }

    fn absorb(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.lanes[self.pos / 8] ^= (b as u64) << (8 * (self.pos % 8));
            self.pos += 1;
            if self.pos == KECCAK_RATE_BYTES {
                keccak_f1600(&mut self.lanes);
                self.pos = 0;
            }
        }
    }

    fn absorb_left_encode(&mut self, value: u64) {
        let mut buf = [0u8; 9];
        let len = left_encode(value, &mut buf);
        self.absorb(&buf[..len]);
    }

    fn absorb_encode_string(&mut self, bytes: &[u8]) {
        let bit_len = u64::try_from(bytes.len())
            .expect("slice length fits u64")
            .checked_mul(8)
            .expect("bit length fits u64");
        self.absorb_left_encode(bit_len);
        self.absorb(bytes);
    }

    fn finalize_32(mut self) -> [u8; 32] {
        self.lanes[self.pos / 8] ^= (self.suffix as u64) << (8 * (self.pos % 8));
        self.lanes[(KECCAK_RATE_BYTES - 1) / 8] ^=
            0x80u64 << (8 * ((KECCAK_RATE_BYTES - 1) % 8));
        keccak_f1600(&mut self.lanes);

        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = (self.lanes[i / 8] >> (8 * (i % 8))) as u8;
        }
        out
    }
}

/// Computes SP 800-185 `cSHAKE256` with empty function-name `N = ""`, customization `S`, and
/// 32-byte output, matching `Obend.Digest.Cshake256.cshake256Bytes` byte-for-byte.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut sponge = CshakeSponge::new(customization);
    sponge.absorb(input);
    sponge.finalize_32()
}

/// Appends canonical unsigned LEB128 encoding of `value`, matching `Obend.Crypto.leb128`.
pub fn encode_leb128(mut value: u64, out: &mut Vec<u8>) {
    loop {
        if value < 128 {
            out.push(value as u8);
            break;
        }
        out.push(((value & 0x7f) as u8) | 0x80);
        value >>= 7;
    }
}

/// Appends one self-delimiting LEB128 length-prefixed field (`leb128(field.len()) || field`),
/// matching `Obend.Crypto.encodeListField` and `Obend.Polis.SandboxDomainTags.encodeSandboxFields`.
pub fn push_framed_field(out: &mut Vec<u8>, field: &[u8]) {
    encode_leb128(field.len() as u64, out);
    out.extend_from_slice(field);
}

/// Checks whether the first `bits` low bits (little-endian in `digest[0..8]`) of `digest` are zero.
#[inline]
pub fn digest_has_low_zero_bits(digest: &[u8; 32], bits: u32) -> bool {
    if bits == 0 {
        return true;
    }
    if bits > 64 {
        return false;
    }
    let sample = u64::from_le_bytes([
        digest[0], digest[1], digest[2], digest[3], digest[4], digest[5], digest[6], digest[7],
    ]);
    if bits == 64 {
        sample == 0
    } else {
        (sample & ((1u64 << bits) - 1)) == 0
    }
}

// ---------------------------------------------------------------------------
// 1. Unconditional UDR / JBR vs. Withdrawn CBR Soundness Gate
// ---------------------------------------------------------------------------

/// Soundness regime requested for a zkML proof suite.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SecurityRegime {
    /// Unconditional Unique-Decoding Regime (`delta = (1 - rho) / 2`), requiring `>= 100` bits.
    ProvenUdr100,
    /// Proven Johnson-Bound Regime (`delta = 1 - sqrt(rho)`), requiring `>= 100` bits.
    ProvenJbr100,
    /// Legacy Withdrawn Capacity-Bound Regime (`log_blowup * num_queries + grind_bits`).
    /// Unconditionally refused by [`ZkmlSuiteProfile::check_proven_floor`].
    WithdrawnCapacityBound,
}

/// Protocol mode recorded in [`ZkmlSuiteArtifact`] (per `CROSS_REPO_CONTRACTS.md`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ZkmlProtocolMode {
    /// IR-v2 FRI (e.g., `dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1`).
    IrV2Fri,
    /// BaseFold / Reed-Solomon IOP.
    BaseFoldRs,
}

impl ZkmlProtocolMode {
    #[inline]
    const fn tag_byte(self) -> u8 {
        match self {
            ZkmlProtocolMode::IrV2Fri => 1,
            ZkmlProtocolMode::BaseFoldRs => 2,
        }
    }
}

/// Soundness-relevant parameters of a zkML STARK / FRI / BaseFold suite.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZkmlSuiteProfile {
    /// Base prime field bit width (e.g., `31` for BabyBear / KoalaBear).
    pub field_modulus_bits: u32,
    /// Challenge extension field degree (e.g., `4` for Ext4, `5` for Ext5).
    pub ext_degree: u32,
    /// Base-2 logarithm of FRI / RS blowup factor (`rho = 2^(-log_blowup)`).
    pub log_blowup: u32,
    /// Number of pinned FRI / BaseFold queries.
    pub num_queries: u32,
    /// Query-phase proof-of-work grinding bits (`pow`, additive and regime-free).
    pub grind_bits: u32,
    /// Base-2 logarithm of the execution trace height (`|H| = 2^log_trace_height`).
    pub log_trace_height: u32,
    /// BCS Merkle hash digest width in bits (e.g., `256` for cSHAKE256 / SHA-256).
    pub digest_bits: u32,
}

/// Certified soundness breakdown emitted when [`ZkmlSuiteProfile::check_proven_floor`] succeeds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkmlSoundnessReport {
    /// Proven regime that admitted this suite (`ProvenUdr100` or `ProvenJbr100`).
    pub regime: SecurityRegime,
    /// Query + grind soundness in the requested proven regime (milli-bits).
    pub regime_query_grind_milli_bits: u64,
    /// Unconditional Unique-Decoding Regime query + grind soundness (milli-bits).
    pub udr_milli_bits: u64,
    /// Proven Johnson-Bound Regime query + grind soundness (milli-bits).
    pub jbr_milli_bits: u64,
    /// Legacy withdrawn CBR diagnostic value (never used for admission).
    pub legacy_withdrawn_cbr_milli_bits: u64,
    /// Extension-field LogUp ceiling `(field_modulus_bits * ext_degree - log_trace_height) * 1000`.
    pub logup_ext_ceiling_milli_bits: u64,
    /// BCS Merkle digest birthday ceiling `(digest_bits / 2) * 1000`.
    pub bcs_digest_ceiling_milli_bits: u64,
    /// Effective composite proven soundness:
    /// `min(regime_query_grind_milli_bits, logup_ext_ceiling_milli_bits, bcs_digest_ceiling_milli_bits)`.
    pub effective_proven_milli_bits: u64,
}

/// Fail-closed refusal reasons for the zkML soundness gate and streaming chunk-carry verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkmlGateRefusal {
    /// Refused any suite requesting [`SecurityRegime::WithdrawnCapacityBound`].
    WithdrawnCbrRegime {
        legacy_cbr_milli_bits: u64,
        udr_milli_bits: u64,
    },
    /// Refused any suite whose proven query+grind or BCS digest soundness falls below `100_000`
    /// milli-bits (`100` bits).
    InsufficientProvenBits {
        regime: SecurityRegime,
        achieved_milli_bits: u64,
        required_milli_bits: u64,
    },
    /// Refused any suite whose extension-field LogUp ceiling falls below `100_000` milli-bits
    /// (e.g., BabyBear Ext4 at high trace heights where Ext5 is required).
    LogUpExtensionWall {
        ext_degree: u32,
        field_modulus_bits: u32,
        log_trace_height: u32,
        realized_milli_bits: u64,
        required_milli_bits: u64,
    },
    /// Refused a multi-chunk recurrent GDN / SSM sequence whose hidden state carry is broken
    /// (`state_out_commit[i] != state_in_commit[i + 1]` or boundary state mismatch).
    BrokenChunkCarry {
        chunk_idx: u64,
        expected_state_in: [u8; 32],
        actual_state_in: [u8; 32],
    },
    /// Refused a job or chunk receipt whose `model_weights_root` drifted from the pinned root.
    WeightRootMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// Refused a chunk receipt whose `pow_nonce` fails the profile's `grind_bits` requirement or
    /// whose PoW search exhausted its span.
    InvalidChunkPow {
        chunk_idx: u64,
        required_bits: u32,
        pow_nonce: u64,
    },
    /// Refused a job or chunk receipt whose `policy_floor_digest` drifted from the pinned digest.
    PolicyFloorMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// Refused a chunk receipt or candidate whose `suite_digest` does not match the suite artifact.
    SuiteDigestMismatch {
        chunk_idx: Option<u64>,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// Refused a streaming job or candidate with zero chunks.
    EmptyChunkChain,
    /// Refused a chunk receipt whose `chunk_idx` is not strictly contiguous `0..K`.
    ChunkIndexMismatch { expected: u64, actual: u64 },
    /// Refused a chunk receipt whose stored `chunk_commitment` does not match recomputed
    /// `cSHAKE256("OBEND.SHE.ZKML_CHUNK/v1", preimage)`.
    ChunkCommitmentMismatch {
        chunk_idx: u64,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// Refused a candidate whose `request_id`, `canonical_input_root`, `canonical_output_root`, or
    /// serialized `proof_bytes` failed fail-closed verification.
    CandidateBindingMismatch { reason: &'static str },
    /// Streaming proving job was cooperatively cancelled (e.g., via stale-epoch invalidation).
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
                write!(f, "broken recurrent chunk carry at chunk {chunk_idx}")
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

/// Per-query unconditional Unique-Decoding Regime soundness in milli-bits:
/// `floor(1000 * (1 - log2(1 + 2^(-log_blowup))))`.
#[inline]
pub const fn udr_query_milli_bits(log_blowup: u32) -> u64 {
    if (log_blowup as usize) < UDR_QUERY_MILLI_BITS_TABLE.len() {
        UDR_QUERY_MILLI_BITS_TABLE[log_blowup as usize]
    } else {
        999
    }
}

/// Per-query Johnson-Bound Regime soundness in milli-bits: `log_blowup * 500`.
#[inline]
pub const fn jbr_query_milli_bits(log_blowup: u32) -> u64 {
    (log_blowup as u64).saturating_mul(500)
}

/// Per-query legacy withdrawn Capacity-Bound Regime soundness in milli-bits: `log_blowup * 1000`.
#[inline]
pub const fn legacy_cbr_query_milli_bits(log_blowup: u32) -> u64 {
    (log_blowup as u64).saturating_mul(MILLI_BITS_PER_BIT)
}

impl ZkmlSuiteProfile {
    /// Legacy deployed BabyBear Ext4 IR-v2 profile `(lb=6, q=19, pow=16)`:
    /// reads UDR `34_563` mbit (`~34.56` bits), JBR `73_000` mbit, withdrawn CBR `130_000` mbit.
    /// Must be **refused** under `ProvenUdr100`, `ProvenJbr100`, and `WithdrawnCapacityBound`.
    pub const fn deployed_ir2_babybear_ext4_legacy() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 19,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
        }
    }

    /// Unconditional 100-bit UDR BabyBear Ext4 profile `(lb=6, q=86, pow=16)` at `2^20` rows:
    /// UDR `100_022` mbit (`>= 100_000`), LogUp `104_000` mbit, BCS `128_000` mbit.
    pub const fn proven_udr100_babybear_ext4() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
        }
    }

    /// Unconditional 100-bit UDR BabyBear Ext5 profile `(lb=6, q=86, pow=16)` clearing the Ext4
    /// LogUp wall even at `log_trace_height = 25` (`LogUp = 130_000` mbit vs Ext4's `99_000`).
    pub const fn proven_udr100_babybear_ext5() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 5,
            log_blowup: 6,
            num_queries: 86,
            grind_bits: 16,
            log_trace_height: 25,
            digest_bits: 256,
        }
    }

    /// Proven 100-bit JBR BabyBear Ext4 profile `(lb=6, q=28, pow=16)`:
    /// JBR `100_000` mbit (passes `ProvenJbr100`), UDR `43_356` mbit (refused under `ProvenUdr100`).
    pub const fn proven_jbr100_babybear_ext4() -> Self {
        Self {
            field_modulus_bits: BABYBEAR_MODULUS_BITS,
            ext_degree: 4,
            log_blowup: 6,
            num_queries: 28,
            grind_bits: 16,
            log_trace_height: 20,
            digest_bits: 256,
        }
    }

    /// Exact integer milli-bits under the unconditional Unique-Decoding Regime (UDR).
    #[inline]
    pub const fn udr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(udr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    /// Exact integer milli-bits under the proven Johnson-Bound Regime (JBR).
    #[inline]
    pub const fn jbr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(jbr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    /// Exact integer milli-bits under the legacy withdrawn Capacity-Bound Regime (CBR):
    /// `log_blowup * num_queries * 1000 + grind_bits * 1000`.
    /// Diagnostic only — never admitted for security claims.
    #[inline]
    pub const fn legacy_withdrawn_cbr_milli_bits(&self) -> u64 {
        (self.num_queries as u64)
            .saturating_mul(legacy_cbr_query_milli_bits(self.log_blowup))
            .saturating_add((self.grind_bits as u64).saturating_mul(MILLI_BITS_PER_BIT))
    }

    /// Realized extension-field LogUp ceiling in milli-bits:
    /// `saturating_sub(field_modulus_bits * ext_degree, log_trace_height) * 1000`.
    #[inline]
    pub const fn logup_ext_ceiling_milli_bits(&self) -> u64 {
        let ext_bits = (self.field_modulus_bits as u64).saturating_mul(self.ext_degree as u64);
        ext_bits
            .saturating_sub(self.log_trace_height as u64)
            .saturating_mul(MILLI_BITS_PER_BIT)
    }

    /// BCS Merkle digest collision ceiling in milli-bits (`(digest_bits / 2) * 1000`).
    #[inline]
    pub const fn bcs_digest_ceiling_milli_bits(&self) -> u64 {
        ((self.digest_bits / 2) as u64).saturating_mul(MILLI_BITS_PER_BIT)
    }

    /// Evaluates the unconditional `>= 100_000` milli-bit floor gate in `regime`.
    ///
    /// Fails closed on:
    /// 1. [`SecurityRegime::WithdrawnCapacityBound`],
    /// 2. LogUp extension-field wall `< 100_000` milli-bits,
    /// 3. BCS Merkle digest ceiling `< 100_000` milli-bits,
    /// 4. Query + grind soundness in `regime` `< 100_000` milli-bits.
    pub const fn check_proven_floor(
        &self,
        regime: SecurityRegime,
    ) -> Result<ZkmlSoundnessReport, ZkmlGateRefusal> {
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

/// Versioned zkML proof-suite export matching `CROSS_REPO_CONTRACTS.md` §2 (`ZkmlSuiteArtifact`).
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
    /// Builds a canonical BabyBear IR-v2 FRI suite artifact for `profile`.
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
            merkle_arity: 2,
            protocol_mode: ZkmlProtocolMode::IrV2Fri,
            fiat_shamir_alphabet_id: "bcs-cshake256-leb128-v1".to_string(),
            checker_id: "obend.zkml.proven_gate".to_string(),
            checker_version: 1,
            checker_content_digest: sha256(b"obend.zkml.proven_gate.v1"),
            profile,
        }
    }

    /// Computes a collision-free 256-bit SHA-256 identity over every field of the suite artifact
    /// using self-delimiting LEB128 length-prefixed framing.
    pub fn suite_digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(512);
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
        sha256(&buf)
    }

    /// Checks consistency between top-level `ext_degree`/`base_field_modulus` and
    /// `profile.{ext_degree, field_modulus_bits}`, then runs the unconditional soundness floor gate.
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
        self.profile.check_proven_floor(regime)
    }
}

// ---------------------------------------------------------------------------
// 2. Streaming Recurrent GDN / SSM Chunk-Carry Receipts & Commitments
// ---------------------------------------------------------------------------

/// One authenticated chunk receipt in a streaming Gated-DeltaNet / SSM recurrent inference chain.
///
/// Matches `Obend.SymbolicZk.ProvenZkmlGate.ZkmlChunkReceipt` field-for-field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkmlChunkReceipt {
    pub model_weights_root: [u8; 32],
    pub policy_floor_digest: [u8; 32],
    pub suite_digest: [u8; 32],
    pub chunk_idx: u64,
    pub state_in_commit: [u8; 32],
    pub input_commit: [u8; 32],
    pub state_out_commit: [u8; 32],
    pub output_commit: [u8; 32],
    pub pow_nonce: u64,
    pub chunk_commitment: [u8; 32],
}

/// Encodes the exact 9-field LEB128-length-framed preimage committed under
/// `OBEND.SHE.ZKML_CHUNK/v1`.
///
/// Field order (exact parity with `Obend.SymbolicZk.ProvenZkmlGate`):
/// 1. `model_weights_root` (32 bytes)
/// 2. `policy_floor_digest` (32 bytes)
/// 3. `suite_digest` (32 bytes)
/// 4. `chunk_idx` (8-byte big-endian)
/// 5. `state_in_commit` (32 bytes)
/// 6. `input_commit` (32 bytes)
/// 7. `state_out_commit` (32 bytes)
/// 8. `output_commit` (32 bytes)
/// 9. `pow_nonce` (8-byte big-endian)
#[allow(clippy::too_many_arguments)]
pub fn encode_zkml_chunk_preimage(
    model_weights_root: &[u8; 32],
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    state_in_commit: &[u8; 32],
    input_commit: &[u8; 32],
    state_out_commit: &[u8; 32],
    output_commit: &[u8; 32],
    pow_nonce: u64,
) -> Vec<u8> {
    // 7 * (1 + 32) + 2 * (1 + 8) = 231 + 18 = 249 bytes.
    let mut preimage = Vec::with_capacity(249);
    push_framed_field(&mut preimage, model_weights_root);
    push_framed_field(&mut preimage, policy_floor_digest);
    push_framed_field(&mut preimage, suite_digest);
    push_framed_field(&mut preimage, &chunk_idx.to_be_bytes());
    push_framed_field(&mut preimage, state_in_commit);
    push_framed_field(&mut preimage, input_commit);
    push_framed_field(&mut preimage, state_out_commit);
    push_framed_field(&mut preimage, output_commit);
    push_framed_field(&mut preimage, &pow_nonce.to_be_bytes());
    preimage
}

/// Computes the canonical 32-byte `OBEND.SHE.ZKML_CHUNK/v1` `cSHAKE256` commitment.
#[allow(clippy::too_many_arguments)]
pub fn compute_zkml_chunk_commitment(
    model_weights_root: &[u8; 32],
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    state_in_commit: &[u8; 32],
    input_commit: &[u8; 32],
    state_out_commit: &[u8; 32],
    output_commit: &[u8; 32],
    pow_nonce: u64,
) -> [u8; 32] {
    let preimage = encode_zkml_chunk_preimage(
        model_weights_root,
        policy_floor_digest,
        suite_digest,
        chunk_idx,
        state_in_commit,
        input_commit,
        state_out_commit,
        output_commit,
        pow_nonce,
    );
    cshake256_32(ZKML_CHUNK_DOMAIN_TAG, &preimage)
}

impl ZkmlChunkReceipt {
    /// Encodes this receipt's 9-field LEB128-framed preimage.
    pub fn encode_preimage(&self) -> Vec<u8> {
        encode_zkml_chunk_preimage(
            &self.model_weights_root,
            &self.policy_floor_digest,
            &self.suite_digest,
            self.chunk_idx,
            &self.state_in_commit,
            &self.input_commit,
            &self.state_out_commit,
            &self.output_commit,
            self.pow_nonce,
        )
    }

    /// Recomputes the canonical `OBEND.SHE.ZKML_CHUNK/v1` `cSHAKE256` commitment for this receipt.
    pub fn recompute_commitment(&self) -> [u8; 32] {
        compute_zkml_chunk_commitment(
            &self.model_weights_root,
            &self.policy_floor_digest,
            &self.suite_digest,
            self.chunk_idx,
            &self.state_in_commit,
            &self.input_commit,
            &self.state_out_commit,
            &self.output_commit,
            self.pow_nonce,
        )
    }

    /// Serializes this receipt into a fixed 272-byte big-endian record.
    pub fn encode_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.model_weights_root);
        out.extend_from_slice(&self.policy_floor_digest);
        out.extend_from_slice(&self.suite_digest);
        out.extend_from_slice(&self.chunk_idx.to_be_bytes());
        out.extend_from_slice(&self.state_in_commit);
        out.extend_from_slice(&self.input_commit);
        out.extend_from_slice(&self.state_out_commit);
        out.extend_from_slice(&self.output_commit);
        out.extend_from_slice(&self.pow_nonce.to_be_bytes());
        out.extend_from_slice(&self.chunk_commitment);
    }

    /// Decodes a fixed 272-byte big-endian record into a [`ZkmlChunkReceipt`].
    pub fn decode_bytes(bytes: &[u8]) -> Result<Self, ZkmlGateRefusal> {
        if bytes.len() != SERIALIZED_CHUNK_RECEIPT_BYTES {
            return Err(ZkmlGateRefusal::CandidateBindingMismatch {
                reason: "chunk receipt byte length mismatch",
            });
        }
        let mut cursor = 0usize;
        let read32 = |c: &mut usize| -> [u8; 32] {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes[*c..*c + 32]);
            *c += 32;
            arr
        };
        let read_u64 = |c: &mut usize| -> u64 {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&bytes[*c..*c + 8]);
            *c += 8;
            u64::from_be_bytes(arr)
        };

        let model_weights_root = read32(&mut cursor);
        let policy_floor_digest = read32(&mut cursor);
        let suite_digest = read32(&mut cursor);
        let chunk_idx = read_u64(&mut cursor);
        let state_in_commit = read32(&mut cursor);
        let input_commit = read32(&mut cursor);
        let state_out_commit = read32(&mut cursor);
        let output_commit = read32(&mut cursor);
        let pow_nonce = read_u64(&mut cursor);
        let chunk_commitment = read32(&mut cursor);

        Ok(Self {
            model_weights_root,
            policy_floor_digest,
            suite_digest,
            chunk_idx,
            state_in_commit,
            input_commit,
            state_out_commit,
            output_commit,
            pow_nonce,
            chunk_commitment,
        })
    }
}

/// Deterministic folding root over a sequence of 32-byte chunk commitments (inputs or outputs).
pub fn fold_chunk_roots(commits: &[[u8; 32]]) -> [u8; 32] {
    let mut pre = Vec::with_capacity(8 + commits.len() * 32);
    pre.extend_from_slice(&(commits.len() as u64).to_be_bytes());
    for c in commits {
        pre.extend_from_slice(c);
    }
    sha256(&pre)
}

/// One chunk step supplied to [`StreamingZkmlJob`] for a streaming Gated-DeltaNet / SSM rollout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingChunkInput {
    pub chunk_idx: u64,
    pub state_in_commit: [u8; 32],
    pub input_commit: [u8; 32],
    pub state_out_commit: [u8; 32],
    pub output_commit: [u8; 32],
}

/// Proving job submitted to [`ProveService<StreamingZkmlJob, CandidateComputation>`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingZkmlJob {
    pub request_id: [u8; 32],
    pub model_id: String,
    pub model_weights_root: [u8; 32],
    pub policy_floor_digest: [u8; 32],
    pub suite: ZkmlSuiteArtifact,
    pub requested_regime: SecurityRegime,
    pub initial_state_commit: [u8; 32],
    pub chunks: Vec<StreamingChunkInput>,
    /// Number of worker threads for `windowed_find_map_first_cancellable` PoW grinding (`>= 1`).
    pub grind_threads: usize,
    /// Upper nonce bound for PoW grinding (`0` uses [`DEFAULT_ZKML_GRIND_SPAN`]).
    pub grind_span: u64,
}

/// Native computation response matching `CROSS_REPO_CONTRACTS.md` §2 (`CandidateComputation`).
///
/// Native completion only means candidate bytes and chunk receipts were produced; final admission
/// must always pass fail-closed [`verify_candidate_computation`].
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
    pub soundness_report: ZkmlSoundnessReport,
    pub chunk_receipts: Vec<ZkmlChunkReceipt>,
    pub proof_bytes: Vec<u8>,
}

/// Serializes a full chunk receipt chain with a leading 8-byte big-endian chunk count.
pub fn encode_chunk_chain_bytes(receipts: &[ZkmlChunkReceipt]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + receipts.len() * SERIALIZED_CHUNK_RECEIPT_BYTES);
    out.extend_from_slice(&(receipts.len() as u64).to_be_bytes());
    for receipt in receipts {
        receipt.encode_bytes(&mut out);
    }
    out
}

/// Decodes `proof_bytes` back into a vector of [`ZkmlChunkReceipt`]s, failing closed on any
/// truncation or trailing garbage.
pub fn decode_chunk_chain_bytes(bytes: &[u8]) -> Result<Vec<ZkmlChunkReceipt>, ZkmlGateRefusal> {
    if bytes.len() < 8 {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "proof_bytes shorter than 8-byte chunk count header",
        });
    }
    let count = u64::from_be_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ]);
    let count_usize = usize::try_from(count).map_err(|_| {
        ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "chunk count overflows usize",
        }
    })?;
    let expected_len = count_usize
        .checked_mul(SERIALIZED_CHUNK_RECEIPT_BYTES)
        .and_then(|n| n.checked_add(8))
        .ok_or(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "proof_bytes length overflow",
        })?;
    if bytes.len() != expected_len {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "proof_bytes length does not match declared chunk count",
        });
    }

    let mut receipts = Vec::with_capacity(count_usize);
    for i in 0..count_usize {
        let start = 8 + i * SERIALIZED_CHUNK_RECEIPT_BYTES;
        let end = start + SERIALIZED_CHUNK_RECEIPT_BYTES;
        receipts.push(ZkmlChunkReceipt::decode_bytes(&bytes[start..end])?);
    }
    Ok(receipts)
}

/// Deterministically grinds the globally lowest `pow_nonce` in `0..span` such that
/// `OBEND.SHE.ZKML_CHUNK/v1` `cSHAKE256` satisfies `grind_bits` low zero bits, using
/// [`windowed_find_map_first_cancellable`] for exact `1T == NT` parity.
#[allow(clippy::too_many_arguments)]
pub fn grind_zkml_chunk_pow(
    model_weights_root: &[u8; 32],
    policy_floor_digest: &[u8; 32],
    suite_digest: &[u8; 32],
    chunk_idx: u64,
    state_in_commit: &[u8; 32],
    input_commit: &[u8; 32],
    state_out_commit: &[u8; 32],
    output_commit: &[u8; 32],
    grind_bits: u32,
    span: u64,
    threads: usize,
    cancel: &CancelToken,
) -> Result<(u64, [u8; 32]), ZkmlGateRefusal> {
    if cancel.is_cancelled() {
        return Err(ZkmlGateRefusal::Cancelled);
    }
    if grind_bits > 64 {
        return Err(ZkmlGateRefusal::InvalidChunkPow {
            chunk_idx,
            required_bits: grind_bits,
            pow_nonce: 0,
        });
    }
    let effective_span = if span == 0 {
        DEFAULT_ZKML_GRIND_SPAN
    } else {
        span
    };

    // Pre-build the fixed 240-byte prefix (fields 1..=8) + field-9 LEB128 length byte `0x08` once,
    // so each candidate nonce only overwrites the final 8 bytes before hashing.
    let mut base_preimage = Vec::with_capacity(249);
    push_framed_field(&mut base_preimage, model_weights_root);
    push_framed_field(&mut base_preimage, policy_floor_digest);
    push_framed_field(&mut base_preimage, suite_digest);
    push_framed_field(&mut base_preimage, &chunk_idx.to_be_bytes());
    push_framed_field(&mut base_preimage, state_in_commit);
    push_framed_field(&mut base_preimage, input_commit);
    push_framed_field(&mut base_preimage, state_out_commit);
    push_framed_field(&mut base_preimage, output_commit);
    encode_leb128(8, &mut base_preimage);
    debug_assert_eq!(base_preimage.len(), 241);

    // Pre-absorb the domain customization and first full 136-byte Keccak rate block once.
    let mut base_sponge = CshakeSponge::new(ZKML_CHUNK_DOMAIN_TAG);
    base_sponge.absorb(&base_preimage[..KECCAK_RATE_BYTES]);
    let tail_prefix = &base_preimage[KECCAK_RATE_BYTES..];

    let window = default_grind_window(grind_bits as usize, 1);
    let hit = windowed_find_map_first_cancellable(
        effective_span,
        window,
        threads.max(1),
        cancel,
        |nonce| {
            let mut sponge = base_sponge.clone();
            sponge.absorb(tail_prefix);
            sponge.absorb(&nonce.to_be_bytes());
            let commit = sponge.finalize_32();
            digest_has_low_zero_bits(&commit, grind_bits).then_some(commit)
        },
    );

    if cancel.is_cancelled() {
        return Err(ZkmlGateRefusal::Cancelled);
    }

    hit.ok_or(ZkmlGateRefusal::InvalidChunkPow {
        chunk_idx,
        required_bits: grind_bits,
        pow_nonce: effective_span,
    })
}

/// Fail-closed verifier for a multi-chunk recurrent [`ZkmlChunkReceipt`] chain.
pub fn verify_zkml_chunk_chain(
    receipts: &[ZkmlChunkReceipt],
    expected_weights_root: &[u8; 32],
    expected_policy_floor_digest: &[u8; 32],
    expected_suite_digest: &[u8; 32],
    initial_state_commit: &[u8; 32],
    required_grind_bits: u32,
) -> Result<[u8; 32], ZkmlGateRefusal> {
    if receipts.is_empty() {
        return Err(ZkmlGateRefusal::EmptyChunkChain);
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

        let recomputed = receipt.recompute_commitment();
        if receipt.chunk_commitment != recomputed {
            return Err(ZkmlGateRefusal::ChunkCommitmentMismatch {
                chunk_idx: expected_idx,
                expected: recomputed,
                actual: receipt.chunk_commitment,
            });
        }

        if !digest_has_low_zero_bits(&receipt.chunk_commitment, required_grind_bits) {
            return Err(ZkmlGateRefusal::InvalidChunkPow {
                chunk_idx: expected_idx,
                required_bits: required_grind_bits,
                pow_nonce: receipt.pow_nonce,
            });
        }

        expected_state_in = receipt.state_out_commit;
    }

    Ok(expected_state_in)
}

/// Fail-closed end-to-end verification of a [`CandidateComputation`] against pinned request,
/// model weight root, policy floor digest, suite artifact, and proven soundness regime.
pub fn verify_candidate_computation(
    candidate: &CandidateComputation,
    expected_request_id: &[u8; 32],
    expected_weights_root: &[u8; 32],
    expected_policy_floor_digest: &[u8; 32],
    expected_suite: &ZkmlSuiteArtifact,
    requested_regime: SecurityRegime,
) -> Result<ZkmlSoundnessReport, ZkmlGateRefusal> {
    let report = expected_suite.check_proven_floor(requested_regime)?;

    if candidate.request_id != *expected_request_id {
        return Err(ZkmlGateRefusal::CandidateBindingMismatch {
            reason: "request_id mismatch",
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

    let final_state = verify_zkml_chunk_chain(
        &decoded,
        expected_weights_root,
        expected_policy_floor_digest,
        &expected_suite_digest,
        &candidate.initial_state_commit,
        expected_suite.profile.grind_bits,
    )?;

    if candidate.final_state_commit != final_state {
        return Err(ZkmlGateRefusal::BrokenChunkCarry {
            chunk_idx: decoded.len() as u64,
            expected_state_in: final_state,
            actual_state_in: candidate.final_state_commit,
        });
    }

    let inputs: Vec<[u8; 32]> = decoded.iter().map(|r| r.input_commit).collect();
    let outputs: Vec<[u8; 32]> = decoded.iter().map(|r| r.output_commit).collect();
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

// ---------------------------------------------------------------------------
// 3. StreamingZkmlBackend Wired to ProveService + CancellableBackend
// ---------------------------------------------------------------------------

/// Streaming recurrent Gated-DeltaNet / SSM proving backend for [`ProveService`].
///
/// Enforces the unconditional soundness floor gate before proving, verifies recurrent chunk-carry
/// continuity across every chunk, grinds deterministic `1T == NT` `OBEND.SHE.ZKML_CHUNK/v1` PoW
/// witnesses via [`windowed_find_map_first_cancellable`], and respects cooperative [`CancelToken`]
/// invalidation for stale epochs.
#[derive(Clone, Debug, Default)]
pub struct StreamingZkmlBackend {
    pinned_weights_root: Option<[u8; 32]>,
    pinned_policy_floor_digest: Option<[u8; 32]>,
}

impl StreamingZkmlBackend {
    /// Creates a streaming zkML backend that pins roots per job.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a streaming zkML backend pinned to a fixed `model_weights_root` and
    /// `policy_floor_digest` (rejecting any job attempting weight or policy drift).
    pub fn pinned(model_weights_root: [u8; 32], policy_floor_digest: [u8; 32]) -> Self {
        Self {
            pinned_weights_root: Some(model_weights_root),
            pinned_policy_floor_digest: Some(policy_floor_digest),
        }
    }

    /// Executes one streaming recurrent chunk-carry job synchronously with cooperative
    /// cancellation.
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

        // 1. Enforce unconditional >= 100-bit proven soundness floor BEFORE grinding.
        let report = job.suite.check_proven_floor(job.requested_regime)?;

        if job.chunks.is_empty() {
            return Err(ZkmlGateRefusal::EmptyChunkChain);
        }

        // 2. Verify recurrent hidden-state carry before grinding so broken chains fail fast.
        let mut expected_state_in = job.initial_state_commit;
        for (idx, chunk) in job.chunks.iter().enumerate() {
            let expected_idx = idx as u64;
            if chunk.chunk_idx != expected_idx {
                return Err(ZkmlGateRefusal::ChunkIndexMismatch {
                    expected: expected_idx,
                    actual: chunk.chunk_idx,
                });
            }
            if chunk.state_in_commit != expected_state_in {
                return Err(ZkmlGateRefusal::BrokenChunkCarry {
                    chunk_idx: expected_idx,
                    expected_state_in,
                    actual_state_in: chunk.state_in_commit,
                });
            }
            expected_state_in = chunk.state_out_commit;
        }

        // 3. Grind deterministic 1T == NT cSHAKE256 PoW commitment for each chunk in sequence.
        let suite_digest = job.suite.suite_digest();
        let mut receipts = Vec::with_capacity(job.chunks.len());
        let mut input_commits = Vec::with_capacity(job.chunks.len());
        let mut output_commits = Vec::with_capacity(job.chunks.len());

        for chunk in &job.chunks {
            if cancel.is_cancelled() {
                return Err(ZkmlGateRefusal::Cancelled);
            }
            let (pow_nonce, chunk_commitment) = grind_zkml_chunk_pow(
                &job.model_weights_root,
                &job.policy_floor_digest,
                &suite_digest,
                chunk.chunk_idx,
                &chunk.state_in_commit,
                &chunk.input_commit,
                &chunk.state_out_commit,
                &chunk.output_commit,
                job.suite.profile.grind_bits,
                job.grind_span,
                job.grind_threads,
                cancel,
            )?;
            receipts.push(ZkmlChunkReceipt {
                model_weights_root: job.model_weights_root,
                policy_floor_digest: job.policy_floor_digest,
                suite_digest,
                chunk_idx: chunk.chunk_idx,
                state_in_commit: chunk.state_in_commit,
                input_commit: chunk.input_commit,
                state_out_commit: chunk.state_out_commit,
                output_commit: chunk.output_commit,
                pow_nonce,
                chunk_commitment,
            });
            input_commits.push(chunk.input_commit);
            output_commits.push(chunk.output_commit);
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
            soundness_report: report,
            chunk_receipts: receipts,
            proof_bytes,
        })
    }

    /// Wraps this backend as a [`CancellableBackend`] for [`ProveService::spawn_cancellable`].
    pub fn into_cancellable_backend(
        self,
    ) -> CancellableBackend<StreamingZkmlJob, CandidateComputation> {
        Arc::new(move |job: StreamingZkmlJob, cancel: &CancelToken| {
            self.prove_job(&job, cancel).map_err(|err| err.to_string())
        })
    }
}

/// Spawns a hardened [`ProveService`] backed by [`StreamingZkmlBackend`].
pub fn spawn_streaming_zkml_service(
    backend: StreamingZkmlBackend,
    config: ProveServiceConfig,
) -> ProveService<StreamingZkmlJob, CandidateComputation> {
    ProveService::spawn_cancellable(backend.into_cancellable_backend(), config)
}
