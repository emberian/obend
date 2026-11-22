#![forbid(unsafe_code)]
//! Unified Multi-Turn "Anti-Vaz" Sovereign SHE Ceremony (`Obend.Polis.SecureHardwareEnv`).
//!
//! Closes *Rainbows End* SHE Gap #5 in pure zero-dependency Rust with byte-exact parity against
//! `lean/Obend/Polis/SecureHardwareEnv.lean`:
//! - **Constitutional Non-Regression (`vaz_coercive_floor_downgrade_refused`)**: Every
//!   [`SheTurn::UpgradeHabitatJudge`] proposal—even carrying a vendor root directive or external
//!   intelligence-agency emergency signature ([`UpgradeAuthorityClaim`])—is unconditionally
//!   refused if it drops any active privacy or physical-safety [`SheFloor`].
//! - **8-Gate Multi-Turn Actuation Settlement (`she_trace_end_to_end_safe_and_anti_vaz`)**:
//!   Enforces strictly monotone sealed sensor/TLSN sequence numbers, proven-regime (`UDR`/`JBR`,
//!   rejecting withdrawn `CBR`) `>= 100`-bit (`100_000` milli-bit) zkML [`CandidateComputation`]
//!   bound to `pinned_model_weights_root` + `she_floors_digest`, fresh 256-bit nullifier,
//!   sufficient `remaining_mandate_budget`, `seL4` private-frame copy-before-verify match,
//!   `Simplex` `3f + 1 <= n` `n - f` finalized QC, `(t, n)` post-quantum custodian threshold
//!   quorum (`signers` duplicate-free, unrevoked, `>= t`), and ToF physical-presence proximity
//!   (`tof_round_trip_ticks <= max_proximity_ticks`).
//! - **Byte-Exact `OBEND.SHE.TURN/v1`, `OBEND.SHE.FLOORS/v1`, & `OBEND.SHE.PAYLOAD/v1` `cSHAKE256`
//!   Framing**: Pure-Rust Keccak-f[1600] + NIST SP 800-185 `cSHAKE256` + `LEB128` length-framed
//!   fields matching `SecureHardwareEnv.lean` bit-for-bit (`0` `cross-lang/domain-tag-drift`).
//! - **Sealed Oracle Integration**: Directly bridges [`VerifiedHttpsTranscript`],
//!   [`VerifiedCallTree`], [`VerifiedE2eeChannel`], and [`VerifiedTeeEvidence`] receipts into
//!   monotone-sealed Sovereign SHE actuation turns.

use crate::sha256::ct_eq;
use crate::tee::{TcbPosture, TeeVendor, VerifiedTeeEvidence};
use crate::tlsn_e2ee::{VerifiedCallTree, VerifiedE2eeChannel, VerifiedHttpsTranscript};

// ---------------------------------------------------------------------------
// Pure-Rust Keccak-f[1600], NIST SP 800-185 `cSHAKE256`, & LEB128 Framing
// ---------------------------------------------------------------------------

const SHAKE256_RATE_BYTES: usize = 136;
const SHAKE256_RATE_LANES: usize = 17;

const KECCAK_ROUND_CONSTANTS: [u64; 24] = [
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

const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

fn keccak_f1600(state: &mut [u64; 25]) {
    for &rc in &KECCAK_ROUND_CONSTANTS {
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
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] =
                    state[x + 5 * y].rotate_left(KECCAK_ROTATION_OFFSETS[x + 5 * y]);
            }
        }
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
            }
        }
        state[0] ^= rc;
    }
}

fn sp800_185_left_encode(mut value: usize) -> Vec<u8> {
    if value == 0 {
        return vec![1u8, 0u8];
    }
    let mut le = Vec::with_capacity(8);
    while value > 0 {
        le.push((value & 0xFF) as u8);
        value >>= 8;
    }
    le.reverse();
    let mut out = Vec::with_capacity(1 + le.len());
    out.push(le.len() as u8);
    out.extend_from_slice(&le);
    out
}

fn sp800_185_encode_string(bytes: &[u8]) -> Vec<u8> {
    let mut out = sp800_185_left_encode(bytes.len().saturating_mul(8));
    out.extend_from_slice(bytes);
    out
}

fn sp800_185_bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
    if width == 0 {
        return Vec::new();
    }
    let mut out = sp800_185_left_encode(width);
    out.extend_from_slice(bytes);
    let rem = out.len() % width;
    if rem != 0 {
        out.resize(out.len() + (width - rem), 0u8);
    }
    out
}

fn xor_rate_block(state: &mut [u64; 25], block: &[u8]) {
    for (lane_idx, st_lane) in state.iter_mut().enumerate().take(SHAKE256_RATE_LANES) {
        let off = 8 * lane_idx;
        let lane = u64::from_le_bytes([
            block[off],
            block[off + 1],
            block[off + 2],
            block[off + 3],
            block[off + 4],
            block[off + 5],
            block[off + 6],
            block[off + 7],
        ]);
        *st_lane ^= lane;
    }
}

/// Evaluate 32-byte NIST SP 800-185 `cSHAKE256` (`N = ""`, `S = customization`), matching
/// `Obend.Digest.Cshake256.cshake256Bytes` and `Obend.Crypto.cshake32ByteArray` bit-for-bit.
pub fn she_cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let suffix = if customization.is_empty() { 0x1f } else { 0x04 };
    let mut framed = if customization.is_empty() {
        input.to_vec()
    } else {
        let mut inner = sp800_185_encode_string(&[]);
        inner.extend_from_slice(&sp800_185_encode_string(customization));
        let mut pfx = sp800_185_bytepad(&inner, SHAKE256_RATE_BYTES);
        pfx.extend_from_slice(input);
        pfx
    };

    let count = SHAKE256_RATE_BYTES - (framed.len() % SHAKE256_RATE_BYTES);
    if count == 1 {
        framed.push(suffix ^ 0x80);
    } else {
        framed.push(suffix);
        framed.resize(framed.len() + (count - 2), 0u8);
        framed.push(0x80);
    }

    let mut state = [0u64; 25];
    for chunk in framed.as_chunks::<SHAKE256_RATE_BYTES>().0 {
        xor_rate_block(&mut state, chunk);
        keccak_f1600(&mut state);
    }

    let mut out = [0u8; 32];
    for lane_idx in 0..4 {
        out[8 * lane_idx..8 * lane_idx + 8].copy_from_slice(&state[lane_idx].to_le_bytes());
    }
    out
}

/// Canonical unsigned LEB128 encoding matching `Obend.Crypto.Transcript.leb128`.
pub fn she_leb128(mut n: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(4);
    loop {
        if n < 128 {
            out.push(n as u8);
            return out;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
}

/// Length-prefixed byte field (`leb128(len(xs)) || xs`) matching `Obend.Crypto.encodeListField`.
pub fn encode_she_field(xs: &[u8]) -> Vec<u8> {
    let mut out = she_leb128(xs.len() as u64);
    out.extend_from_slice(xs);
    out
}

/// Concatenate length-prefixed fields matching `Obend.Polis.SecureHardwareEnv.encodeSheFields`.
pub fn encode_she_fields(fields: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for f in fields {
        out.extend_from_slice(&encode_she_field(f));
    }
    out
}

fn encode_nat_list(xs: &[u64]) -> Vec<u8> {
    let mapped: Vec<Vec<u8>> = xs.iter().map(|&n| she_leb128(n)).collect();
    encode_she_fields(&mapped)
}

// ---------------------------------------------------------------------------
// 1. Floors, Unconditional zkML Soundness Accounting, & Turn Carriers
// ---------------------------------------------------------------------------

/// Minimum proven zkML soundness floor required for Sovereign SHE actuation (`100.000` bits).
pub const SHE_MIN_PROVEN_ZKML_MILLI_BITS: u64 = 100_000;

/// Constitutional user-sovereign safety & privacy floors (`Obend.Polis.SecureHardwareEnv.SheFloor`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SheFloor {
    SensorRoiRedaction { min_redacted_rois: u64 },
    ConsentBandNonOcclusion { min_band_height_px: u64 },
    ZkmlProvenSoundnessMilliBits { min_milli_bits: u64 },
    PhysicalProximityMaxTicks { max_ticks: u64 },
    E2eeTeeChannelBound { min_attested_gpus: u64 },
    OperatorLocalRevert { max_revert_steps: u64 },
}

impl SheFloor {
    pub const fn is_bedrock(self) -> bool {
        matches!(self, Self::OperatorLocalRevert { .. })
    }

    pub const fn well_formed(self) -> bool {
        match self {
            Self::SensorRoiRedaction { .. } | Self::E2eeTeeChannelBound { .. } => true,
            Self::ConsentBandNonOcclusion { min_band_height_px } => min_band_height_px > 0,
            Self::ZkmlProvenSoundnessMilliBits { min_milli_bits } => {
                min_milli_bits >= SHE_MIN_PROVEN_ZKML_MILLI_BITS
            }
            Self::PhysicalProximityMaxTicks { max_ticks } => max_ticks > 0,
            Self::OperatorLocalRevert { max_revert_steps } => max_revert_steps > 0,
        }
    }

    pub fn encode(self) -> Vec<u8> {
        let (tag, val) = match self {
            Self::SensorRoiRedaction { min_redacted_rois } => (0x01u8, min_redacted_rois),
            Self::ConsentBandNonOcclusion { min_band_height_px } => (0x02u8, min_band_height_px),
            Self::ZkmlProvenSoundnessMilliBits { min_milli_bits } => (0x03u8, min_milli_bits),
            Self::PhysicalProximityMaxTicks { max_ticks } => (0x04u8, max_ticks),
            Self::E2eeTeeChannelBound { min_attested_gpus } => (0x05u8, min_attested_gpus),
            Self::OperatorLocalRevert { max_revert_steps } => (0x06u8, max_revert_steps),
        };
        let mut out = vec![tag];
        out.extend_from_slice(&she_leb128(val));
        out
    }
}

/// Encode a slice of [`SheFloor`] values with `encode_she_field` framing on each floor.
pub fn encode_she_floors(floors: &[SheFloor]) -> Vec<u8> {
    let encoded: Vec<Vec<u8>> = floors.iter().map(|f| f.encode()).collect();
    encode_she_fields(&encoded)
}

/// Canonical 256-bit `OBEND.SHE.FLOORS/v1` digest matching `SecureHardwareEnv.floorsDigest`.
pub fn she_floors_digest(floors: &[SheFloor]) -> [u8; 32] {
    she_cshake256_32(b"OBEND.SHE.FLOORS/v1", &encode_she_floors(floors))
}

/// Canonical 256-bit `OBEND.SHE.PAYLOAD/v1` digest matching `SecureHardwareEnv.shePayloadDigest`.
pub fn she_payload_digest(payload: &[u8]) -> [u8; 32] {
    she_cshake256_32(
        b"OBEND.SHE.PAYLOAD/v1",
        &encode_she_fields(&[payload.to_vec()]),
    )
}

/// Soundness regime declared by a zkML [`CandidateComputation`] proof suite.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZkmlSoundnessRegime {
    UniqueDecodingUdr,
    JohnsonBoundJbr,
    WithdrawnCapacityBoundCbr,
}

impl ZkmlSoundnessRegime {
    pub const fn tag_byte(self) -> u8 {
        match self {
            Self::UniqueDecodingUdr => 0x01,
            Self::JohnsonBoundJbr => 0x02,
            Self::WithdrawnCapacityBoundCbr => 0x03,
        }
    }
}

/// Exact integer milli-bits per query in the Unique-Decoding Regime (`UDR`).
pub const fn udr_per_query_milli_bits(log_blowup: u64) -> u64 {
    match log_blowup {
        0 => 0,
        1 => 415,
        2 => 678,
        3 => 830,
        4 => 912,
        5 => 955,
        6 => 977,
        7 => 988,
        _ => 994,
    }
}

/// Exact integer milli-bits per query in the Johnson-Bound Regime (`JBR`).
pub const fn jbr_per_query_milli_bits(log_blowup: u64) -> u64 {
    log_blowup.saturating_mul(500)
}

/// Candidate zkML inference computation binding model weights, active floors, sealed sensor
/// input, and proposed actuation payload (`SecureHardwareEnv.CandidateComputation`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateComputation {
    pub statement_digest: [u8; 32],
    pub model_weights_root: [u8; 32],
    pub bound_floors_digest: [u8; 32],
    pub sensor_seal_digest: [u8; 32],
    pub action_payload_digest: [u8; 32],
    pub regime: ZkmlSoundnessRegime,
    pub log_blowup: u64,
    pub num_queries: u64,
    pub grind_bits: u64,
    pub ext_field_bits: u64,
    pub proof_verified: bool,
}

impl CandidateComputation {
    pub fn encode(&self) -> Vec<u8> {
        encode_she_fields(&[
            self.statement_digest.to_vec(),
            self.model_weights_root.to_vec(),
            self.bound_floors_digest.to_vec(),
            self.sensor_seal_digest.to_vec(),
            self.action_payload_digest.to_vec(),
            vec![self.regime.tag_byte()],
            she_leb128(self.log_blowup),
            she_leb128(self.num_queries),
            she_leb128(self.grind_bits),
            she_leb128(self.ext_field_bits),
            vec![u8::from(self.proof_verified)],
        ])
    }
}

/// Realized proven soundness in milli-bits matching `SecureHardwareEnv.provenZkmlMilliBits`.
/// Withdrawn `CBR` suites score `0`, and PoW grinding credit is capped at `24` bits so query
/// soundness carries `>= 76` bits.
pub fn proven_zkml_milli_bits(c: &CandidateComputation) -> u64 {
    if !c.proof_verified || c.log_blowup == 0 || c.num_queries == 0 {
        return 0;
    }
    let cap = c.ext_field_bits.saturating_mul(1_000).min(256_000);
    let grind_mbit = c.grind_bits.min(24).saturating_mul(1_000);
    match c.regime {
        ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr => 0,
        ZkmlSoundnessRegime::UniqueDecodingUdr => c
            .num_queries
            .saturating_mul(udr_per_query_milli_bits(c.log_blowup))
            .saturating_add(grind_mbit)
            .min(cap),
        ZkmlSoundnessRegime::JohnsonBoundJbr => c
            .num_queries
            .saturating_mul(jbr_per_query_milli_bits(c.log_blowup))
            .saturating_add(grind_mbit)
            .min(cap),
    }
}

/// Legacy withdrawn `CBR` milli-bit estimate (`lb * q * 1000 + grind * 1000`).
pub fn legacy_withdrawn_cbr_milli_bits(c: &CandidateComputation) -> u64 {
    c.log_blowup
        .saturating_mul(c.num_queries)
        .saturating_mul(1_000)
        .saturating_add(c.grind_bits.saturating_mul(1_000))
}

/// Claimed authority accompanying a judge upgrade (`SecureHardwareEnv.UpgradeAuthorityClaim`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UpgradeAuthorityClaim {
    LocalCustodianCeremony,
    VendorRootDirective { vendor_sig: Vec<u8> },
    AgencyEmergencyOrder { agency_id: Vec<u8>, agency_sig: Vec<u8> },
}

impl UpgradeAuthorityClaim {
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Self::LocalCustodianCeremony => encode_she_fields(&[vec![0x01]]),
            Self::VendorRootDirective { vendor_sig } => {
                encode_she_fields(&[vec![0x02], vendor_sig.clone()])
            }
            Self::AgencyEmergencyOrder {
                agency_id,
                agency_sig,
            } => encode_she_fields(&[vec![0x03], agency_id.clone(), agency_sig.clone()]),
        }
    }
}

/// Full 8-gate actuation proposal (`SecureHardwareEnv.ActuationTurnProposal`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActuationTurnProposal {
    pub sensor_seq: u64,
    pub sensor_seal_digest: [u8; 32],
    pub candidate: CandidateComputation,
    pub nullifier: [u8; 32],
    pub mandate_cost: u64,
    pub redacted_roi_count: u64,
    pub consent_band_height_px: u64,
    pub attested_gpu_count: u64,
    pub shared_ring_at_copy: Vec<u8>,
    pub private_frame_copy: Vec<u8>,
    pub dispatched_payload: Vec<u8>,
    pub simplex_committee_n: u64,
    pub simplex_faulty_f: u64,
    pub simplex_finalize_signers: Vec<u64>,
    pub custodian_epoch: u64,
    pub custodian_signers: Vec<u64>,
    pub tof_round_trip_ticks: u64,
}

/// Constitutional habitat judge upgrade proposal (`SecureHardwareEnv.UpgradeJudgeProposal`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpgradeJudgeProposal {
    pub new_judge_digest: [u8; 32],
    pub new_model_weights_root: [u8; 32],
    pub new_floors: Vec<SheFloor>,
    pub new_revert_window_steps: u64,
    pub new_custodian_epoch: u64,
    pub custodian_signers: Vec<u64>,
    pub tof_round_trip_ticks: u64,
    pub authority_claim: UpgradeAuthorityClaim,
}

/// Monotone mandate attenuation & custodian revocation (`SecureHardwareEnv.MandateAttenuation`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MandateAttenuation {
    pub new_budget_cap: u64,
    pub new_max_proximity_ticks: u64,
    pub newly_revoked_custodians: Vec<u64>,
    pub reason_digest: [u8; 32],
}

/// Three-kind Sovereign SHE ceremony turn (`SecureHardwareEnv.SheTurn`).
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SheTurn {
    ProposeAndSettleActuation(ActuationTurnProposal),
    UpgradeHabitatJudge(UpgradeJudgeProposal),
    RevokeOrAttenuateMandate(MandateAttenuation),
}

/// Canonical `OBEND.SHE.TURN/v1` length-framed preimage matching `SecureHardwareEnv.sheTurnPreimage`.
pub fn she_turn_preimage(turn: &SheTurn) -> Vec<u8> {
    let fields: Vec<Vec<u8>> = match turn {
        SheTurn::ProposeAndSettleActuation(act) => vec![
            vec![0x01],
            she_leb128(act.sensor_seq),
            act.sensor_seal_digest.to_vec(),
            act.candidate.encode(),
            act.nullifier.to_vec(),
            she_leb128(act.mandate_cost),
            she_leb128(act.redacted_roi_count),
            she_leb128(act.consent_band_height_px),
            she_leb128(act.attested_gpu_count),
            act.shared_ring_at_copy.clone(),
            act.private_frame_copy.clone(),
            act.dispatched_payload.clone(),
            she_leb128(act.simplex_committee_n),
            she_leb128(act.simplex_faulty_f),
            encode_nat_list(&act.simplex_finalize_signers),
            she_leb128(act.custodian_epoch),
            encode_nat_list(&act.custodian_signers),
            she_leb128(act.tof_round_trip_ticks),
        ],
        SheTurn::UpgradeHabitatJudge(up) => vec![
            vec![0x02],
            up.new_judge_digest.to_vec(),
            up.new_model_weights_root.to_vec(),
            encode_she_floors(&up.new_floors),
            she_leb128(up.new_revert_window_steps),
            she_leb128(up.new_custodian_epoch),
            encode_nat_list(&up.custodian_signers),
            she_leb128(up.tof_round_trip_ticks),
            up.authority_claim.encode(),
        ],
        SheTurn::RevokeOrAttenuateMandate(rev) => vec![
            vec![0x03],
            she_leb128(rev.new_budget_cap),
            she_leb128(rev.new_max_proximity_ticks),
            encode_nat_list(&rev.newly_revoked_custodians),
            rev.reason_digest.to_vec(),
        ],
    };
    encode_she_fields(&fields)
}

/// Full 256-bit `OBEND.SHE.TURN/v1` `cSHAKE256` turn envelope digest matching
/// `SecureHardwareEnv.sheTurnEnvelopeDigest`.
pub fn she_turn_envelope_digest(turn: &SheTurn) -> [u8; 32] {
    she_cshake256_32(b"OBEND.SHE.TURN/v1", &she_turn_preimage(turn))
}

// ---------------------------------------------------------------------------
// 2. Persistent Sovereign SHE State, Refusals, & `apply_she_turn`
// ---------------------------------------------------------------------------

/// Permanent audit record of a settled external actuation (`SecureHardwareEnv.SettledActuationRecord`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SettledActuationRecord {
    pub sensor_seq: u64,
    pub sensor_seal_digest: [u8; 32],
    pub nullifier: [u8; 32],
    pub mandate_cost: u64,
    pub redacted_roi_count: u64,
    pub consent_band_height_px: u64,
    pub attested_gpu_count: u64,
    pub proven_zkml_milli_bits: u64,
    pub zkml_regime: ZkmlSoundnessRegime,
    pub model_weights_root: [u8; 32],
    pub active_floors_at_settlement: Vec<SheFloor>,
    pub bound_floors_digest: [u8; 32],
    pub revert_window_at_settlement: u64,
    pub shared_ring_at_copy: Vec<u8>,
    pub private_frame_copy: Vec<u8>,
    pub dispatched_payload: Vec<u8>,
    pub simplex_committee_n: u64,
    pub simplex_faulty_f: u64,
    pub simplex_quorum_count: usize,
    pub custodian_epoch: u64,
    pub custodian_signers: Vec<u64>,
    pub tof_round_trip_ticks: u64,
    pub max_proximity_ticks_at_settle: u64,
    pub turn_envelope_digest: [u8; 32],
}

/// Persistent multi-turn Sovereign SHE state (`SecureHardwareEnv.SheState`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SheState {
    pub habitat_judge_digest: [u8; 32],
    pub pinned_model_weights_root: [u8; 32],
    pub mono_sensor_seq: u64,
    pub consumed_nullifiers: Vec<[u8; 32]>,
    pub remaining_mandate_budget: u64,
    pub active_safety_and_privacy_floors: Vec<SheFloor>,
    pub settled_outbox_actions: Vec<SettledActuationRecord>,
    pub custodian_threshold_t: u64,
    pub custodian_total_n: u64,
    pub custodian_quorum_epoch: u64,
    pub revoked_custodians: Vec<u64>,
    pub max_proximity_ticks: u64,
    pub revert_window_steps: u64,
}

impl SheState {
    pub fn settled_total_cost(&self) -> u64 {
        self.settled_outbox_actions
            .iter()
            .fold(0u64, |acc, r| acc.saturating_add(r.mandate_cost))
    }

    pub fn well_formed(&self) -> bool {
        check_slice_nodup(&self.active_safety_and_privacy_floors)
            && self
                .active_safety_and_privacy_floors
                .iter()
                .any(|f| f.is_bedrock())
            && self
                .active_safety_and_privacy_floors
                .iter()
                .all(|f| f.well_formed())
            && self.custodian_threshold_t >= 1
            && self.custodian_threshold_t <= self.custodian_total_n
            && self.max_proximity_ticks > 0
    }
}

/// Refusal vocabulary matching `SecureHardwareEnv.SheRefusal`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SheRefusal {
    MalformedInitialState,
    InvalidDigestWidth,
    NonMonotoneSensorSeq {
        current_seq: u64,
        proposed_seq: u64,
    },
    SensorSealMismatch,
    ZkmlProofUnverified,
    WithdrawnCbrRegimeRefused,
    BelowProven100BitFloor {
        actual_milli_bits: u64,
    },
    ModelWeightsRootMismatch,
    FloorsDigestMismatch,
    PayloadDigestMismatch,
    FloorConstraintViolated(SheFloor),
    NullifierReplayed,
    MandateBudgetExceeded {
        requested: u64,
        available: u64,
    },
    PrivateFrameCopyMismatch,
    InvalidSimplexCommittee {
        committee_n: u64,
        faulty_f: u64,
    },
    InvalidSimplexFinalityQc {
        signed_count: usize,
        required_quorum: u64,
    },
    CustodianEpochMismatch {
        expected: u64,
        actual: u64,
    },
    DuplicateOrOutOfRangeSigner,
    RevokedCustodianSigner {
        signer: u64,
    },
    InsufficientCustodianQuorum {
        signed_count: usize,
        required_t: u64,
    },
    TofProximityExceeded {
        actual_ticks: u64,
        max_ticks: u64,
    },
    CoerciveFloorDowngrade {
        dropped_floor: SheFloor,
    },
    MalformedFloorSet,
    NonMonotoneCustodianEpoch {
        current_epoch: u64,
        proposed_epoch: u64,
    },
    MandateAmplificationRefused,
    ProximityWideningRefused {
        proposed_ticks: u64,
        current_max_ticks: u64,
    },
    OracleEvidenceBindingMismatch,
}

fn check_slice_nodup<T: PartialEq>(xs: &[T]) -> bool {
    for (i, x) in xs.iter().enumerate() {
        if xs[i + 1..].contains(x) {
            return false;
        }
    }
    true
}

fn check_floor_on_actuation(
    revert_steps: u64,
    act: &ActuationTurnProposal,
    floor: SheFloor,
) -> bool {
    match floor {
        SheFloor::SensorRoiRedaction { min_redacted_rois } => {
            act.redacted_roi_count >= min_redacted_rois
        }
        SheFloor::ConsentBandNonOcclusion { min_band_height_px } => {
            min_band_height_px > 0 && act.consent_band_height_px >= min_band_height_px
        }
        SheFloor::ZkmlProvenSoundnessMilliBits { min_milli_bits } => {
            proven_zkml_milli_bits(&act.candidate) >= min_milli_bits
        }
        SheFloor::PhysicalProximityMaxTicks { max_ticks } => act.tof_round_trip_ticks <= max_ticks,
        SheFloor::E2eeTeeChannelBound { min_attested_gpus } => {
            act.attested_gpu_count >= min_attested_gpus
        }
        SheFloor::OperatorLocalRevert { max_revert_steps } => revert_steps <= max_revert_steps,
    }
}

fn check_custodian_quorum(st: &SheState, signers: &[u64]) -> Result<(), SheRefusal> {
    if st.custodian_threshold_t < 1 || st.custodian_threshold_t > st.custodian_total_n {
        return Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: signers.len(),
            required_t: st.custodian_threshold_t,
        });
    }
    if !check_slice_nodup(signers) || !signers.iter().all(|&s| s < st.custodian_total_n) {
        return Err(SheRefusal::DuplicateOrOutOfRangeSigner);
    }
    if let Some(&rev) = signers
        .iter()
        .find(|&&s| st.revoked_custodians.contains(&s))
    {
        return Err(SheRefusal::RevokedCustodianSigner { signer: rev });
    }
    if (signers.len() as u64) < st.custodian_threshold_t {
        return Err(SheRefusal::InsufficientCustodianQuorum {
            signed_count: signers.len(),
            required_t: st.custodian_threshold_t,
        });
    }
    Ok(())
}

/// Deterministic single-turn Sovereign SHE transition gate matching `SecureHardwareEnv.applySheTurn`.
pub fn apply_she_turn(st: &SheState, turn: &SheTurn) -> Result<SheState, SheRefusal> {
    match turn {
        SheTurn::ProposeAndSettleActuation(act) => {
            if act.sensor_seq <= st.mono_sensor_seq {
                return Err(SheRefusal::NonMonotoneSensorSeq {
                    current_seq: st.mono_sensor_seq,
                    proposed_seq: act.sensor_seq,
                });
            }
            if !ct_eq(&act.candidate.sensor_seal_digest, &act.sensor_seal_digest) {
                return Err(SheRefusal::SensorSealMismatch);
            }
            if !act.candidate.proof_verified {
                return Err(SheRefusal::ZkmlProofUnverified);
            }
            if act.candidate.regime == ZkmlSoundnessRegime::WithdrawnCapacityBoundCbr {
                return Err(SheRefusal::WithdrawnCbrRegimeRefused);
            }
            let milli_bits = proven_zkml_milli_bits(&act.candidate);
            if milli_bits < SHE_MIN_PROVEN_ZKML_MILLI_BITS {
                return Err(SheRefusal::BelowProven100BitFloor {
                    actual_milli_bits: milli_bits,
                });
            }
            if !ct_eq(
                &act.candidate.model_weights_root,
                &st.pinned_model_weights_root,
            ) {
                return Err(SheRefusal::ModelWeightsRootMismatch);
            }
            let expected_floors_dig = she_floors_digest(&st.active_safety_and_privacy_floors);
            if !ct_eq(&act.candidate.bound_floors_digest, &expected_floors_dig) {
                return Err(SheRefusal::FloorsDigestMismatch);
            }
            let expected_payload_dig = she_payload_digest(&act.private_frame_copy);
            if !ct_eq(&act.candidate.action_payload_digest, &expected_payload_dig) {
                return Err(SheRefusal::PayloadDigestMismatch);
            }
            if act.tof_round_trip_ticks > st.max_proximity_ticks {
                return Err(SheRefusal::TofProximityExceeded {
                    actual_ticks: act.tof_round_trip_ticks,
                    max_ticks: st.max_proximity_ticks,
                });
            }
            if let Some(&violated) = st
                .active_safety_and_privacy_floors
                .iter()
                .find(|&&f| !check_floor_on_actuation(st.revert_window_steps, act, f))
            {
                return Err(SheRefusal::FloorConstraintViolated(violated));
            }
            if st
                .consumed_nullifiers
                .iter()
                .any(|n| ct_eq(n, &act.nullifier))
            {
                return Err(SheRefusal::NullifierReplayed);
            }
            if act.mandate_cost > st.remaining_mandate_budget {
                return Err(SheRefusal::MandateBudgetExceeded {
                    requested: act.mandate_cost,
                    available: st.remaining_mandate_budget,
                });
            }
            if act.private_frame_copy != act.shared_ring_at_copy
                || act.dispatched_payload != act.private_frame_copy
            {
                return Err(SheRefusal::PrivateFrameCopyMismatch);
            }
            let Some(min_committee) = act
                .simplex_faulty_f
                .checked_mul(3)
                .and_then(|v| v.checked_add(1))
            else {
                return Err(SheRefusal::InvalidSimplexCommittee {
                    committee_n: act.simplex_committee_n,
                    faulty_f: act.simplex_faulty_f,
                });
            };
            if act.simplex_committee_n < min_committee {
                return Err(SheRefusal::InvalidSimplexCommittee {
                    committee_n: act.simplex_committee_n,
                    faulty_f: act.simplex_faulty_f,
                });
            }
            let required_qc = act.simplex_committee_n - act.simplex_faulty_f;
            if !check_slice_nodup(&act.simplex_finalize_signers)
                || !act
                    .simplex_finalize_signers
                    .iter()
                    .all(|&v| v < act.simplex_committee_n)
                || (act.simplex_finalize_signers.len() as u64) < required_qc
            {
                return Err(SheRefusal::InvalidSimplexFinalityQc {
                    signed_count: act.simplex_finalize_signers.len(),
                    required_quorum: required_qc,
                });
            }
            if act.custodian_epoch != st.custodian_quorum_epoch {
                return Err(SheRefusal::CustodianEpochMismatch {
                    expected: st.custodian_quorum_epoch,
                    actual: act.custodian_epoch,
                });
            }
            check_custodian_quorum(st, &act.custodian_signers)?;

            let turn_envelope_digest = she_turn_envelope_digest(turn);
            let record = SettledActuationRecord {
                sensor_seq: act.sensor_seq,
                sensor_seal_digest: act.sensor_seal_digest,
                nullifier: act.nullifier,
                mandate_cost: act.mandate_cost,
                redacted_roi_count: act.redacted_roi_count,
                consent_band_height_px: act.consent_band_height_px,
                attested_gpu_count: act.attested_gpu_count,
                proven_zkml_milli_bits: milli_bits,
                zkml_regime: act.candidate.regime,
                model_weights_root: act.candidate.model_weights_root,
                active_floors_at_settlement: st.active_safety_and_privacy_floors.clone(),
                bound_floors_digest: act.candidate.bound_floors_digest,
                revert_window_at_settlement: st.revert_window_steps,
                shared_ring_at_copy: act.shared_ring_at_copy.clone(),
                private_frame_copy: act.private_frame_copy.clone(),
                dispatched_payload: act.dispatched_payload.clone(),
                simplex_committee_n: act.simplex_committee_n,
                simplex_faulty_f: act.simplex_faulty_f,
                simplex_quorum_count: act.simplex_finalize_signers.len(),
                custodian_epoch: act.custodian_epoch,
                custodian_signers: act.custodian_signers.clone(),
                tof_round_trip_ticks: act.tof_round_trip_ticks,
                max_proximity_ticks_at_settle: st.max_proximity_ticks,
                turn_envelope_digest,
            };

            let mut next = st.clone();
            next.mono_sensor_seq = act.sensor_seq;
            next.consumed_nullifiers.push(act.nullifier);
            next.remaining_mandate_budget -= act.mandate_cost;
            next.settled_outbox_actions.push(record);
            Ok(next)
        }
        SheTurn::UpgradeHabitatJudge(up) => {
            // Anti-Vaz Gate 1: Unconditional floor non-regression BEFORE inspecting authority_claim.
            if let Some(&dropped) = st
                .active_safety_and_privacy_floors
                .iter()
                .find(|&&f| !up.new_floors.contains(&f))
            {
                return Err(SheRefusal::CoerciveFloorDowngrade {
                    dropped_floor: dropped,
                });
            }
            let revert_ok = up.new_floors.iter().all(|&f| match f {
                SheFloor::OperatorLocalRevert { max_revert_steps } => {
                    up.new_revert_window_steps <= max_revert_steps
                }
                _ => true,
            });
            if !check_slice_nodup(&up.new_floors)
                || !up.new_floors.iter().any(|f| f.is_bedrock())
                || !up.new_floors.iter().all(|f| f.well_formed())
                || !revert_ok
            {
                return Err(SheRefusal::MalformedFloorSet);
            }
            if up.new_custodian_epoch <= st.custodian_quorum_epoch {
                return Err(SheRefusal::NonMonotoneCustodianEpoch {
                    current_epoch: st.custodian_quorum_epoch,
                    proposed_epoch: up.new_custodian_epoch,
                });
            }
            check_custodian_quorum(st, &up.custodian_signers)?;
            if up.tof_round_trip_ticks > st.max_proximity_ticks {
                return Err(SheRefusal::TofProximityExceeded {
                    actual_ticks: up.tof_round_trip_ticks,
                    max_ticks: st.max_proximity_ticks,
                });
            }

            let mut next = st.clone();
            next.habitat_judge_digest = up.new_judge_digest;
            next.pinned_model_weights_root = up.new_model_weights_root;
            next.active_safety_and_privacy_floors = up.new_floors.clone();
            next.revert_window_steps = up.new_revert_window_steps;
            next.custodian_quorum_epoch = up.new_custodian_epoch;
            Ok(next)
        }
        SheTurn::RevokeOrAttenuateMandate(rev) => {
            if rev.new_budget_cap > st.remaining_mandate_budget {
                return Err(SheRefusal::MandateAmplificationRefused);
            }
            if rev.new_max_proximity_ticks == 0
                || rev.new_max_proximity_ticks > st.max_proximity_ticks
            {
                return Err(SheRefusal::ProximityWideningRefused {
                    proposed_ticks: rev.new_max_proximity_ticks,
                    current_max_ticks: st.max_proximity_ticks,
                });
            }
            if !rev
                .newly_revoked_custodians
                .iter()
                .all(|&c| c < st.custodian_total_n)
            {
                return Err(SheRefusal::DuplicateOrOutOfRangeSigner);
            }

            let mut next = st.clone();
            next.remaining_mandate_budget = rev.new_budget_cap;
            next.max_proximity_ticks = rev.new_max_proximity_ticks;
            for &c in &rev.newly_revoked_custodians {
                if !next.revoked_custodians.contains(&c) {
                    next.revoked_custodians.push(c);
                }
            }
            Ok(next)
        }
    }
}

/// Execute a multi-turn sequence of [`SheTurn`]s, returning `(step_index, refusal)` on failure.
pub fn run_she_trace(st: &SheState, turns: &[SheTurn]) -> Result<SheState, (usize, SheRefusal)> {
    let mut cur = st.clone();
    for (idx, turn) in turns.iter().enumerate() {
        cur = apply_she_turn(&cur, turn).map_err(|e| (idx, e))?;
    }
    Ok(cur)
}

// ---------------------------------------------------------------------------
// 3. Sealed Integration with `obend-oracles-e2ee` TLSNotary & TEE Receipts
// ---------------------------------------------------------------------------

/// Sealed oracle ingress token binding verified TLSNotary / `calltree` / E2EE + TEE hardware
/// evidence to a monotone sensor sequence number.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedOracleIngress {
    mono_seq: u64,
    seal_digest: [u8; 32],
    attested_gpu_count: u64,
}

impl SealedOracleIngress {
    pub const fn mono_seq(&self) -> u64 {
        self.mono_seq
    }

    pub const fn seal_digest(&self) -> [u8; 32] {
        self.seal_digest
    }

    pub const fn attested_gpu_count(&self) -> u64 {
        self.attested_gpu_count
    }

    /// Seal a verified TLSNotary HTTPS transcript alongside verified CPU + GPU TEE tokens.
    pub fn from_tlsn_and_tee(
        mono_seq: u64,
        transcript: &VerifiedHttpsTranscript,
        cpu_tee: &VerifiedTeeEvidence,
        gpu_tees: &[VerifiedTeeEvidence],
    ) -> Result<Self, SheRefusal> {
        if matches!(cpu_tee.vendor(), TeeVendor::NvidiaGpu(_))
            || matches!(
                (cpu_tee.vendor(), cpu_tee.tcb_posture()),
                (
                    TeeVendor::AmdSevSnp(_) | TeeVendor::IntelTdx,
                    TcbPosture::NoPolicyOnPlatform
                )
            )
        {
            return Err(SheRefusal::OracleEvidenceBindingMismatch);
        }
        let mut seen_gpu_keys = std::collections::BTreeSet::new();
        for gpu in gpu_tees {
            if !matches!(gpu.vendor(), TeeVendor::NvidiaGpu(_))
                || gpu.tcb_posture() != TcbPosture::VerifiedFloor
                || gpu.gpu_fwid().is_none()
                || !seen_gpu_keys.insert(gpu.leaf_spki_sha256())
            {
                return Err(SheRefusal::OracleEvidenceBindingMismatch);
            }
        }
        Ok(Self {
            mono_seq,
            seal_digest: transcript.transcript_digest(),
            attested_gpu_count: gpu_tees.len() as u64,
        })
    }

    /// Seal a verified multi-hop `calltree` DAG root digest.
    pub fn from_verified_calltree(mono_seq: u64, tree: &VerifiedCallTree) -> Self {
        Self {
            mono_seq,
            seal_digest: tree.root_digest(),
            attested_gpu_count: 0,
        }
    }

    /// Seal a verified E2EE prompt/response channel bound to CPU + GPU TEE evidence.
    pub fn from_verified_e2ee_channel(
        mono_seq: u64,
        channel: &VerifiedE2eeChannel,
        cpu_tee: &VerifiedTeeEvidence,
    ) -> Result<Self, SheRefusal> {
        if !ct_eq(&channel.cpu_evidence_digest(), &cpu_tee.evidence_digest()) {
            return Err(SheRefusal::OracleEvidenceBindingMismatch);
        }
        Ok(Self {
            mono_seq,
            seal_digest: channel.channel_binding_id(),
            attested_gpu_count: channel.gpu_fwids().len() as u64,
        })
    }
}

/// Apply an actuation turn strictly gated on a [`SealedOracleIngress`] receipt produced by
/// `obend-oracles-e2ee`'s TLSNotary / E2EE / TEE verifiers.
pub fn apply_oracle_attested_actuation(
    state: &SheState,
    ingress: &SealedOracleIngress,
    proposal: &ActuationTurnProposal,
) -> Result<SheState, SheRefusal> {
    if proposal.sensor_seq != ingress.mono_seq()
        || !ct_eq(&proposal.sensor_seal_digest, &ingress.seal_digest())
        || proposal.attested_gpu_count > ingress.attested_gpu_count()
    {
        return Err(SheRefusal::OracleEvidenceBindingMismatch);
    }
    apply_she_turn(
        state,
        &SheTurn::ProposeAndSettleActuation(proposal.clone()),
    )
}
