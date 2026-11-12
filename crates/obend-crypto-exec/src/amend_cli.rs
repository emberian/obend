//! Canonical `ZkBiscuit` Attenuation + Policy/Amendment Commitment + `DualPcsReceipt`
//! Verifier over Strict RFC 8949 §4.2 Deterministic CBOR (`no_std + alloc`, `#![forbid(unsafe_code)]`).
//!
//! Cryptographically binds:
//! 1. **Monotone `ZkBiscuit` capability chains** (`Obend.Polis.ZkBiscuit`): `cSHAKE256`-chained
//!    hop nullifiers, monotone rights attenuation (`child & !parent == 0`), monotone epoch caveats,
//!    and $O(\log N)$ ancestor-cone revocation checks (`revoke_ancestor_kills_cone`).
//! 2. **Length-framed `AmendmentProposal` commitments**: policy digest, amendment digest, epoch,
//!    monotonic anti-replay nonce, required rights bitmask, and target organ tag.
//! 3. **Dual-Track `DualPcsReceipt` (`Canopy` Track H + `PikkuFold`/`Akita` Track L)**: bound via
//!    `FenziTranscript` (`Unbound -> RelationBound -> InstanceBound`) to `(vk_digest, circuit_desc)`
//!    derived from the verified `ZkBiscuit` leaf lineage and `AmendmentProposal` digest.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::canopy::{CanopyError, CanopyParams, DomainKind, HashInvocationStats, ProximityRegime};
use crate::det_cbor::{
    CborValue, DetCborError, DualPcsReceipt, decode_det_cbor, encode_det_cbor,
    prove_dual_pcs_receipt, verify_dual_pcs_receipt,
};
use crate::goldilocks::Goldilocks;
use crate::pikkufold::{LatticeError, LatticeParams};
use crate::transcript::{cshake256_32, leb128};

/// Canonical wire schema version for `SignedAmendmentEnvelope`.
pub const AMENDMENT_ENVELOPE_SCHEMA_VERSION: u64 = 2;

/// Domain-separated Fiat-Shamir protocol identifier for `SignedAmendmentEnvelope`.
pub const AMENDMENT_PROTOCOL_ID: &str = "OBEND.POLIS.AMEND_ZK_BISCUIT/v2";

const AMEND_PROPOSAL_CUSTOM: &[u8] = b"OBEND.AMEND.PROPOSAL_COMMIT/v1";
const AMEND_VK_CUSTOM: &[u8] = b"OBEND.AMEND.VK_DIGEST/v1";
const BISCUIT_LINEAGE_CUSTOM: &[u8] = b"OBEND.POLIS.LINEAGE/v1";
const BISCUIT_NUL_CUSTOM: &[u8] = b"OBEND.POLIS.NUL/v1";
/// The MAC profile requires a verifier-held secret. Public authority identifiers are not keys.
pub fn root_authority_id(root_secret: &[u8; 32]) -> [u8; 32] {
    cshake256_32(b"OBEND.POLIS.ROOT_AUTHORITY/v1", root_secret)
}

fn authenticate_hop(root_secret: &[u8; 32], nullifier: &[u8; 32]) -> [u8; 32] {
    let mut pre = Vec::new();
    frame_bytes(&mut pre, root_secret);
    frame_bytes(&mut pre, nullifier);
    cshake256_32(b"OBEND.POLIS.HOP_MAC/v1", &pre)
}

fn tags_equal(a: &[u8; 32], b: &[u8; 32]) -> bool {
    a.iter().zip(b).fold(0u8, |diff, (x, y)| diff | (x ^ y)) == 0
}

/// Stable machine-readable refusal codes emitted by the `ZkBiscuit` + `DualPcsReceipt` verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefusalCode {
    NonCanonicalCbor,
    ReplayedNonce,
    ForgedAttenuationHop,
    RevokedLineage,
    InsufficientRights,
    AmendmentBindingMismatch,
    TamperedCanopyOpening,
    TamperedPikkufoldOpening,
    TranscriptOrSumcheckMismatch,
}

impl RefusalCode {
    /// Stable uppercase identifier for structured JSON CLI output and cross-language harnesses.
    #[inline]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NonCanonicalCbor => "REFUSED_NON_CANONICAL_CBOR",
            Self::ReplayedNonce => "REFUSED_REPLAYED_NONCE",
            Self::ForgedAttenuationHop => "REFUSED_FORGED_ATTENUATION_HOP",
            Self::RevokedLineage => "REFUSED_REVOKED_LINEAGE",
            Self::InsufficientRights => "REFUSED_INSUFFICIENT_RIGHTS",
            Self::AmendmentBindingMismatch => "REFUSED_AMENDMENT_BINDING_MISMATCH",
            Self::TamperedCanopyOpening => "REFUSED_TAMPERED_CANOPY_OPENING",
            Self::TamperedPikkufoldOpening => "REFUSED_TAMPERED_PIKKUFOLD_OPENING",
            Self::TranscriptOrSumcheckMismatch => "REFUSED_SUMCHECK_OR_TRANSCRIPT_MISMATCH",
        }
    }
}

impl fmt::Display for RefusalCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Typed verification refusal distinguishing CBOR canonicality, replay, biscuit attenuation,
/// revocation, policy/amendment binding, Track H (`Canopy`), and Track L (`PikkuFold`/`Akita`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AmendRefusal {
    NonCanonicalCbor(DetCborError),
    ReplayedNonce {
        nonce: u64,
    },
    ForgedAttenuationHop {
        hop_index: usize,
        reason: &'static str,
    },
    RevokedLineage {
        hop_index: usize,
        channel_id: u64,
    },
    InsufficientRights {
        effective_rights: u64,
        required_rights: u64,
    },
    AmendmentBindingMismatch {
        field: &'static str,
    },
    TamperedCanopyOpening(CanopyError),
    TamperedPikkufoldOpening(LatticeError),
    TranscriptOrSumcheckMismatch(DetCborError),
}

impl AmendRefusal {
    /// Canonical `RefusalCode` tag for this failure.
    #[inline]
    pub const fn code(&self) -> RefusalCode {
        match self {
            Self::NonCanonicalCbor(_) => RefusalCode::NonCanonicalCbor,
            Self::ReplayedNonce { .. } => RefusalCode::ReplayedNonce,
            Self::ForgedAttenuationHop { .. } => RefusalCode::ForgedAttenuationHop,
            Self::RevokedLineage { .. } => RefusalCode::RevokedLineage,
            Self::InsufficientRights { .. } => RefusalCode::InsufficientRights,
            Self::AmendmentBindingMismatch { .. } => RefusalCode::AmendmentBindingMismatch,
            Self::TamperedCanopyOpening(_) => RefusalCode::TamperedCanopyOpening,
            Self::TamperedPikkufoldOpening(_) => RefusalCode::TamperedPikkufoldOpening,
            Self::TranscriptOrSumcheckMismatch(_) => RefusalCode::TranscriptOrSumcheckMismatch,
        }
    }
}

impl fmt::Display for AmendRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {:?}", self.code().as_str(), self)
    }
}

/// Fast Dual-Track profile (`v = 8`, `N = 256` Goldilocks elements).
/// Canopy uses blowup 4 and 256 queries (128 query-error bits); this is not
/// a claim of 128-bit total soundness over the 64-bit base field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastReceiptProfile {
    pub num_vars: usize,
    pub canopy_params: CanopyParams,
    pub lattice_params: LatticeParams,
}

impl FastReceiptProfile {
    /// Construct the standard sub-5ms CLI authority-verification profile (`v = 8`).
    pub fn sub5ms_default() -> Self {
        let canopy_params = CanopyParams::new_with_min_soundness(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            256,
            128,
        )
        .expect("valid PrimeField UDR CanopyParams");
        // 2^8 = 256 Goldilocks elements = 1024 16-bit limbs = 16 RingElems (degree 64)
        let lattice_params = LatticeParams::expand_from_seed(*b"OBEND.AMEND.LATTICE.CRS.SEED/v01", 2, 16)
            .expect("valid R_q64 LatticeParams (2x16)");
        Self {
            num_vars: 8,
            canopy_params,
            lattice_params,
        }
    }

    /// Use the same 128 query-error-bit profile at `v = 10` (`N = 1024`).
    pub fn query_128bit_v10() -> Self {
        let canopy_params = CanopyParams::default_128bit();
        // 2^10 = 1024 Goldilocks elements = 4096 16-bit limbs = 64 RingElems (degree 64)
        let lattice_params = LatticeParams::expand_from_seed(*b"OBEND.AMEND.LATTICE.CRS.V10/v001", 2, 64)
            .expect("valid R_q64 LatticeParams (2x64)");
        Self {
            num_vars: 10,
            canopy_params,
            lattice_params,
        }
    }
}

fn frame_bytes(dst: &mut Vec<u8>, bytes: &[u8]) {
    dst.extend_from_slice(&leb128(bytes.len()));
    dst.extend_from_slice(bytes);
}

fn frame_u64(dst: &mut Vec<u8>, val: u64) {
    dst.extend_from_slice(&val.to_be_bytes());
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

fn decode_hash32(val: &CborValue, field: &'static str) -> Result<[u8; 32], DetCborError> {
    let b = val.as_bytes()?;
    if b.len() != 32 {
        return Err(DetCborError::SchemaMismatch(alloc::format!(
            "field {field} expected 32 bytes, got {}",
            b.len()
        )));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(b);
    Ok(out)
}

/// Canonical finite Law clause: the same 16-configuration truth table as Lean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawClause { pub name: String, pub priority: u64, pub allowed: u16 }

fn law_clauses_bytes(clauses: &[LawClause]) -> Vec<u8> {
    let mut out = leb128(clauses.len());
    for c in clauses {
        let mut row = Vec::new();
        frame_bytes(&mut row, c.name.as_bytes());
        frame_bytes(&mut row, &leb128(c.priority as usize));
        frame_bytes(&mut row, &c.allowed.to_be_bytes());
        frame_bytes(&mut out, &row);
    }
    out
}

/// Transparent execution witness of pointwise revision. The selected model is checked
/// against every candidate, including deterministic tie-breaking and immutable bedrock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmendmentExecution {
    pub slot: u64,
    pub old: Vec<LawClause>,
    pub proposed: Vec<LawClause>,
    pub bedrock: u16,
    pub bedrock_seed: u8,
    pub selected: u8,
}

impl AmendmentExecution {
    pub fn turn_digest(&self) -> [u8; 32] {
        let mut pre = Vec::new();
        frame_bytes(&mut pre, &leb128(16));
        frame_bytes(&mut pre, &leb128(self.slot as usize));
        frame_bytes(&mut pre, &law_clauses_bytes(&self.proposed));
        cshake256_32(b"OBEND.LAW.AMENDMENT_TURN/v1", &pre)
    }
    pub fn bedrock_digest(&self) -> [u8; 32] {
        let mut pre = Vec::new();
        frame_bytes(&mut pre, &leb128(16));
        frame_bytes(&mut pre, &self.bedrock.to_be_bytes());
        frame_bytes(&mut pre, &leb128(self.bedrock_seed as usize));
        cshake256_32(b"OBEND.LAW.BEDROCK/v1", &pre)
    }
    pub fn prior_digest(&self) -> [u8; 32] {
        cshake256_32(b"OBEND.LAW.PRIOR/v1", &law_clauses_bytes(&self.old))
    }
    fn residuals(&self) -> Result<Vec<Goldilocks>, AmendRefusal> {
        if self.selected >= 16 || self.bedrock_seed >= 16 {
            return Err(AmendRefusal::AmendmentBindingMismatch { field: "model_index" });
        }
        let admissible = |v: u8| self.bedrock & (1 << v) != 0 &&
            self.proposed.iter().all(|c| c.allowed & (1 << v) != 0);
        // u128 prevents a single u64 priority from wrapping the loss comparison.
        let loss = |v: u8| self.old.iter().filter(|c| c.allowed & (1 << v) == 0)
            .map(|c| c.priority as u128 + 1).sum::<u128>();
        let mut ok = vec![self.bedrock & (1 << self.bedrock_seed) != 0, admissible(self.selected)];
        for v in 0..16 {
            ok.push(!admissible(v) || (loss(self.selected), self.selected) <= (loss(v), v));
        }
        Ok(ok.into_iter().map(|b| if b { Goldilocks::ZERO } else { Goldilocks::ONE }).collect())
    }
    fn to_cbor_value(&self) -> CborValue {
        let clauses = |cs: &[LawClause]| CborValue::Array(cs.iter().map(|c|
            CborValue::Array(vec![CborValue::Text(c.name.clone()), CborValue::Unsigned(c.priority),
                CborValue::Unsigned(c.allowed as u64)])).collect());
        CborValue::Array(vec![CborValue::Unsigned(self.slot), clauses(&self.old), clauses(&self.proposed),
            CborValue::Unsigned(self.bedrock as u64), CborValue::Unsigned(self.bedrock_seed as u64),
            CborValue::Unsigned(self.selected as u64)])
    }
    fn from_cbor_value(v: &CborValue) -> Result<Self, DetCborError> {
        let a = v.as_array()?;
        if a.len() != 6 { return Err(DetCborError::UnexpectedFieldCount { expected: 6, actual: a.len() }); }
        let clauses = |v: &CborValue| -> Result<Vec<LawClause>, DetCborError> {
            v.as_array()?.iter().map(|v| {
                let c = v.as_array()?;
                if c.len() != 3 { return Err(DetCborError::UnexpectedFieldCount { expected: 3, actual: c.len() }); }
                Ok(LawClause { name: String::from(c[0].as_text()?), priority: c[1].as_u64()?,
                    allowed: u16::try_from(c[2].as_u64()?).map_err(|_| DetCborError::LengthOverflow)? })
            }).collect()
        };
        Ok(Self { slot: a[0].as_u64()?, old: clauses(&a[1])?, proposed: clauses(&a[2])?,
            bedrock: u16::try_from(a[3].as_u64()?).map_err(|_| DetCborError::LengthOverflow)?,
            bedrock_seed: u8::try_from(a[4].as_u64()?).map_err(|_| DetCborError::LengthOverflow)?,
            selected: u8::try_from(a[5].as_u64()?).map_err(|_| DetCborError::LengthOverflow)? })
    }
}

/// Canonical receipt commitment, including the actual support and tile-frame commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawReceipt {
    pub slot: u64,
    pub accepted: bool,
    pub selected: u8,
    pub retained: Vec<LawClause>,
    pub refused_cost: u64,
    pub evicted: Vec<LawClause>,
    pub skipped: Vec<String>,
    pub frames: Vec<(u64, u64)>,
    pub turn_digest: [u8; 32],
    pub bedrock_digest: [u8; 32],
    pub support_digest: [u8; 32],
}
impl LawReceipt {
    pub fn digest(&self) -> [u8; 32] {
        let mut rev = vec![u8::from(!self.accepted)];
        frame_bytes(&mut rev, &leb128(self.selected as usize));
        frame_bytes(&mut rev, &law_clauses_bytes(&self.retained));
        if !self.accepted { frame_bytes(&mut rev, &leb128(self.refused_cost as usize)); }
        let mut skipped = leb128(self.skipped.len());
        for name in &self.skipped { frame_bytes(&mut skipped, name.as_bytes()); }
        let mut frames = leb128(self.frames.len());
        for (payload, crc) in &self.frames {
            frame_bytes(&mut frames, &payload.to_be_bytes()); frame_bytes(&mut frames, &crc.to_be_bytes());
        }
        let mut pre = Vec::new();
        for field in [&leb128(self.slot as usize), &rev, &law_clauses_bytes(&self.evicted),
            &skipped, &frames, &self.turn_digest.to_vec(), &self.bedrock_digest.to_vec(), &self.support_digest.to_vec()] {
            frame_bytes(&mut pre, field);
        }
        cshake256_32(b"OBEND.LAW.AMEND_RECEIPT/v1", &pre)
    }
}

/// Inhabited finite-law example used by the CLI and cross-language vectors.
pub fn example_amendment_execution() -> AmendmentExecution {
    AmendmentExecution { slot: 2, old: vec![LawClause { name: String::from("fee"), priority: 3, allowed: 0xaaaa }],
        proposed: vec![LawClause { name: String::from("recover"), priority: 1, allowed: 0x00c0 }],
        bedrock: 0x00c0, bedrock_seed: 6, selected: 7 }
}

/// Governance/policy amendment commitment payload. Every field is length-framed into
/// `commitment_digest()` (`frame_bytes` / fixed-width BE) so Stage-B binding has zero unframed slack.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmendmentProposal {
    pub policy_digest: [u8; 32],
    pub amendment_digest: [u8; 32],
    pub prior_digest: [u8; 32],
    pub epoch: u64,
    pub nonce: u64,
    pub required_rights: u64,
    pub target_organ: String,
}

impl AmendmentProposal {
    /// Domain-separated 256-bit `cSHAKE256` commitment over all 6 length-framed fields.
    pub fn commitment_digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(128 + self.target_organ.len());
        frame_bytes(&mut buf, &self.policy_digest);
        frame_bytes(&mut buf, &self.amendment_digest);
        frame_bytes(&mut buf, &self.prior_digest);
        frame_u64(&mut buf, self.epoch);
        frame_u64(&mut buf, self.nonce);
        frame_u64(&mut buf, self.required_rights);
        frame_bytes(&mut buf, self.target_organ.as_bytes());
        cshake256_32(AMEND_PROPOSAL_CUSTOM, &buf)
    }

    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
            (CborValue::Text(String::from("prior_digest")), CborValue::Bytes(self.prior_digest.to_vec())),
            (
                CborValue::Text(String::from("amendment_digest")),
                CborValue::Bytes(self.amendment_digest.to_vec()),
            ),
            (
                CborValue::Text(String::from("epoch")),
                CborValue::Unsigned(self.epoch),
            ),
            (
                CborValue::Text(String::from("nonce")),
                CborValue::Unsigned(self.nonce),
            ),
            (
                CborValue::Text(String::from("policy_digest")),
                CborValue::Bytes(self.policy_digest.to_vec()),
            ),
            (
                CborValue::Text(String::from("required_rights")),
                CborValue::Unsigned(self.required_rights),
            ),
            (
                CborValue::Text(String::from("target_organ")),
                CborValue::Text(self.target_organ.clone()),
            ),
        ])
    }

    pub fn from_cbor_value(val: &CborValue) -> Result<Self, DetCborError> {
        let m = val.as_map()?;
        if m.len() != 7 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 7,
                actual: m.len(),
            });
        }
        Ok(Self {
            prior_digest: decode_hash32(map_lookup(m, "prior_digest")?, "prior_digest")?,
            policy_digest: decode_hash32(map_lookup(m, "policy_digest")?, "policy_digest")?,
            amendment_digest: decode_hash32(map_lookup(m, "amendment_digest")?, "amendment_digest")?,
            epoch: map_lookup(m, "epoch")?.as_u64()?,
            nonce: map_lookup(m, "nonce")?.as_u64()?,
            required_rights: map_lookup(m, "required_rights")?.as_u64()?,
            target_organ: String::from(map_lookup(m, "target_organ")?.as_text()?),
        })
    }
}

/// Single attenuation block in a `ZkBiscuitChain` (`Obend.Polis.ZkBiscuit.Block` Exec mirror).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BiscuitHop {
    pub hop_index: u32,
    pub channel_id: u64,
    pub rights_mask: u64,
    pub caveat_epoch_max: u64,
    pub attenuation_note: String,
    pub parent_lineage: [u8; 32],
    pub hop_nullifier: [u8; 32],
    pub lineage_digest: [u8; 32],
    pub authentication: [u8; 32],
}

impl BiscuitHop {
    /// Exact Lean `Block.encode` and `rootPreimage`/`stepPreimage` schema.
    /// Epoch is an atom caveat; this execution profile interprets that atom as an epoch limit.
    pub fn compute_lineage(root_authority_id: &[u8; 32], hop_index: u32,
        channel_id: u64, rights_mask: u64, caveat_epoch_max: u64,
        attenuation_note: &str, parent_lineage: &[u8; 32]) -> [u8; 32] {
        let mut holder = Vec::new();
        frame_bytes(&mut holder, root_authority_id);
        frame_bytes(&mut holder, &hop_index.to_be_bytes());
        frame_bytes(&mut holder, attenuation_note.as_bytes());
        let mut block = rights_mask.to_be_bytes().to_vec();
        block.push(0); // Caveat.atom
        block.extend_from_slice(&leb128(caveat_epoch_max as usize));
        frame_bytes(&mut block, &holder);
        frame_bytes(&mut block, &channel_id.to_be_bytes());
        let mut pre = vec![if hop_index == 0 { 0 } else { 1 }];
        if hop_index != 0 { frame_bytes(&mut pre, parent_lineage); }
        pre.extend_from_slice(&block);
        cshake256_32(BISCUIT_LINEAGE_CUSTOM, &pre)
    }

    pub fn compute_nullifier(root_authority_id: &[u8; 32], hop_index: u32,
        channel_id: u64, rights_mask: u64, caveat_epoch_max: u64,
        attenuation_note: &str, parent_lineage: &[u8; 32]) -> [u8; 32] {
        let lineage = Self::compute_lineage(root_authority_id, hop_index, channel_id, rights_mask,
            caveat_epoch_max, attenuation_note, parent_lineage);
        let mut pre = vec![1];
        pre.extend_from_slice(&lineage);
        cshake256_32(BISCUIT_NUL_CUSTOM, &pre)
    }

    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
            (CborValue::Text(String::from("lineage_digest")), CborValue::Bytes(self.lineage_digest.to_vec())),
            (CborValue::Text(String::from("authentication")), CborValue::Bytes(self.authentication.to_vec())),
            (
                CborValue::Text(String::from("attenuation_note")),
                CborValue::Text(self.attenuation_note.clone()),
            ),
            (
                CborValue::Text(String::from("caveat_epoch_max")),
                CborValue::Unsigned(self.caveat_epoch_max),
            ),
            (
                CborValue::Text(String::from("channel_id")),
                CborValue::Unsigned(self.channel_id),
            ),
            (
                CborValue::Text(String::from("hop_index")),
                CborValue::Unsigned(self.hop_index as u64),
            ),
            (
                CborValue::Text(String::from("hop_nullifier")),
                CborValue::Bytes(self.hop_nullifier.to_vec()),
            ),
            (
                CborValue::Text(String::from("parent_lineage")),
                CborValue::Bytes(self.parent_lineage.to_vec()),
            ),
            (
                CborValue::Text(String::from("rights_mask")),
                CborValue::Unsigned(self.rights_mask),
            ),
        ])
    }

    pub fn from_cbor_value(val: &CborValue) -> Result<Self, DetCborError> {
        let m = val.as_map()?;
        if m.len() != 9 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 9,
                actual: m.len(),
            });
        }
        let hop_index_u64 = map_lookup(m, "hop_index")?.as_u64()?;
        let hop_index = u32::try_from(hop_index_u64).map_err(|_| DetCborError::LengthOverflow)?;
        Ok(Self {
            lineage_digest: decode_hash32(map_lookup(m, "lineage_digest")?, "lineage_digest")?,
            authentication: decode_hash32(map_lookup(m, "authentication")?, "authentication")?,
            hop_index,
            channel_id: map_lookup(m, "channel_id")?.as_u64()?,
            rights_mask: map_lookup(m, "rights_mask")?.as_u64()?,
            caveat_epoch_max: map_lookup(m, "caveat_epoch_max")?.as_u64()?,
            attenuation_note: String::from(map_lookup(m, "attenuation_note")?.as_text()?),
            parent_lineage: decode_hash32(map_lookup(m, "parent_lineage")?, "parent_lineage")?,
            hop_nullifier: decode_hash32(map_lookup(m, "hop_nullifier")?, "hop_nullifier")?,
        })
    }
}

///Sorted binary-search revocation set over 256-bit hop nullifiers and 64-bit CapTP channel IDs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RevocationSet {
    revoked_nullifiers: Vec<[u8; 32]>,
    revoked_channels: Vec<u64>,
}

impl RevocationSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn revoke_nullifier(&mut self, nullifier: [u8; 32]) {
        if let Err(pos) = self.revoked_nullifiers.binary_search(&nullifier) {
            self.revoked_nullifiers.insert(pos, nullifier);
        }
    }

    pub fn revoke_channel(&mut self, channel_id: u64) {
        if let Err(pos) = self.revoked_channels.binary_search(&channel_id) {
            self.revoked_channels.insert(pos, channel_id);
        }
    }

    #[inline]
    pub fn is_nullifier_revoked(&self, nullifier: &[u8; 32]) -> bool {
        self.revoked_nullifiers.binary_search(nullifier).is_ok()
    }

    #[inline]
    pub fn is_channel_revoked(&self, channel_id: u64) -> bool {
        self.revoked_channels.binary_search(&channel_id).is_ok()
    }
}

/// Summary extracted by `ZkBiscuitChain::verify_chain`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedBiscuitLineage {
    pub root_authority_id: [u8; 32],
    pub leaf_nullifier: [u8; 32],
    pub effective_rights: u64,
    pub caveat_epoch_max: u64,
    pub hop_count: usize,
}

/// Monotone `ZkBiscuit` attenuation chain (`Obend.Polis.ZkBiscuit.foldChain` Exec mirror).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkBiscuitChain {
    pub root_authority_id: [u8; 32],
    pub hops: Vec<BiscuitHop>,
}

impl ZkBiscuitChain {
    /// Mint with the secret MAC authority key; the public identifier is derived, never supplied.
    pub fn mint_root(
        root_secret: [u8; 32],
        channel_id: u64,
        initial_rights: u64,
        caveat_epoch_max: u64,
        note: &str,
    ) -> Self {
        let root_authority_id = root_authority_id(&root_secret);
        let parent_lineage = [0u8; 32];
        let hop_nullifier = BiscuitHop::compute_nullifier(
            &root_authority_id,
            0,
            channel_id,
            initial_rights,
            caveat_epoch_max,
            note,
            &parent_lineage,
        );
        Self {
            root_authority_id,
            hops: vec![BiscuitHop {
                hop_index: 0,
                channel_id,
                rights_mask: initial_rights,
                caveat_epoch_max,
                attenuation_note: String::from(note),
                parent_lineage,
                hop_nullifier,
                lineage_digest: BiscuitHop::compute_lineage(&root_authority_id, 0, channel_id,
                    initial_rights, caveat_epoch_max, note, &parent_lineage),
                authentication: authenticate_hop(&root_secret, &hop_nullifier),
            }],
        }
    }

    /// Append a strictly monotone attenuated child hop (`attenuated_rights ⊆ parent.rights_mask`
    /// and `caveat_epoch_max <= parent.caveat_epoch_max`).
    pub fn attenuate(
        &self,
        root_secret: &[u8; 32],
        channel_id: u64,
        attenuated_rights: u64,
        caveat_epoch_max: u64,
        note: &str,
    ) -> Result<Self, AmendRefusal> {
        self.verify_authenticated(root_secret, &RevocationSet::new())?;
        let Some(prev) = self.hops.last() else {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: 0,
                reason: "cannot attenuate empty chain",
            });
        };
        let next_idx = self.hops.len();
        if (attenuated_rights & !prev.rights_mask) != 0 {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: next_idx,
                reason: "rights escalation forbidden by monotone attenuation",
            });
        }
        if caveat_epoch_max > prev.caveat_epoch_max {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: next_idx,
                reason: "caveat_epoch_max relaxation forbidden",
            });
        }
        let hop_index = u32::try_from(next_idx).map_err(|_| AmendRefusal::ForgedAttenuationHop {
            hop_index: next_idx,
            reason: "hop index overflow",
        })?;
        let parent_lineage = prev.lineage_digest;
        let hop_nullifier = BiscuitHop::compute_nullifier(
            &self.root_authority_id,
            hop_index,
            channel_id,
            attenuated_rights,
            caveat_epoch_max,
            note,
            &parent_lineage,
        );
        let mut next = self.clone();
        next.hops.push(BiscuitHop {
            hop_index,
            channel_id,
            rights_mask: attenuated_rights,
            caveat_epoch_max,
            attenuation_note: String::from(note),
            parent_lineage,
            hop_nullifier,
            lineage_digest: BiscuitHop::compute_lineage(&self.root_authority_id, hop_index, channel_id,
                attenuated_rights, caveat_epoch_max, note, &parent_lineage),
            authentication: authenticate_hop(root_secret, &hop_nullifier),
        });
        Ok(next)
    }

    /// Authenticate every delegation before accepting its rights. In this MAC profile
    /// delegation is authorized by the root; possession of public wire bytes grants no signing power.
    pub fn verify_authenticated(&self, root_secret: &[u8; 32], revocations: &RevocationSet)
        -> Result<VerifiedBiscuitLineage, AmendRefusal>
    {
        if self.root_authority_id != root_authority_id(root_secret) {
            return Err(AmendRefusal::AmendmentBindingMismatch { field: "root_authority_id" });
        }
        let lineage = self.verify_chain(revocations)?;
        for (idx, hop) in self.hops.iter().enumerate() {
            if !tags_equal(&hop.authentication, &authenticate_hop(root_secret, &hop.hop_nullifier)) {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx, reason: "invalid authority MAC",
                });
            }
        }
        Ok(lineage)
    }

    /// Fold and verify every hop's parent pointer, `cSHAKE256` nullifier, monotone rights/epoch
    /// invariants, and ancestor-cone non-revocation.
    pub fn verify_chain(
        &self,
        revocations: &RevocationSet,
    ) -> Result<VerifiedBiscuitLineage, AmendRefusal> {
        if self.hops.is_empty() {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: 0,
                reason: "empty biscuit hop list",
            });
        }
        let mut prev_nullifier = [0u8; 32];
        let mut prev_lineage = [0u8; 32];
        let mut prev_rights = u64::MAX;
        let mut prev_epoch_max = u64::MAX;

        for (idx, hop) in self.hops.iter().enumerate() {
            if hop.hop_index as usize != idx {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "non-contiguous hop_index",
                });
            }
            if hop.parent_lineage != prev_lineage {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "parent_lineage mismatch",
                });
            }
            if idx > 0 && (hop.rights_mask & !prev_rights) != 0 {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "child rights_mask escalates parent rights_mask",
                });
            }
            if idx > 0 && hop.caveat_epoch_max > prev_epoch_max {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "child caveat_epoch_max exceeds parent caveat_epoch_max",
                });
            }
            let expected_nullifier = BiscuitHop::compute_nullifier(
                &self.root_authority_id,
                hop.hop_index,
                hop.channel_id,
                hop.rights_mask,
                hop.caveat_epoch_max,
                &hop.attenuation_note,
                &hop.parent_lineage,
            );
            if hop.hop_nullifier != expected_nullifier || hop.lineage_digest != BiscuitHop::compute_lineage(
                &self.root_authority_id, hop.hop_index, hop.channel_id, hop.rights_mask,
                hop.caveat_epoch_max, &hop.attenuation_note, &hop.parent_lineage) {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "hop_nullifier cSHAKE256 mismatch",
                });
            }
            if revocations.is_nullifier_revoked(&hop.hop_nullifier)
                || revocations.is_channel_revoked(hop.channel_id)
            {
                return Err(AmendRefusal::RevokedLineage {
                    hop_index: idx,
                    channel_id: hop.channel_id,
                });
            }
            prev_nullifier = hop.hop_nullifier;
            prev_lineage = hop.lineage_digest;
            prev_rights = hop.rights_mask;
            prev_epoch_max = hop.caveat_epoch_max;
        }

        Ok(VerifiedBiscuitLineage {
            root_authority_id: self.root_authority_id,
            leaf_nullifier: prev_nullifier,
            effective_rights: prev_rights,
            caveat_epoch_max: prev_epoch_max,
            hop_count: self.hops.len(),
        })
    }

    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
            (
                CborValue::Text(String::from("hops")),
                CborValue::Array(self.hops.iter().map(BiscuitHop::to_cbor_value).collect()),
            ),
            (
                CborValue::Text(String::from("root_authority_id")),
                CborValue::Bytes(self.root_authority_id.to_vec()),
            ),
        ])
    }

    pub fn from_cbor_value(val: &CborValue) -> Result<Self, DetCborError> {
        let m = val.as_map()?;
        if m.len() != 2 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 2,
                actual: m.len(),
            });
        }
        let root_authority_id =
            decode_hash32(map_lookup(m, "root_authority_id")?, "root_authority_id")?;
        let hops = map_lookup(m, "hops")?
            .as_array()?
            .iter()
            .map(BiscuitHop::from_cbor_value)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            root_authority_id,
            hops,
        })
    }
}

/// Derive the canonical `vk_digest` pinning `(root_authority_id, policy_digest)`.
pub fn derive_amendment_vk_digest(
    root_authority_id: &[u8; 32],
    policy_digest: &[u8; 32],
) -> [u8; 32] {
    let mut pre = Vec::with_capacity(72);
    frame_bytes(&mut pre, root_authority_id);
    frame_bytes(&mut pre, policy_digest);
    cshake256_32(AMEND_VK_CUSTOM, &pre)
}

/// Encode the canonical `DetCbor` `circuit_desc` binding `AmendmentProposal` + `VerifiedBiscuitLineage`
/// into Phase 2 (`RelationBound`) of `FenziTranscript`.
pub fn encode_amendment_circuit_desc(
    proposal: &AmendmentProposal,
    lineage: &VerifiedBiscuitLineage,
) -> Result<Vec<u8>, DetCborError> {
    let commit = proposal.commitment_digest();
    let val = CborValue::Map(vec![
        (
            CborValue::Text(String::from("amendment_digest")),
            CborValue::Bytes(proposal.amendment_digest.to_vec()),
        ),
        (
            CborValue::Text(String::from("caveat_epoch_max")),
            CborValue::Unsigned(lineage.caveat_epoch_max),
        ),
        (
            CborValue::Text(String::from("effective_rights")),
            CborValue::Unsigned(lineage.effective_rights),
        ),
        (
            CborValue::Text(String::from("epoch")),
            CborValue::Unsigned(proposal.epoch),
        ),
        (
            CborValue::Text(String::from("leaf_nullifier")),
            CborValue::Bytes(lineage.leaf_nullifier.to_vec()),
        ),
        (
            CborValue::Text(String::from("nonce")),
            CborValue::Unsigned(proposal.nonce),
        ),
        (
            CborValue::Text(String::from("policy_digest")),
            CborValue::Bytes(proposal.policy_digest.to_vec()),
        ),
        (
            CborValue::Text(String::from("proposal_commitment")),
            CborValue::Bytes(commit.to_vec()),
        ),
        (
            CborValue::Text(String::from("root_authority_id")),
            CborValue::Bytes(lineage.root_authority_id.to_vec()),
        ),
    ]);
    encode_det_cbor(&val)
}

/// Public header rows and actual finite-law residuals, padded to a checked domain.
/// There is no PRNG witness. The verifier reconstructs these rows from the opened execution.
pub fn derive_amendment_witness_table(
    execution: &AmendmentExecution,
    proposal: &AmendmentProposal,
    lineage: &VerifiedBiscuitLineage,
    num_vars: usize,
) -> Result<Vec<Goldilocks>, AmendRefusal> {
    if !(8..=24).contains(&num_vars) {
        return Err(AmendRefusal::AmendmentBindingMismatch { field: "num_vars" });
    }
    if proposal.policy_digest != execution.bedrock_digest() ||
        proposal.amendment_digest != execution.turn_digest() || proposal.prior_digest != execution.prior_digest() {
        return Err(AmendRefusal::AmendmentBindingMismatch { field: "law_commitments" });
    }
    let residuals = execution.residuals()?;
    if residuals.iter().any(|r| *r != Goldilocks::ZERO) {
        return Err(AmendRefusal::AmendmentBindingMismatch { field: "pointwise_revision" });
    }
    let mut out = Vec::new();
    // Byte rows preserve all 256 bits without reduction modulo the Goldilocks prime.
    for digest in [proposal.commitment_digest(), lineage.root_authority_id, lineage.leaf_nullifier] {
        out.extend(digest.iter().map(|b| Goldilocks::from_u64_reduced(*b as u64)));
    }
    out.extend(residuals);
    out.resize(1usize << num_vars, Goldilocks::ZERO);
    Ok(out)
}

/// Complete canonical `DetCbor` wire envelope bundling `AmendmentProposal`, `ZkBiscuitChain`,
/// and Dual-Track `DualPcsReceipt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedAmendmentEnvelope {
    pub schema_version: u64,
    pub proposal: AmendmentProposal,
    pub execution: AmendmentExecution,
    pub biscuit_chain: ZkBiscuitChain,
    pub dual_receipt: DualPcsReceipt,
}

impl SignedAmendmentEnvelope {
    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
            (CborValue::Text(String::from("execution")), self.execution.to_cbor_value()),
            (
                CborValue::Text(String::from("biscuit_chain")),
                self.biscuit_chain.to_cbor_value(),
            ),
            (
                CborValue::Text(String::from("dual_receipt")),
                self.dual_receipt.to_cbor_value(),
            ),
            (
                CborValue::Text(String::from("proposal")),
                self.proposal.to_cbor_value(),
            ),
            (
                CborValue::Text(String::from("schema_version")),
                CborValue::Unsigned(self.schema_version),
            ),
        ])
    }

    /// Encode to strict RFC 8949 §4.2 Deterministic CBOR wire bytes.
    pub fn to_det_cbor_bytes(&self) -> Result<Vec<u8>, DetCborError> {
        encode_det_cbor(&self.to_cbor_value())
    }

    /// Decode from strict RFC 8949 §4.2 Deterministic CBOR wire bytes, rejecting any non-canonical
    /// map ordering, duplicate keys, non-minimal integers, floats, or trailing bytes.
    pub fn from_det_cbor_bytes(bytes: &[u8]) -> Result<Self, AmendRefusal> {
        let val = decode_det_cbor(bytes).map_err(AmendRefusal::NonCanonicalCbor)?;
        let m = val.as_map().map_err(AmendRefusal::NonCanonicalCbor)?;
        if m.len() != 5 {
            return Err(AmendRefusal::NonCanonicalCbor(
                DetCborError::UnexpectedFieldCount {
                    expected: 5,
                    actual: m.len(),
                },
            ));
        }
        let schema_version = map_lookup(m, "schema_version")
            .and_then(CborValue::as_u64)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        if schema_version != AMENDMENT_ENVELOPE_SCHEMA_VERSION {
            return Err(AmendRefusal::NonCanonicalCbor(
                DetCborError::SchemaMismatch(String::from("unsupported envelope schema_version")),
            ));
        }
        let proposal = map_lookup(m, "proposal")
            .and_then(AmendmentProposal::from_cbor_value)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        let biscuit_chain = map_lookup(m, "biscuit_chain")
            .and_then(ZkBiscuitChain::from_cbor_value)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        let dual_receipt_val =
            map_lookup(m, "dual_receipt").map_err(AmendRefusal::NonCanonicalCbor)?;
        let dual_receipt_bytes =
            encode_det_cbor(dual_receipt_val).map_err(AmendRefusal::NonCanonicalCbor)?;
        let dual_receipt = DualPcsReceipt::from_det_cbor_bytes(&dual_receipt_bytes)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        let execution = map_lookup(m, "execution").and_then(AmendmentExecution::from_cbor_value)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        let env = Self {
            execution,
            schema_version,
            proposal,
            biscuit_chain,
            dual_receipt,
        };
        // Roundtrip byte-identity check ensures inner domain maps also had canonical key sets.
        let reencoded = env
            .to_det_cbor_bytes()
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        if reencoded != bytes {
            return Err(AmendRefusal::NonCanonicalCbor(
                DetCborError::UnsortedMapKeys,
            ));
        }
        Ok(env)
    }
}

/// Acceptance telemetry returned when `AmendmentVerifierState` accepts an envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmendmentVerifyReport {
    pub proposal_commitment: [u8; 32],
    pub leaf_nullifier: [u8; 32],
    pub canopy_root: [u8; 32],
    pub final_transcript_digest: [u8; 32],
    pub effective_rights: u64,
    pub hop_count: usize,
    pub nonce: u64,
    pub epoch: u64,
    pub hash_stats: HashInvocationStats,
}

/// Stateful verifier tracking sorted accepted nonces (`O(log N)` replay defense),
/// pinned root authority & policy digests, and `RevocationSet`.
#[derive(Clone, PartialEq, Eq)]
pub struct AmendmentVerifierState {
    pub expected_root_authority: [u8; 32],
    root_secret: [u8; 32],
    pub required_rights: u64,
    pub current_epoch: u64,
    pub expected_policy_digest: [u8; 32],
    pub expected_prior_digest: [u8; 32],
    pub revocations: RevocationSet,
    accepted_nonces: Vec<u64>,
}

impl AmendmentVerifierState {
    pub fn new(root_secret: [u8; 32], expected_policy_digest: [u8; 32],
        required_rights: u64, current_epoch: u64, expected_prior_digest: [u8; 32]) -> Self {
        Self {
            expected_root_authority: root_authority_id(&root_secret),
            root_secret,
            required_rights,
            current_epoch,
            expected_policy_digest,
            expected_prior_digest,
            revocations: RevocationSet::new(),
            accepted_nonces: Vec::new(),
        }
    }

    /// Restore a trusted durable replay log. The CLI holds an exclusive file lock.
    pub fn restore_accepted_nonces(&mut self, nonces: &[u64]) {
        self.accepted_nonces.extend_from_slice(nonces);
        self.accepted_nonces.sort_unstable();
        self.accepted_nonces.dedup();
    }

    pub fn restore_spent_nullifiers(&mut self, nullifiers: &[[u8; 32]]) {
        for n in nullifiers { self.revocations.revoke_nullifier(*n); }
    }

    #[inline]
    pub fn accepted_nonces(&self) -> &[u64] {
        &self.accepted_nonces
    }

    /// Verify a already-decoded `SignedAmendmentEnvelope` and atomically record its `nonce`
    /// only if every capability, commitment, and Dual-PCS opening gate passes.
    pub fn verify_and_record_envelope(
        &mut self,
        canopy_params: &CanopyParams,
        lattice_params: &LatticeParams,
        env: &SignedAmendmentEnvelope,
    ) -> Result<AmendmentVerifyReport, AmendRefusal> {
        canopy_params
            .validate_soundness()
            .map_err(AmendRefusal::TamperedCanopyOpening)?;
        // 1. Anti-replay nonce check (O(log N) over sorted nonce log)
        let nonce_insert_pos = match self.accepted_nonces.binary_search(&env.proposal.nonce) {
            Ok(_) => {
                return Err(AmendRefusal::ReplayedNonce {
                    nonce: env.proposal.nonce,
                });
            }
            Err(pos) => pos,
        };

        // 2. Pinned policy & authority check
        if env.proposal.policy_digest != self.expected_policy_digest {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "policy_digest",
            });
        }
        if env.proposal.prior_digest != self.expected_prior_digest {
            return Err(AmendRefusal::AmendmentBindingMismatch { field: "prior_digest" });
        }
        if env.biscuit_chain.root_authority_id != self.expected_root_authority {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "root_authority_id",
            });
        }

        // 3. ZkBiscuit monotone attenuation & ancestor-cone revocation fold
        let lineage = env.biscuit_chain.verify_authenticated(&self.root_secret, &self.revocations)?;

        // 4. Epoch caveat & attenuated rights authorization
        if env.proposal.epoch != self.current_epoch || self.current_epoch > lineage.caveat_epoch_max {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: lineage.hop_count - 1,
                reason: "proposal epoch exceeds leaf caveat_epoch_max",
            });
        }
        let required_rights = self.required_rights | env.proposal.required_rights;
        if (lineage.effective_rights & required_rights) != required_rights
        {
            return Err(AmendRefusal::InsufficientRights {
                effective_rights: lineage.effective_rights,
                required_rights,
            });
        }

        // 5. Cryptographic relation binding (`protocol_id`, `vk_digest`, `circuit_desc`)
        if env.dual_receipt.protocol_id != AMENDMENT_PROTOCOL_ID {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "protocol_id",
            });
        }
        let expected_vk =
            derive_amendment_vk_digest(&self.expected_root_authority, &self.expected_policy_digest);
        if env.dual_receipt.vk_digest != expected_vk {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "vk_digest",
            });
        }
        let expected_circuit_desc = encode_amendment_circuit_desc(&env.proposal, &lineage)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        if env.dual_receipt.circuit_desc != expected_circuit_desc {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "circuit_desc",
            });
        }

        // 6. Dual-Track PCS verification (`Canopy` Track H + `PikkuFold`/`Akita` Track L + Sumcheck)
        let hash_stats =
            verify_dual_pcs_receipt(canopy_params, lattice_params, &env.dual_receipt).map_err(
                |err| match err {
                    DetCborError::CanopyFailure(ce) => AmendRefusal::TamperedCanopyOpening(ce),
                    DetCborError::LatticeFailure(le) => AmendRefusal::TamperedPikkufoldOpening(le),
                    other => AmendRefusal::TranscriptOrSumcheckMismatch(other),
                },
            )?;

        let expected_table = derive_amendment_witness_table(&env.execution, &env.proposal,
            &lineage, env.dual_receipt.num_vars as usize)?;
        let opened_table = crate::pikkufold::unpack_ring_witness_to_goldilocks(
            &env.dual_receipt.lattice_opening, expected_table.len())
            .map_err(AmendRefusal::TamperedPikkufoldOpening)?;
        if opened_table != expected_table {
            return Err(AmendRefusal::AmendmentBindingMismatch { field: "constraint_table" });
        }

        // 7. Commit nonce to anti-replay log only after full verification passes
        self.accepted_nonces
            .insert(nonce_insert_pos, env.proposal.nonce);
        self.revocations.revoke_nullifier(lineage.leaf_nullifier);

        Ok(AmendmentVerifyReport {
            proposal_commitment: env.proposal.commitment_digest(),
            leaf_nullifier: lineage.leaf_nullifier,
            canopy_root: env.dual_receipt.canopy_commitment.root,
            final_transcript_digest: env.dual_receipt.final_transcript_digest,
            effective_rights: lineage.effective_rights,
            hop_count: lineage.hop_count,
            nonce: env.proposal.nonce,
            epoch: env.proposal.epoch,
            hash_stats,
        })
    }

    /// Decode strict `DetCbor` wire bytes and run `verify_and_record_envelope`.
    pub fn verify_and_record_bytes(
        &mut self,
        canopy_params: &CanopyParams,
        lattice_params: &LatticeParams,
        raw_cbor_bytes: &[u8],
    ) -> Result<AmendmentVerifyReport, AmendRefusal> {
        let env = SignedAmendmentEnvelope::from_det_cbor_bytes(raw_cbor_bytes)?;
        self.verify_and_record_envelope(canopy_params, lattice_params, &env)
    }
}

/// Prove a complete `SignedAmendmentEnvelope` binding `proposal` and `biscuit_chain` to a
/// Dual-Track `DualPcsReceipt`.
pub fn prove_amendment_envelope(
    canopy_params: &CanopyParams,
    lattice_params: &LatticeParams,
    num_vars: usize,
    execution: &AmendmentExecution,
    proposal: AmendmentProposal,
    biscuit_chain: ZkBiscuitChain,
    revocations: &RevocationSet,
) -> Result<SignedAmendmentEnvelope, AmendRefusal> {
    canopy_params
        .validate_soundness()
        .map_err(AmendRefusal::TamperedCanopyOpening)?;
    let lineage = biscuit_chain.verify_chain(revocations)?;
    if proposal.epoch > lineage.caveat_epoch_max {
        return Err(AmendRefusal::ForgedAttenuationHop {
            hop_index: lineage.hop_count - 1,
            reason: "proposal epoch exceeds leaf caveat_epoch_max",
        });
    }
    if (lineage.effective_rights & proposal.required_rights) != proposal.required_rights {
        return Err(AmendRefusal::InsufficientRights {
            effective_rights: lineage.effective_rights,
            required_rights: proposal.required_rights,
        });
    }

    let vk_digest =
        derive_amendment_vk_digest(&biscuit_chain.root_authority_id, &proposal.policy_digest);
    let circuit_desc = encode_amendment_circuit_desc(&proposal, &lineage)
        .map_err(AmendRefusal::NonCanonicalCbor)?;
    let table = derive_amendment_witness_table(execution, &proposal, &lineage, num_vars)?;

    let dual_receipt = prove_dual_pcs_receipt(
        AMENDMENT_PROTOCOL_ID,
        vk_digest,
        &circuit_desc,
        canopy_params,
        lattice_params,
        num_vars,
        &table,
    )
    .map_err(|err| match err {
        DetCborError::CanopyFailure(ce) => AmendRefusal::TamperedCanopyOpening(ce),
        DetCborError::LatticeFailure(le) => AmendRefusal::TamperedPikkufoldOpening(le),
        other => AmendRefusal::TranscriptOrSumcheckMismatch(other),
    })?;

    Ok(SignedAmendmentEnvelope {
        execution: execution.clone(),
        schema_version: AMENDMENT_ENVELOPE_SCHEMA_VERSION,
        proposal,
        biscuit_chain,
        dual_receipt,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_fixture() -> (
        FastReceiptProfile,
        [u8; 32],
        [u8; 32],
        AmendmentProposal,
        ZkBiscuitChain,
    ) {
        let profile = FastReceiptProfile::sub5ms_default();
        let root_auth = cshake256_32(b"TEST.ROOT", b"polis-council-root-v1");
        let policy_digest = example_amendment_execution().bedrock_digest();
        let amendment_digest = example_amendment_execution().turn_digest();

        let chain = ZkBiscuitChain::mint_root(root_auth, 1001, 0b1111_1111, 50, "root:council")
            .attenuate(&root_auth, 1002, 0b0011_1111, 40, "delegate:cluster-gov")
            .unwrap()
            .attenuate(&root_auth, 1003, 0b0000_1111, 30, "worker:amend-prover")
            .unwrap();

        let proposal = AmendmentProposal {
            policy_digest,
            amendment_digest,
            prior_digest: example_amendment_execution().prior_digest(),
            epoch: 25,
            nonce: 7,
            required_rights: 0b0000_0101,
            target_organ: String::from("CathedralApex.StageB"),
        };
        (profile, root_auth, policy_digest, proposal, chain)
    }

    #[test]
    fn test_prove_verify_roundtrip_and_nonce_replay_refusal() {
        let (profile, root_auth, policy_digest, proposal, chain) = sample_fixture();
        let revocations = RevocationSet::new();
        let env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &example_amendment_execution(),
            proposal,
            chain,
            &revocations,
        )
        .unwrap();

        let wire = env.to_det_cbor_bytes().unwrap();
        let mut verifier = AmendmentVerifierState::new(root_auth, policy_digest, 5, 25, example_amendment_execution().prior_digest());
        let report = verifier
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .unwrap();
        assert_eq!(report.hop_count, 3);
        assert_eq!(report.nonce, 7);
        assert_eq!(verifier.accepted_nonces(), &[7]);

        // Replaying the exact same valid receipt is deterministically refused!
        let replay_err = verifier
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .unwrap_err();
        assert_eq!(replay_err.code(), RefusalCode::ReplayedNonce);
    }

    #[test]
    fn test_refuses_non_canonical_cbor_forged_hop_revocation_and_tampered_pcs() {
        let (profile, root_auth, policy_digest, proposal, chain) = sample_fixture();
        let revocations = RevocationSet::new();
        let env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &example_amendment_execution(),
            proposal,
            chain,
            &revocations,
        )
        .unwrap();
        let wire = env.to_det_cbor_bytes().unwrap();

        // Case 1: Non-canonical CBOR map key order (`{ "z": 1, "a": 2 }`)
        let mut verifier = AmendmentVerifierState::new(root_auth, policy_digest, 5, 25, example_amendment_execution().prior_digest());
        let raw_unsorted = [0xa2, 0x61, b'z', 0x01, 0x61, b'a', 0x02];
        let cbor_err = verifier
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &raw_unsorted)
            .unwrap_err();
        assert_eq!(cbor_err.code(), RefusalCode::NonCanonicalCbor);

        // Case 2: Trailing garbage byte appended to valid DetCbor wire envelope
        let mut trailing = wire.clone();
        trailing.push(0x00);
        let trail_err = verifier
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &trailing)
            .unwrap_err();
        assert_eq!(trail_err.code(), RefusalCode::NonCanonicalCbor);

        // Case 3: Forged attenuation hop (escalating leaf rights_mask from 0x0F to 0xFF)
        let mut forged_hop_env = env.clone();
        forged_hop_env.biscuit_chain.hops[2].rights_mask = 0xFF;
        let hop_err = verifier
            .verify_and_record_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                &forged_hop_env,
            )
            .unwrap_err();
        assert_eq!(hop_err.code(), RefusalCode::ForgedAttenuationHop);

        // Case 4: Ancestor revocation kills descendant cone (`revoke_ancestor_kills_cone`)
        let mut rev_verifier = AmendmentVerifierState::new(root_auth, policy_digest, 5, 25, example_amendment_execution().prior_digest());
        rev_verifier
            .revocations
            .revoke_nullifier(env.biscuit_chain.hops[1].hop_nullifier);
        let rev_err = rev_verifier
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .unwrap_err();
        assert_eq!(rev_err.code(), RefusalCode::RevokedLineage);

        // Case 5: Policy / amendment digest substitution without re-proving
        let mut swapped_amend_env = env.clone();
        swapped_amend_env.proposal.amendment_digest[0] ^= 0x01;
        let bind_err = verifier
            .verify_and_record_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                &swapped_amend_env,
            )
            .unwrap_err();
        assert_eq!(bind_err.code(), RefusalCode::AmendmentBindingMismatch);

        // Case 6: Tampered Track H (`Canopy`) opened column value
        let mut bad_canopy_env = env.clone();
        bad_canopy_env.dual_receipt.canopy_proof.opened_columns[0].values[0] += Goldilocks::ONE;
        let canopy_err = verifier
            .verify_and_record_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                &bad_canopy_env,
            )
            .unwrap_err();
        assert_eq!(canopy_err.code(), RefusalCode::TamperedCanopyOpening);

        // Case 7: Tampered Track L (`PikkuFold`/`Akita`) final folded witness
        let mut bad_lattice_env = env.clone();
        let mut coeffs = *bad_lattice_env
            .dual_receipt
            .lattice_proof
            .final_witness
            .coeffs();
        coeffs[0] += 1;
        bad_lattice_env.dual_receipt.lattice_proof.final_witness =
            crate::pikkufold::RingElem::from_coeffs(coeffs);
        let lat_err = verifier
            .verify_and_record_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                &bad_lattice_env,
            )
            .unwrap_err();
        assert_eq!(lat_err.code(), RefusalCode::TamperedPikkufoldOpening);

        // Failed verifications must NEVER pollute the anti-replay nonce log!
        assert!(verifier.accepted_nonces().is_empty());
    }
    #[test]
    fn test_authority_policy_constraints_and_domain_bounds() {
        let (profile, secret, policy, proposal, chain) = sample_fixture();
        let execution = example_amendment_execution();
        let env = prove_amendment_envelope(&profile.canopy_params, &profile.lattice_params,
            8, &execution, proposal.clone(), chain.clone(), &RevocationSet::new()).unwrap();
        let public_id = root_authority_id(&secret);
        let mut stranger = ZkBiscuitChain::mint_root(public_id, 1, u64::MAX, u64::MAX, "forged");
        // Give the attacker all public framing/hash operations and the exact trusted label.
        stranger.root_authority_id = public_id;
        let hop = &mut stranger.hops[0];
        hop.lineage_digest = BiscuitHop::compute_lineage(&public_id, 0, 1, u64::MAX,
            u64::MAX, "forged", &[0; 32]);
        hop.hop_nullifier = BiscuitHop::compute_nullifier(&public_id, 0, 1, u64::MAX,
            u64::MAX, "forged", &[0; 32]);
        hop.authentication = authenticate_hop(&public_id, &hop.hop_nullifier);
        assert!(stranger.verify_chain(&RevocationSet::new()).is_ok());
        assert!(matches!(stranger.verify_authenticated(&secret, &RevocationSet::new()),
            Err(AmendRefusal::ForgedAttenuationHop { reason: "invalid authority MAC", .. })));

        let mut forged = env.clone();
        forged.biscuit_chain = stranger;
        forged.proposal.required_rights = 0;
        let mut verifier = AmendmentVerifierState::new(secret, policy, 5, 25, example_amendment_execution().prior_digest());
        assert!(verifier.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &forged).is_err());
        assert!(chain.attenuate(&public_id, 7, 1, 20, "unauthorized").is_err());
        let mut policy_verifier = AmendmentVerifierState::new(secret, policy, 1 << 63, 25, example_amendment_execution().prior_digest());
        assert_eq!(policy_verifier.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &env)
            .unwrap_err().code(), RefusalCode::InsufficientRights);
        let mut wrong_prior = AmendmentVerifierState::new(secret, policy, 5, 25, [0; 32]);
        assert!(matches!(wrong_prior.verify_and_record_envelope(&profile.canopy_params,
            &profile.lattice_params, &env),
            Err(AmendRefusal::AmendmentBindingMismatch { field: "prior_digest" })));
        let mut expired = AmendmentVerifierState::new(secret, policy, 5, 31, example_amendment_execution().prior_digest());
        assert!(expired.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &env).is_err());
        let mut bad = execution.clone(); bad.selected = 14;
        assert!(derive_amendment_witness_table(&bad, &proposal, &chain.verify_chain(&RevocationSet::new()).unwrap(), 8).is_err());
        for vars in [0, 7, 25, usize::MAX] {
            assert!(derive_amendment_witness_table(&execution, &proposal,
                &chain.verify_chain(&RevocationSet::new()).unwrap(), vars).is_err());
        }
        let mut unrelated = env.clone();
        unrelated.dual_receipt = prove_dual_pcs_receipt(AMENDMENT_PROTOCOL_ID, env.dual_receipt.vk_digest,
            &env.dual_receipt.circuit_desc, &profile.canopy_params, &profile.lattice_params,
            8, &vec![Goldilocks::ZERO; 256]).unwrap();
        assert!(verifier.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &unrelated).is_err());
        assert!(verifier.accepted_nonces().is_empty());
        verifier.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &env).unwrap();
        let mut changed_nonce = env.clone(); changed_nonce.proposal.nonce += 1;
        assert_eq!(verifier.verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params,
            &changed_nonce).unwrap_err().code(), RefusalCode::RevokedLineage);
    }

    #[test]
    fn test_query_soundness_refuses_old_profiles() {
        let (profile, secret, policy, proposal, chain) = sample_fixture();
        let execution = example_amendment_execution();
        // Zero-bit query parameters are refused directly by CanopyParams::new.
        assert!(CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            1
        )
        .is_err());
        assert!(CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            2,
            2
        )
        .is_err());
        // Sub-128-bit profiles (8, 16, 32 queries at blowup 4 -> 4, 8, 16 bits) are refused by
        // new_with_min_soundness(128), validate_soundness(), prove_amendment_envelope, and verify_and_record_envelope.
        let valid_env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            8,
            &execution,
            proposal.clone(),
            chain.clone(),
            &RevocationSet::new(),
        )
        .unwrap();
        for q in [8, 16, 32] {
            assert!(CanopyParams::new_with_min_soundness(
                DomainKind::PrimeField,
                ProximityRegime::UniqueDecodingRadius,
                4,
                q,
                128
            )
            .is_err());
            let weak_cp = CanopyParams::new(
                DomainKind::PrimeField,
                ProximityRegime::UniqueDecodingRadius,
                4,
                q,
            )
            .unwrap();
            assert_eq!(weak_cp.soundness_bits(), q / 2);
            assert!(weak_cp.validate_soundness().is_err());
            assert!(matches!(
                prove_amendment_envelope(
                    &weak_cp,
                    &profile.lattice_params,
                    8,
                    &execution,
                    proposal.clone(),
                    chain.clone(),
                    &RevocationSet::new(),
                ),
                Err(AmendRefusal::TamperedCanopyOpening(
                    CanopyError::InsufficientQuerySoundness { .. }
                ))
            ));
            let mut verifier = AmendmentVerifierState::new(
                secret,
                policy,
                5,
                25,
                execution.prior_digest(),
            );
            assert!(matches!(
                verifier.verify_and_record_envelope(&weak_cp, &profile.lattice_params, &valid_env),
                Err(AmendRefusal::TamperedCanopyOpening(
                    CanopyError::InsufficientQuerySoundness { .. }
                ))
            ));
        }
        assert!(CanopyParams::default_128bit().soundness_bits() >= 128);
        for n in [25, usize::MAX] {
            assert!(matches!(
                crate::canopy::canopy_commit(&CanopyParams::default_128bit(), n, &[], None),
                Err(CanopyError::InvalidVariableCount(_))
            ));
        }
    }

    #[test]
    fn test_law_biscuit_golden_vectors() {
        let e = example_amendment_execution();
        let lineage = BiscuitHop::compute_lineage(&[3; 32], 0, 101, 255, 1000, "golden", &[0; 32]);
        let nul = BiscuitHop::compute_nullifier(&[3; 32], 0, 101, 255, 1000, "golden", &[0; 32]);
        let receipt = LawReceipt { slot: 2, accepted: true, selected: 7, retained: e.old.clone(),
            refused_cost: 0, evicted: vec![], skipped: vec![String::from("untouched")], frames: vec![(42, 99)],
            turn_digest: e.turn_digest(), bedrock_digest: e.bedrock_digest(),
            support_digest: cshake256_32(b"OBEND.LAW.SUPPORT/v1", &[0]) };
        for (name, digest) in [("turn", e.turn_digest()), ("bedrock", e.bedrock_digest()),
            ("receipt", receipt.digest()), ("lineage", lineage), ("nullifier", nul)] {
            let hex: String = digest.iter().map(|b| alloc::format!("{b:02x}")).collect();
            let expected = match name {
                "turn" => "2431ea726b7b7030421d7278cbbf3570767930d00f0a439804c825148edb6b35",
                "bedrock" => "0d9cb8d846f06d8780ea40f054faef443159568f0587ef09f4c2776a6fae0f83",
                "receipt" => "cf5a6308c19e9183faedadac9ddf72533272750ab3b64f616e421d93061d25f6",
                "lineage" => "e7d43dfb65f7d2f70ed08dbf68492e1fde0bd24251a456ed4f33b25dc9e4f251",
                "nullifier" => "aa15ffe15196a3cce9df102d6897fa10e2d441a1a5c393d1e035b0562152c027",
                _ => unreachable!(),
            };
            assert_eq!(hex, expected, "cross-language {name} vector");
        }
    }

}
