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
pub const AMENDMENT_ENVELOPE_SCHEMA_V1: u64 = 1;

/// Domain-separated Fiat-Shamir protocol identifier for `SignedAmendmentEnvelope`.
pub const AMENDMENT_PROTOCOL_ID: &str = "OBEND.POLIS.AMEND_ZK_BISCUIT/v1";

const AMEND_PROPOSAL_CUSTOM: &[u8] = b"OBEND.AMEND.PROPOSAL_COMMIT/v1";
const AMEND_VK_CUSTOM: &[u8] = b"OBEND.AMEND.VK_DIGEST/v1";
const BISCUIT_GENESIS_CUSTOM: &[u8] = b"OBEND.ZK_BISCUIT.GENESIS_HOP/v1";
const BISCUIT_ATTENUATE_CUSTOM: &[u8] = b"OBEND.ZK_BISCUIT.ATTENUATE_HOP/v1";
const AMEND_WITNESS_EXPAND_CUSTOM: &[u8] = b"OBEND.AMEND.WITNESS_EXPAND/v1";

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

/// Default fast sub-5ms 128-bit Dual-Track profile (`v = 8`, `N = 256` Goldilocks elements,
/// `Canopy` `blowup = 4, queries = 16`, `PikkuFold`/`Akita` `rows = 2, cols = 16`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastReceiptProfile {
    pub num_vars: usize,
    pub canopy_params: CanopyParams,
    pub lattice_params: LatticeParams,
}

impl FastReceiptProfile {
    /// Construct the standard sub-5ms CLI & stranger-verification profile (`v = 8`).
    pub fn sub5ms_default() -> Self {
        let canopy_params = CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            16,
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

    /// Construct a full `CanopyParams::default_128bit()` (`queries = 32`) profile at `v = 10` (`N = 1024`).
    pub fn full_128bit_v10() -> Self {
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

/// Governance/policy amendment commitment payload. Every field is length-framed into
/// `commitment_digest()` (`frame_bytes` / fixed-width BE) so Stage-B binding has zero unframed slack.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmendmentProposal {
    pub policy_digest: [u8; 32],
    pub amendment_digest: [u8; 32],
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
        frame_u64(&mut buf, self.epoch);
        frame_u64(&mut buf, self.nonce);
        frame_u64(&mut buf, self.required_rights);
        frame_bytes(&mut buf, self.target_organ.as_bytes());
        cshake256_32(AMEND_PROPOSAL_CUSTOM, &buf)
    }

    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
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
        if m.len() != 6 {
            return Err(DetCborError::UnexpectedFieldCount {
                expected: 6,
                actual: m.len(),
            });
        }
        Ok(Self {
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
    pub parent_nullifier: [u8; 32],
    pub hop_nullifier: [u8; 32],
}

impl BiscuitHop {
    /// Compute the canonical `cSHAKE256` lineage nullifier for a genesis or attenuation hop.
    pub fn compute_nullifier(
        root_authority_id: &[u8; 32],
        hop_index: u32,
        channel_id: u64,
        rights_mask: u64,
        caveat_epoch_max: u64,
        attenuation_note: &str,
        parent_nullifier: &[u8; 32],
    ) -> [u8; 32] {
        let mut pre = Vec::with_capacity(128 + attenuation_note.len());
        frame_bytes(&mut pre, root_authority_id);
        pre.extend_from_slice(&hop_index.to_be_bytes());
        frame_u64(&mut pre, channel_id);
        frame_u64(&mut pre, rights_mask);
        frame_u64(&mut pre, caveat_epoch_max);
        frame_bytes(&mut pre, attenuation_note.as_bytes());
        frame_bytes(&mut pre, parent_nullifier);
        let custom = if hop_index == 0 {
            BISCUIT_GENESIS_CUSTOM
        } else {
            BISCUIT_ATTENUATE_CUSTOM
        };
        cshake256_32(custom, &pre)
    }

    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
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
                CborValue::Text(String::from("parent_nullifier")),
                CborValue::Bytes(self.parent_nullifier.to_vec()),
            ),
            (
                CborValue::Text(String::from("rights_mask")),
                CborValue::Unsigned(self.rights_mask),
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
        let hop_index_u64 = map_lookup(m, "hop_index")?.as_u64()?;
        let hop_index = u32::try_from(hop_index_u64).map_err(|_| DetCborError::LengthOverflow)?;
        Ok(Self {
            hop_index,
            channel_id: map_lookup(m, "channel_id")?.as_u64()?,
            rights_mask: map_lookup(m, "rights_mask")?.as_u64()?,
            caveat_epoch_max: map_lookup(m, "caveat_epoch_max")?.as_u64()?,
            attenuation_note: String::from(map_lookup(m, "attenuation_note")?.as_text()?),
            parent_nullifier: decode_hash32(map_lookup(m, "parent_nullifier")?, "parent_nullifier")?,
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
    /// Mint a root authority genesis capability block (`hop_index = 0`).
    pub fn mint_root(
        root_authority_id: [u8; 32],
        channel_id: u64,
        initial_rights: u64,
        caveat_epoch_max: u64,
        note: &str,
    ) -> Self {
        let parent_nullifier = [0u8; 32];
        let hop_nullifier = BiscuitHop::compute_nullifier(
            &root_authority_id,
            0,
            channel_id,
            initial_rights,
            caveat_epoch_max,
            note,
            &parent_nullifier,
        );
        Self {
            root_authority_id,
            hops: vec![BiscuitHop {
                hop_index: 0,
                channel_id,
                rights_mask: initial_rights,
                caveat_epoch_max,
                attenuation_note: String::from(note),
                parent_nullifier,
                hop_nullifier,
            }],
        }
    }

    /// Append a strictly monotone attenuated child hop (`attenuated_rights ⊆ parent.rights_mask`
    /// and `caveat_epoch_max <= parent.caveat_epoch_max`).
    pub fn attenuate(
        &self,
        channel_id: u64,
        attenuated_rights: u64,
        caveat_epoch_max: u64,
        note: &str,
    ) -> Result<Self, AmendRefusal> {
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
        let parent_nullifier = prev.hop_nullifier;
        let hop_nullifier = BiscuitHop::compute_nullifier(
            &self.root_authority_id,
            hop_index,
            channel_id,
            attenuated_rights,
            caveat_epoch_max,
            note,
            &parent_nullifier,
        );
        let mut next = self.clone();
        next.hops.push(BiscuitHop {
            hop_index,
            channel_id,
            rights_mask: attenuated_rights,
            caveat_epoch_max,
            attenuation_note: String::from(note),
            parent_nullifier,
            hop_nullifier,
        });
        Ok(next)
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
        let mut prev_rights = u64::MAX;
        let mut prev_epoch_max = u64::MAX;

        for (idx, hop) in self.hops.iter().enumerate() {
            if hop.hop_index as usize != idx {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "non-contiguous hop_index",
                });
            }
            if hop.parent_nullifier != prev_nullifier {
                return Err(AmendRefusal::ForgedAttenuationHop {
                    hop_index: idx,
                    reason: "parent_nullifier mismatch",
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
                &hop.parent_nullifier,
            );
            if hop.hop_nullifier != expected_nullifier {
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

/// Deterministically expand a `2^num_vars` `Goldilocks` multilinear execution trace from
/// `(witness_secret, proposal_commitment, leaf_nullifier)`.
pub fn derive_amendment_witness_table(
    witness_secret: &[u8; 32],
    proposal: &AmendmentProposal,
    lineage: &VerifiedBiscuitLineage,
    num_vars: usize,
) -> Vec<Goldilocks> {
    let n = 1usize << num_vars;
    let prop_commit = proposal.commitment_digest();
    let mut out = Vec::with_capacity(n);
    let mut block_in = [0u8; 104];
    block_in[0..32].copy_from_slice(witness_secret);
    block_in[32..64].copy_from_slice(&prop_commit);
    block_in[64..96].copy_from_slice(&lineage.leaf_nullifier);

    // Squeeze 4 Goldilocks elements per 32-byte cSHAKE256 block
    let blocks = n.div_ceil(4);
    for blk in 0..blocks {
        block_in[96..104].copy_from_slice(&(blk as u64).to_be_bytes());
        let digest = cshake256_32(AMEND_WITNESS_EXPAND_CUSTOM, &block_in);
        for limb in 0..4 {
            if out.len() == n {
                break;
            }
            let mut word_bytes = [0u8; 8];
            word_bytes.copy_from_slice(&digest[limb * 8..(limb + 1) * 8]);
            out.push(Goldilocks::from_u64_reduced(u64::from_le_bytes(word_bytes)));
        }
    }
    out
}

/// Complete canonical `DetCbor` wire envelope bundling `AmendmentProposal`, `ZkBiscuitChain`,
/// and Dual-Track `DualPcsReceipt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedAmendmentEnvelope {
    pub schema_version: u64,
    pub proposal: AmendmentProposal,
    pub biscuit_chain: ZkBiscuitChain,
    pub dual_receipt: DualPcsReceipt,
}

impl SignedAmendmentEnvelope {
    pub fn to_cbor_value(&self) -> CborValue {
        CborValue::Map(vec![
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
        if m.len() != 4 {
            return Err(AmendRefusal::NonCanonicalCbor(
                DetCborError::UnexpectedFieldCount {
                    expected: 4,
                    actual: m.len(),
                },
            ));
        }
        let schema_version = map_lookup(m, "schema_version")
            .and_then(CborValue::as_u64)
            .map_err(AmendRefusal::NonCanonicalCbor)?;
        if schema_version != AMENDMENT_ENVELOPE_SCHEMA_V1 {
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
        let env = Self {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmendmentVerifierState {
    pub expected_root_authority: [u8; 32],
    pub expected_policy_digest: [u8; 32],
    pub revocations: RevocationSet,
    accepted_nonces: Vec<u64>,
}

impl AmendmentVerifierState {
    pub fn new(expected_root_authority: [u8; 32], expected_policy_digest: [u8; 32]) -> Self {
        Self {
            expected_root_authority,
            expected_policy_digest,
            revocations: RevocationSet::new(),
            accepted_nonces: Vec::new(),
        }
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
        if env.biscuit_chain.root_authority_id != self.expected_root_authority {
            return Err(AmendRefusal::AmendmentBindingMismatch {
                field: "root_authority_id",
            });
        }

        // 3. ZkBiscuit monotone attenuation & ancestor-cone revocation fold
        let lineage = env.biscuit_chain.verify_chain(&self.revocations)?;

        // 4. Epoch caveat & attenuated rights authorization
        if env.proposal.epoch > lineage.caveat_epoch_max {
            return Err(AmendRefusal::ForgedAttenuationHop {
                hop_index: lineage.hop_count - 1,
                reason: "proposal epoch exceeds leaf caveat_epoch_max",
            });
        }
        if (lineage.effective_rights & env.proposal.required_rights) != env.proposal.required_rights
        {
            return Err(AmendRefusal::InsufficientRights {
                effective_rights: lineage.effective_rights,
                required_rights: env.proposal.required_rights,
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

        // 7. Commit nonce to anti-replay log only after full verification passes
        self.accepted_nonces
            .insert(nonce_insert_pos, env.proposal.nonce);

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
    witness_secret: &[u8; 32],
    proposal: AmendmentProposal,
    biscuit_chain: ZkBiscuitChain,
    revocations: &RevocationSet,
) -> Result<SignedAmendmentEnvelope, AmendRefusal> {
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
    let table = derive_amendment_witness_table(witness_secret, &proposal, &lineage, num_vars);

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
        schema_version: AMENDMENT_ENVELOPE_SCHEMA_V1,
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
        let policy_digest = cshake256_32(b"TEST.POLICY", b"cathedral-policy-v5");
        let amendment_digest = cshake256_32(b"TEST.AMEND", b"enable-stageb-seal-organ7");

        let chain = ZkBiscuitChain::mint_root(root_auth, 1001, 0b1111_1111, 50, "root:council")
            .attenuate(1002, 0b0011_1111, 40, "delegate:cluster-gov")
            .unwrap()
            .attenuate(1003, 0b0000_1111, 30, "worker:amend-prover")
            .unwrap();

        let proposal = AmendmentProposal {
            policy_digest,
            amendment_digest,
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
            &[0x42u8; 32],
            proposal,
            chain,
            &revocations,
        )
        .unwrap();

        let wire = env.to_det_cbor_bytes().unwrap();
        let mut verifier = AmendmentVerifierState::new(root_auth, policy_digest);
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
            &[0x42u8; 32],
            proposal,
            chain,
            &revocations,
        )
        .unwrap();
        let wire = env.to_det_cbor_bytes().unwrap();

        // Case 1: Non-canonical CBOR map key order (`{ "z": 1, "a": 2 }`)
        let mut verifier = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut rev_verifier = AmendmentVerifierState::new(root_auth, policy_digest);
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
}
