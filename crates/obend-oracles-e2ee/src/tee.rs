//! Hardened Multi-Vendor TEE & GPU Attestation Gate (`CAP-24`, `CAP-25`, `CAP-26` closed).
//!
//! Quarried and hardened from `breadstuffs/tee-verify/src/{lib.rs,snp.rs,snp_chain.rs,tdx.rs,nvidia.rs,nvidia_rim.rs,nvidia_ocsp.rs}`:
//!
//! - **`CAP-24` closed:** Enforces RFC 5280 `BasicConstraints` (`is_ca`, `path_len_constraint`)
//!   and `KeyUsage` (`keyCertSign`, `cRLSign`, `digitalSignature`) on every root, intermediate,
//!   and leaf certificate across AWS Nitro, AMD SEV-SNP, Intel TDX, and NVIDIA GPU/RIM chains,
//!   including pure-Rust ASN.1 DER extension parsers. Leaf-signed child certificates forging
//!   `device_chain[0]` are refused unconditionally.
//! - **`CAP-25` closed:** AMD SEV-SNP requires at least one verified, non-expired CRL issued by
//!   an authorized CA (`cRLSign`) covering ASK/VCEK serials, AND rejects below-floor TCB directly
//!   inside the gate (never emitting an accepted token with `BelowPolicy`).
//! - **`CAP-26` closed:** Intel TDX 1.0/1.5 enforces fail-closed `now_secs > 0`, strict TCB
//!   status allowlist, custom `mr_servicetd` allowlist (allowing pinned service TDs while
//!   refusing unpinned nonzero `mr_servicetd`), and `MRTD`/`RTMR0..2` (plus optional `RTMR3`)
//!   measurement pins. NVIDIA Hopper (`H100`/`GH100`) and Blackwell (`B200`/`GB200`) enforce
//!   strict SPDM 1.1 `GET_MEASUREMENTS` parsing, OCSP non-revocation, and 3-way `FWID` pinning
//!   (`SPDM TLV 20 == leaf TCG DICE DER extension == signed RIM expected_fwid`).
//! - Returns a sealed [`VerifiedTeeEvidence`] token with private fields constructible only by
//!   the verified gate functions in this module.

use std::collections::BTreeMap;

use crate::sha256::{ct_eq, sha256, Sha256};

// ---------------------------------------------------------------------------
// Constants & Bitmasks
// ---------------------------------------------------------------------------

/// RFC 5280 KeyUsage bit 0 (`digitalSignature`).
pub const KEY_USAGE_DIGITAL_SIGNATURE: u16 = 1 << 0;
/// RFC 5280 KeyUsage bit 5 (`keyCertSign`).
pub const KEY_USAGE_KEY_CERT_SIGN: u16 = 1 << 5;
/// RFC 5280 KeyUsage bit 6 (`cRLSign`).
pub const KEY_USAGE_CRL_SIGN: u16 = 1 << 6;

/// Maximum allowed future timestamp skew for Nitro docs (seconds), matching `tee-verify/src/lib.rs:178`.
pub const MAX_FUTURE_SKEW_SECS: u64 = 60;

/// All-zero TD 1.5 `MR_SERVICETD` value (no migration/service TD bound).
pub const NO_SERVICE_TD: [u8; 48] = [0u8; 48];

/// SPDM 1.1 constants matching `breadstuffs/tee-verify/src/nvidia.rs:46-55`.
pub const SPDM_REQUEST_LEN: usize = 37;
pub const SPDM_SIGNATURE_LEN: usize = 96;
pub const SPDM_NONCE_LEN: usize = 32;
const SPDM_GET_MEASUREMENTS_REQUEST: u8 = 0xE0;
const SPDM_MEASUREMENTS_RESPONSE: u8 = 0x60;
const SPDM_DMTF_SPEC: u8 = 1;

/// NVIDIA SPDM opaque TLV types (`breadstuffs/tee-verify/src/nvidia.rs:367,401-403`).
pub const OPAQUE_CHIP_SKU: u16 = 15;
pub const OPAQUE_PROJECT: u16 = 17;
pub const OPAQUE_PROJECT_SKU: u16 = 18;
pub const OPAQUE_FWID: u16 = 20;

/// AMD SEV-SNP policy bits (`breadstuffs/tee-verify/src/snp.rs`).
pub const SNP_POLICY_SMT: u64 = 1 << 16;
pub const SNP_POLICY_RESERVED_MBO: u64 = 1 << 17;
pub const SNP_POLICY_MIGRATE_MA: u64 = 1 << 18;
pub const SNP_POLICY_DEBUG: u64 = 1 << 19;
pub const SNP_POLICY_SINGLE_SOCKET: u64 = 1 << 20;
pub const SNP_POLICY_CXL_ALLOW: u64 = 1 << 21;
pub const SNP_POLICY_MEM_AES_256_XTS: u64 = 1 << 22;
pub const SNP_POLICY_RAPL_DIS: u64 = 1 << 23;
pub const SNP_POLICY_CIPHERTEXT_HIDING: u64 = 1 << 24;
pub const SNP_POLICY_KNOWN_MASK: u64 = 0xFFFF
    | SNP_POLICY_SMT
    | SNP_POLICY_RESERVED_MBO
    | SNP_POLICY_MIGRATE_MA
    | SNP_POLICY_DEBUG
    | SNP_POLICY_SINGLE_SOCKET
    | SNP_POLICY_CXL_ALLOW
    | SNP_POLICY_MEM_AES_256_XTS
    | SNP_POLICY_RAPL_DIS
    | SNP_POLICY_CIPHERTEXT_HIDING;
pub const SNP_SIGNING_KEY_VCEK: u8 = 0;

// ---------------------------------------------------------------------------
// Pure-Rust ASN.1 DER Parsers for RFC 5280 BasicConstraints, KeyUsage, & DICE FWID
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BasicConstraints {
    pub is_ca: bool,
    pub path_len_constraint: Option<u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyUsage {
    pub bits: u16,
}

impl KeyUsage {
    pub const fn new(bits: u16) -> Self {
        Self { bits }
    }

    pub const fn has(self, mask: u16) -> bool {
        (self.bits & mask) == mask
    }

    pub const fn key_cert_sign(self) -> bool {
        self.has(KEY_USAGE_KEY_CERT_SIGN)
    }

    pub const fn crl_sign(self) -> bool {
        self.has(KEY_USAGE_CRL_SIGN)
    }

    pub const fn digital_signature(self) -> bool {
        self.has(KEY_USAGE_DIGITAL_SIGNATURE)
    }
}

fn parse_der_tlv(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let &tag = input.first()?;
    let &len_byte = input.get(1)?;
    let (len, hdr_len) = if (len_byte & 0x80) == 0 {
        (usize::from(len_byte), 2usize)
    } else {
        let num_octets = usize::from(len_byte & 0x7f);
        if num_octets == 0 || num_octets > 4 {
            return None;
        }
        let len_slice = input.get(2..2 + num_octets)?;
        // Enforce DER minimal-length encoding (no leading zero byte, length >= 128).
        if len_slice[0] == 0 {
            return None;
        }
        let mut len = 0usize;
        for &b in len_slice {
            len = (len << 8) | usize::from(b);
        }
        if len < 128 {
            return None;
        }
        (len, 2 + num_octets)
    };
    let end = hdr_len.checked_add(len)?;
    let value = input.get(hdr_len..end)?;
    let rest = input.get(end..)?;
    Some((tag, value, rest))
}

/// Strictly parse RFC 5280 `BasicConstraints ::= SEQUENCE { cA BOOLEAN DEFAULT FALSE, pathLenConstraint INTEGER (0..MAX) OPTIONAL }`.
pub fn parse_der_basic_constraints(der: &[u8]) -> Option<BasicConstraints> {
    let (tag, body, trailing) = parse_der_tlv(der)?;
    if tag != 0x30 || !trailing.is_empty() {
        return None;
    }
    let mut cur = body;
    let mut is_ca = false;
    let mut path_len_constraint = None;

    if !cur.is_empty() && cur[0] == 0x01 {
        let (_, val, rest) = parse_der_tlv(cur)?;
        if val.len() != 1 {
            return None;
        }
        // DER BOOLEAN: 0x00 = FALSE, 0xFF = TRUE (other values invalid in DER).
        is_ca = match val[0] {
            0x00 => false,
            0xFF => true,
            _ => return None,
        };
        cur = rest;
    }
    if !cur.is_empty() {
        let (int_tag, val, rest) = parse_der_tlv(cur)?;
        if int_tag != 0x02 || !rest.is_empty() || val.is_empty() || val.len() > 2 {
            return None;
        }
        // Negative INTEGER or non-minimal DER padding is invalid.
        if (val[0] & 0x80) != 0 {
            return None;
        }
        if val.len() == 2 && (val[0] != 0x00 || (val[1] & 0x80) == 0) {
            return None;
        }
        let n = if val.len() == 1 {
            val[0]
        } else {
            val[1]
        };
        path_len_constraint = Some(n);
    }
    Some(BasicConstraints {
        is_ca,
        path_len_constraint,
    })
}

/// Strictly parse RFC 5280 `KeyUsage ::= BIT STRING` into bit flags (`KEY_USAGE_*`).
/// In X.509 BIT STRINGs, bit 0 is the MSB (0x80) of the first content octet.
pub fn parse_der_key_usage(der: &[u8]) -> Option<KeyUsage> {
    let (tag, val, trailing) = parse_der_tlv(der)?;
    if tag != 0x03 || !trailing.is_empty() || val.len() < 2 || val.len() > 3 {
        return None;
    }
    let unused_bits = val[0];
    if unused_bits > 7 {
        return None;
    }
    let last_byte = *val.last()?;
    if unused_bits > 0 && (last_byte & ((1u8 << unused_bits) - 1)) != 0 {
        return None;
    }
    let mut bits = 0u16;
    let total_bits = (val.len() - 1) * 8 - usize::from(unused_bits);
    for bit_idx in 0..total_bits.min(16) {
        let byte = val[1 + (bit_idx / 8)];
        let shift = 7 - (bit_idx % 8);
        if ((byte >> shift) & 1) == 1 {
            bits |= 1u16 << bit_idx;
        }
    }
    Some(KeyUsage { bits })
}

/// Extract the 48-byte TCG DICE `FWID` digest from a DER-encoded DICE extension value
/// (NVIDIA Hopper/Blackwell: trailing 48-byte SHA-384 FWID inside the extension OCTET STRING / SEQUENCE).
/// Fails closed if fewer than 48 bytes or if the FWID is all zeros.
pub fn extract_der_dice_fwid(ext_value: &[u8]) -> Option<[u8; 48]> {
    if ext_value.len() < 48 {
        return None;
    }
    let mut fwid = [0u8; 48];
    fwid.copy_from_slice(&ext_value[ext_value.len() - 48..]);
    if fwid.iter().all(|&b| b == 0) {
        return None;
    }
    Some(fwid)
}

// ---------------------------------------------------------------------------
// RFC 5280 Certificate Chain Gate (CAP-24)
// ---------------------------------------------------------------------------

/// Structured X.509 certificate record verified by [`verify_rfc5280_cert_chain`].
/// Callers may supply pre-parsed `basic_constraints` / `key_usage` OR raw DER extension bytes
/// (`basic_constraints_der` / `key_usage_der`), which are parsed strictly and must agree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertRecord {
    pub subject: String,
    pub issuer: String,
    pub serial: Vec<u8>,
    pub cert_sha256: [u8; 32],
    pub not_before: u64,
    pub not_after: u64,
    pub basic_constraints: Option<BasicConstraints>,
    pub basic_constraints_der: Option<Vec<u8>>,
    pub key_usage: Option<KeyUsage>,
    pub key_usage_der: Option<Vec<u8>>,
    /// Whether the cryptographic signature of this cert verified under its issuer's public key.
    pub sig_verified: bool,
    /// Optional raw TCG DICE FWID extension bytes (OID `2.23.133.5.4.1` / `.1.1`) on leaf certs.
    pub dice_fwid_ext_der: Option<Vec<u8>>,
}

impl CertRecord {
    fn resolved_basic_constraints(&self) -> Result<Option<BasicConstraints>, CertChainError> {
        match (self.basic_constraints, self.basic_constraints_der.as_deref()) {
            (Some(bc), Some(der)) => {
                let parsed = parse_der_basic_constraints(der)
                    .ok_or(CertChainError::MalformedBasicConstraintsDer)?;
                if parsed != bc {
                    return Err(CertChainError::MalformedBasicConstraintsDer);
                }
                Ok(Some(parsed))
            }
            (None, Some(der)) => {
                let parsed = parse_der_basic_constraints(der)
                    .ok_or(CertChainError::MalformedBasicConstraintsDer)?;
                Ok(Some(parsed))
            }
            (Some(bc), None) => Ok(Some(bc)),
            (None, None) => Ok(None),
        }
    }

    fn resolved_key_usage(&self) -> Result<Option<KeyUsage>, CertChainError> {
        match (self.key_usage, self.key_usage_der.as_deref()) {
            (Some(ku), Some(der)) => {
                let parsed =
                    parse_der_key_usage(der).ok_or(CertChainError::MalformedKeyUsageDer)?;
                if parsed != ku {
                    return Err(CertChainError::MalformedKeyUsageDer);
                }
                Ok(Some(parsed))
            }
            (None, Some(der)) => {
                let parsed =
                    parse_der_key_usage(der).ok_or(CertChainError::MalformedKeyUsageDer)?;
                Ok(Some(parsed))
            }
            (Some(ku), None) => Ok(Some(ku)),
            (None, None) => Ok(None),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertChainError {
    InvalidClock,
    EmptyChain,
    SingleCertChainDisallowed,
    RootAnchorMismatch,
    RootNotSelfIssued,
    IssuerSubjectMismatch { index: usize },
    NotValidAtReferenceTime { index: usize },
    BadChainSignature { index: usize },
    MalformedBasicConstraintsDer,
    MalformedKeyUsageDer,
    MissingCaBasicConstraints { index: usize },
    NonCaIssuer { index: usize },
    MissingKeyCertSign { index: usize },
    PathLenConstraintExceeded { index: usize, max_allowed: u8, actual: usize },
    LeafMustNotBeCa,
    LeafMissingDigitalSignature,
}

/// Verify an X.509 certificate chain ordered **`[root, intermediate_1, ..., intermediate_k, leaf]`**
/// against `pinned_root_sha256` at `now_secs`, closing **`CAP-24`**:
///
/// 1. Refuses `now_secs == 0` (fail-closed clock check) and chains with `< 2` certs.
/// 2. Requires `chain[0].cert_sha256 == pinned_root_sha256` and self-issued root.
/// 3. For every cert `i`: checks validity window `not_before <= now_secs <= not_after`,
///    signature verification `sig_verified`, and issuer/subject chaining.
/// 4. For every non-leaf CA cert (`0..len-1`): requires `BasicConstraints { is_ca: true, .. }`,
///    requires `KeyUsage::KEY_CERT_SIGN`, and enforces `path_len_constraint` against the number
///    of subordinate intermediate CAs below `i`.
/// 5. For the leaf cert (`len - 1`): forbids `is_ca == true` and requires `DIGITAL_SIGNATURE`.
pub fn verify_rfc5280_cert_chain(
    chain_root_to_leaf: &[CertRecord],
    pinned_root_sha256: &[u8; 32],
    now_secs: u64,
) -> Result<(), CertChainError> {
    if now_secs == 0 {
        return Err(CertChainError::InvalidClock);
    }
    if chain_root_to_leaf.is_empty() {
        return Err(CertChainError::EmptyChain);
    }
    if chain_root_to_leaf.len() < 2 {
        return Err(CertChainError::SingleCertChainDisallowed);
    }

    let root = &chain_root_to_leaf[0];
    if !ct_eq(&root.cert_sha256, pinned_root_sha256) {
        return Err(CertChainError::RootAnchorMismatch);
    }
    if root.subject != root.issuer {
        return Err(CertChainError::RootNotSelfIssued);
    }

    let last = chain_root_to_leaf.len() - 1;
    let mut ca_path_lens: Vec<(usize, u8)> = Vec::new();
    for (i, cert) in chain_root_to_leaf.iter().enumerate() {
        if cert.not_before > cert.not_after
            || now_secs < cert.not_before
            || now_secs > cert.not_after
        {
            return Err(CertChainError::NotValidAtReferenceTime { index: i });
        }
        if !cert.sig_verified {
            return Err(CertChainError::BadChainSignature { index: i });
        }
        if i > 0 && cert.issuer != chain_root_to_leaf[i - 1].subject {
            return Err(CertChainError::IssuerSubjectMismatch { index: i });
        }

        let bc = cert.resolved_basic_constraints()?;
        let ku = cert.resolved_key_usage()?;

        if i < last {
            // Root or intermediate CA: MUST carry BasicConstraints(CA:TRUE) + KeyUsage(keyCertSign).
            let Some(bc) = bc else {
                return Err(CertChainError::MissingCaBasicConstraints { index: i });
            };
            if !bc.is_ca {
                return Err(CertChainError::NonCaIssuer { index: i });
            }
            let ku = ku.ok_or(CertChainError::MissingKeyCertSign { index: i })?;
            if !ku.key_cert_sign() {
                return Err(CertChainError::MissingKeyCertSign { index: i });
            }
            if let Some(max_len) = bc.path_len_constraint {
                ca_path_lens.push((i, max_len));
            }
        } else {
            // Leaf certificate: MUST NOT be a CA, and MUST carry digitalSignature.
            if let Some(bc) = bc {
                if bc.is_ca {
                    return Err(CertChainError::LeafMustNotBeCa);
                }
            }
            let ku = ku.ok_or(CertChainError::LeafMissingDigitalSignature)?;
            if !ku.digital_signature() {
                return Err(CertChainError::LeafMissingDigitalSignature);
            }
        }
    }

    // Enforce RFC 5280 pathLenConstraint after confirming every issuer is a genuine CA.
    for (i, max_len) in ca_path_lens {
        let subordinate_intermediates = last - 1 - i;
        if subordinate_intermediates > usize::from(max_len) {
            return Err(CertChainError::PathLenConstraintExceeded {
                index: i,
                max_allowed: max_len,
                actual: subordinate_intermediates,
            });
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// SPDM 1.1 GPU Report Wire Parser (NVIDIA Hopper / Blackwell)
// ---------------------------------------------------------------------------

/// Parsed SPDM 1.1 `GET_MEASUREMENTS` request + response (`breadstuffs/tee-verify/src/nvidia.rs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpdmGpuReport {
    pub spdm_version: u8,
    pub request_nonce: [u8; SPDM_NONCE_LEN],
    pub response_nonce: [u8; SPDM_NONCE_LEN],
    pub measurements: BTreeMap<u8, Vec<u8>>,
    pub opaque: Vec<(u16, Vec<u8>)>,
    pub signed_prefix: Vec<u8>,
    pub signature: [u8; SPDM_SIGNATURE_LEN],
}

impl SpdmGpuReport {
    pub fn opaque_field(&self, ty: u16) -> Option<&[u8]> {
        self.opaque
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, v)| v.as_slice())
    }

    pub fn fwid(&self) -> Option<[u8; 48]> {
        let raw = self.opaque_field(OPAQUE_FWID)?;
        if raw.len() != 48 {
            return None;
        }
        let mut out = [0u8; 48];
        out.copy_from_slice(raw);
        if out.iter().all(|&b| b == 0) {
            return None;
        }
        Some(out)
    }
}

fn spdm_take<'a>(b: &'a [u8], at: &mut usize, n: usize) -> Result<&'a [u8], TeeError> {
    let end = at.checked_add(n).ok_or(TeeError::SpdmMalformed)?;
    let s = b.get(*at..end).ok_or(TeeError::SpdmMalformed)?;
    *at = end;
    Ok(s)
}

fn spdm_le(b: &[u8]) -> usize {
    b.iter()
        .rev()
        .fold(0usize, |acc, &x| (acc << 8) | usize::from(x))
}

/// Parse an SPDM 1.1 `request(37) || response` NVIDIA GPU attestation report fail-closed:
/// exact lengths, DMTF spec bit, unique measurement indices, opaque TLVs, 0 trailing bytes.
pub fn parse_spdm_gpu_report(report: &[u8]) -> Result<SpdmGpuReport, TeeError> {
    if report.len() <= SPDM_REQUEST_LEN + SPDM_SIGNATURE_LEN {
        return Err(TeeError::SpdmMalformed);
    }
    let (req, resp) = report.split_at(SPDM_REQUEST_LEN);
    if req[1] != SPDM_GET_MEASUREMENTS_REQUEST {
        return Err(TeeError::SpdmMalformed);
    }
    let mut request_nonce = [0u8; SPDM_NONCE_LEN];
    request_nonce.copy_from_slice(&req[4..4 + SPDM_NONCE_LEN]);

    let mut at = 0usize;
    let hdr = spdm_take(resp, &mut at, 4)?;
    if hdr[0] != req[0] || hdr[1] != SPDM_MEASUREMENTS_RESPONSE {
        return Err(TeeError::SpdmMalformed);
    }
    let nblocks = usize::from(spdm_take(resp, &mut at, 1)?[0]);
    let rec_len = spdm_le(spdm_take(resp, &mut at, 3)?);
    let record = spdm_take(resp, &mut at, rec_len)?;

    let mut measurements = BTreeMap::new();
    let mut r = 0usize;
    while r < record.len() {
        let index = spdm_take(record, &mut r, 1)?[0];
        let spec = spdm_take(record, &mut r, 1)?[0];
        if spec != SPDM_DMTF_SPEC {
            return Err(TeeError::SpdmMalformed);
        }
        let size = spdm_le(spdm_take(record, &mut r, 2)?);
        let block = spdm_take(record, &mut r, size)?;
        if block.len() < 3 {
            return Err(TeeError::SpdmMalformed);
        }
        let vsize = spdm_le(&block[1..3]);
        if 3 + vsize != block.len() {
            return Err(TeeError::SpdmMalformed);
        }
        if measurements.insert(index, block[3..].to_vec()).is_some() {
            return Err(TeeError::SpdmDuplicateBlock(index));
        }
    }
    if measurements.len() != nblocks {
        return Err(TeeError::SpdmMalformed);
    }

    let mut response_nonce = [0u8; SPDM_NONCE_LEN];
    response_nonce.copy_from_slice(spdm_take(resp, &mut at, SPDM_NONCE_LEN)?);
    let opaque_len = spdm_le(spdm_take(resp, &mut at, 2)?);
    let opaque_bytes = spdm_take(resp, &mut at, opaque_len)?;
    let mut opaque = Vec::new();
    let mut o = 0usize;
    while o < opaque_bytes.len() {
        let ty = spdm_le(spdm_take(opaque_bytes, &mut o, 2)?) as u16;
        let n = spdm_le(spdm_take(opaque_bytes, &mut o, 2)?);
        opaque.push((ty, spdm_take(opaque_bytes, &mut o, n)?.to_vec()));
    }
    let sig_slice = spdm_take(resp, &mut at, SPDM_SIGNATURE_LEN)?;
    if at != resp.len() {
        return Err(TeeError::SpdmTrailingBytes(resp.len() - at));
    }
    let mut signature = [0u8; SPDM_SIGNATURE_LEN];
    signature.copy_from_slice(sig_slice);

    Ok(SpdmGpuReport {
        spdm_version: req[0],
        request_nonce,
        response_nonce,
        measurements,
        opaque,
        signed_prefix: report[..report.len() - SPDM_SIGNATURE_LEN].to_vec(),
        signature,
    })
}

// ---------------------------------------------------------------------------
// Sealed VerifiedTeeEvidence Token & Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuArch {
    HopperH100,
    BlackwellB200,
}

impl GpuArch {
    pub const fn rim_product(self) -> &'static str {
        match self {
            Self::HopperH100 => "GH100",
            Self::BlackwellB200 => "GB200",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AmdSnpProduct {
    Milan,
    Genoa,
    Turin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TeeVendor {
    AwsNitro,
    AmdSevSnp(AmdSnpProduct),
    IntelTdx,
    NvidiaGpu(GpuArch),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcbPosture {
    /// Hardware TCB floor / DCAP TCB status / RIM golden measurements were actively verified.
    VerifiedFloor,
    /// Platform exposes no microcode/TCB version (AWS Nitro Enclaves); code identity pin carries trust.
    NoPolicyOnPlatform,
}

/// Sealed, unforgeable verified TEE / confidential-GPU attestation token.
/// Private fields ensure construction is exclusively via the hardened verifier gates in this module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedTeeEvidence {
    vendor: TeeVendor,
    measurement: [u8; 32],
    report_data: [u8; 64],
    tcb_posture: TcbPosture,
    gpu_fwid: Option<[u8; 48]>,
    verified_at: u64,
    evidence_digest: [u8; 32],
}

impl VerifiedTeeEvidence {
    pub fn vendor(&self) -> TeeVendor {
        self.vendor
    }
    pub fn measurement(&self) -> [u8; 32] {
        self.measurement
    }
    pub fn report_data(&self) -> &[u8; 64] {
        &self.report_data
    }
    pub fn report_data_32(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(&self.report_data[..32]);
        out
    }
    pub fn tcb_posture(&self) -> TcbPosture {
        self.tcb_posture
    }
    pub fn gpu_fwid(&self) -> Option<[u8; 48]> {
        self.gpu_fwid
    }
    pub fn verified_at(&self) -> u64 {
        self.verified_at
    }
    pub fn evidence_digest(&self) -> [u8; 32] {
        self.evidence_digest
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TeeError {
    InvalidClock,
    CertChain(CertChainError),
    ReportSignatureInvalid,
    MeasurementMismatch,
    // Nitro
    NitroMissingPcr(u8),
    NitroFutureTimestamp { ahead_secs: u64 },
    NitroStaleDoc { age_secs: u64, max_age_secs: u64 },
    // AMD SEV-SNP (CAP-25)
    SnpChainLengthInvalid,
    SnpMissingCrl,
    SnpCrlSignatureInvalid,
    SnpCrlIssuerUnauthorized,
    SnpCrlNotCurrent,
    SnpCertificateRevoked,
    SnpSigningKeyNotVcek(u8),
    SnpTcbNotCorroborated,
    SnpTcbBelowFloor,
    SnpChipIdNotCorroborated,
    SnpPolicyReservedBitClear,
    SnpPolicyUnknownBitsSet,
    SnpDebugGuestForbidden,
    SnpMigrationAgentForbidden,
    SnpVmplNotAllowed(u8),
    SnpGuestSvnBelowMinimum { actual: u32, min: u32 },
    // Intel TDX (CAP-26)
    TdxTcbStatusRejected(String),
    TdxServiceTdNotPinned,
    TdxMrtdMismatch,
    TdxRtmrMismatch(u8),
    // NVIDIA GPU (CAP-24 / CAP-26)
    SpdmMalformed,
    SpdmDuplicateBlock(u8),
    SpdmTrailingBytes(usize),
    GpuNonceMismatch,
    GpuMissingFwid,
    GpuFwidCertMismatch,
    GpuFwidRimPinMismatch,
    GpuRimArchMismatch,
    GpuRimVersionMismatch,
    GpuMeasurementMismatch(u8),
    GpuUncoveredMeasurement(u8),
    GpuMissingGoldenMeasurement(u8),
    GpuOcspMissing,
    GpuOcspNotCurrent,
    GpuOcspSignatureInvalid,
    GpuOcspRevoked,
}

impl From<CertChainError> for TeeError {
    fn from(e: CertChainError) -> Self {
        Self::CertChain(e)
    }
}

// ---------------------------------------------------------------------------
// Measurement & Report-Data Binding Helpers
// ---------------------------------------------------------------------------

/// `SHA-256(PCR0 || PCR1 || PCR2)` matching `breadstuffs/tee-verify/src/lib.rs:320`.
pub fn fold_nitro_pcrs(pcr0: &[u8], pcr1: &[u8], pcr2: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(pcr0);
    h.update(pcr1);
    h.update(pcr2);
    h.finalize()
}

/// `SHA-256(MRTD || RTMR0 || RTMR1 || RTMR2)` matching `breadstuffs/tee-verify/src/tdx.rs`.
pub fn fold_tdx_measurement(
    mr_td: &[u8; 48],
    rt_mr0: &[u8; 48],
    rt_mr1: &[u8; 48],
    rt_mr2: &[u8; 48],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(mr_td);
    h.update(rt_mr0);
    h.update(rt_mr1);
    h.update(rt_mr2);
    h.finalize()
}

/// `SHA-256(ascii(nonce_hex) || ascii(e2e_pubkey_b64))` matching `dregg-chutes-e2ee` / `tee-verify/src/tdx.rs`.
pub fn chutes_report_data_binding(nonce_hex: &str, e2e_pubkey_b64: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(nonce_hex.as_bytes());
    h.update(e2e_pubkey_b64.as_bytes());
    h.finalize()
}

fn compute_evidence_digest(
    domain: &[u8],
    measurement: &[u8; 32],
    report_data: &[u8; 64],
    extra: &[u8],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(domain);
    h.update(measurement);
    h.update(report_data);
    h.update(extra);
    h.finalize()
}

// ---------------------------------------------------------------------------
// 1. AWS Nitro Enclaves Gate (CAP-24 + Honest TCB Posture)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwsNitroPolicy {
    pub pinned_root_sha256: [u8; 32],
    pub expected_measurement: [u8; 32],
    pub max_age_secs: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwsNitroAttestation {
    /// `[AWS Nitro Root G1, intermediates..., NSM leaf]`
    pub cert_chain: Vec<CertRecord>,
    pub cose_es384_sig_ok: bool,
    pub doc_timestamp_ms: u64,
    pub pcr0: Vec<u8>,
    pub pcr1: Vec<u8>,
    pub pcr2: Vec<u8>,
    pub user_data: [u8; 64],
}

pub fn verify_aws_nitro(
    policy: &AwsNitroPolicy,
    att: &AwsNitroAttestation,
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    let doc_ts_secs = att.doc_timestamp_ms / 1000;
    verify_rfc5280_cert_chain(&att.cert_chain, &policy.pinned_root_sha256, doc_ts_secs)?;
    if !att.cose_es384_sig_ok {
        return Err(TeeError::ReportSignatureInvalid);
    }
    if let Some(max_age) = policy.max_age_secs {
        if doc_ts_secs > now_secs {
            let ahead = doc_ts_secs - now_secs;
            if ahead > MAX_FUTURE_SKEW_SECS {
                return Err(TeeError::NitroFutureTimestamp { ahead_secs: ahead });
            }
        } else {
            let age = now_secs - doc_ts_secs;
            if age > max_age {
                return Err(TeeError::NitroStaleDoc {
                    age_secs: age,
                    max_age_secs: max_age,
                });
            }
        }
    }
    if att.pcr0.is_empty() {
        return Err(TeeError::NitroMissingPcr(0));
    }
    if att.pcr1.is_empty() {
        return Err(TeeError::NitroMissingPcr(1));
    }
    if att.pcr2.is_empty() {
        return Err(TeeError::NitroMissingPcr(2));
    }
    let measurement = fold_nitro_pcrs(&att.pcr0, &att.pcr1, &att.pcr2);
    if !ct_eq(&measurement, &policy.expected_measurement) {
        return Err(TeeError::MeasurementMismatch);
    }
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.NITRO/v1",
        &measurement,
        &att.user_data,
        &att.doc_timestamp_ms.to_be_bytes(),
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::AwsNitro,
        measurement,
        report_data: att.user_data,
        tcb_posture: TcbPosture::NoPolicyOnPlatform,
        gpu_fwid: None,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 2. AMD SEV-SNP Gate (CAP-24 + CAP-25 Mandatory Non-Expired CRL + TCB Floor)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AmdSnpTcbVersion {
    pub fmc: u8,
    pub bootloader: u8,
    pub tee: u8,
    pub snp: u8,
    pub microcode: u8,
}

impl AmdSnpTcbVersion {
    pub const fn meets(self, floor: Self) -> bool {
        self.fmc >= floor.fmc
            && self.bootloader >= floor.bootloader
            && self.tee >= floor.tee
            && self.snp >= floor.snp
            && self.microcode >= floor.microcode
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmdSnpCrl {
    pub issuer: String,
    pub last_update: u64,
    pub next_update: u64,
    pub revoked_serials: Vec<Vec<u8>>,
    pub sig_verified: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmdSnpPolicy {
    pub product: AmdSnpProduct,
    pub pinned_ark_sha256: [u8; 32],
    pub expected_measurement: [u8; 32],
    pub min_tcb: AmdSnpTcbVersion,
    pub allow_debug: bool,
    pub allow_migration_agent: bool,
    pub max_vmpl: u8,
    pub min_guest_svn: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmdSnpAttestation {
    /// Exact 3-cert AMD chain: `[ARK, ASK, VCEK]`.
    pub cert_chain: Vec<CertRecord>,
    /// Mandatory non-empty list of CRLs (CAP-25: empty list is REFUSED).
    pub crls: Vec<AmdSnpCrl>,
    pub report_sig_ok: bool,
    pub signing_key: u8,
    pub reported_tcb: AmdSnpTcbVersion,
    pub vcek_ext_tcb: AmdSnpTcbVersion,
    pub report_chip_id: [u8; 64],
    pub vcek_ext_hw_id: [u8; 64],
    pub guest_policy: u64,
    pub vmpl: u8,
    pub guest_svn: u32,
    pub launch_measurement: [u8; 48],
    pub report_data: [u8; 64],
}

/// Hardened AMD SEV-SNP verification gate closing **`CAP-24`** & **`CAP-25`**.
pub fn verify_amd_sev_snp(
    policy: &AmdSnpPolicy,
    att: &AmdSnpAttestation,
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    if att.cert_chain.len() != 3 {
        return Err(TeeError::SnpChainLengthInvalid);
    }
    verify_rfc5280_cert_chain(&att.cert_chain, &policy.pinned_ark_sha256, now_secs)?;

    // CAP-25: Mandatory non-empty, verified, non-expired CRL checking both ASK and VCEK.
    if att.crls.is_empty() {
        return Err(TeeError::SnpMissingCrl);
    }
    let ark = &att.cert_chain[0];
    let ask = &att.cert_chain[1];
    let vcek = &att.cert_chain[2];

    for crl in &att.crls {
        let issuer_cert = if crl.issuer == ark.subject {
            ark
        } else if crl.issuer == ask.subject {
            ask
        } else {
            return Err(TeeError::SnpCrlIssuerUnauthorized);
        };
        let issuer_ku = issuer_cert
            .resolved_key_usage()?
            .ok_or(TeeError::SnpCrlIssuerUnauthorized)?;
        if !issuer_ku.crl_sign() {
            return Err(TeeError::SnpCrlIssuerUnauthorized);
        }
        if !crl.sig_verified {
            return Err(TeeError::SnpCrlSignatureInvalid);
        }
        if crl.last_update > now_secs || crl.next_update <= now_secs || crl.last_update >= crl.next_update {
            return Err(TeeError::SnpCrlNotCurrent);
        }
        for revoked in &crl.revoked_serials {
            if revoked == &ask.serial || revoked == &vcek.serial {
                return Err(TeeError::SnpCertificateRevoked);
            }
        }
    }

    if !att.report_sig_ok {
        return Err(TeeError::ReportSignatureInvalid);
    }
    if att.signing_key != SNP_SIGNING_KEY_VCEK {
        return Err(TeeError::SnpSigningKeyNotVcek(att.signing_key));
    }
    if att.reported_tcb != att.vcek_ext_tcb {
        return Err(TeeError::SnpTcbNotCorroborated);
    }
    // CAP-25: Enforce TCB floor directly inside the gate (fail-closed, never returning BelowPolicy).
    if !att.vcek_ext_tcb.meets(policy.min_tcb) {
        return Err(TeeError::SnpTcbBelowFloor);
    }
    if !ct_eq(&att.report_chip_id, &att.vcek_ext_hw_id)
        || att.report_chip_id.iter().all(|&b| b == 0)
    {
        return Err(TeeError::SnpChipIdNotCorroborated);
    }

    let p = att.guest_policy;
    if (p & SNP_POLICY_RESERVED_MBO) == 0 {
        return Err(TeeError::SnpPolicyReservedBitClear);
    }
    if (p & !SNP_POLICY_KNOWN_MASK) != 0 {
        return Err(TeeError::SnpPolicyUnknownBitsSet);
    }
    if (p & SNP_POLICY_DEBUG) != 0 && !policy.allow_debug {
        return Err(TeeError::SnpDebugGuestForbidden);
    }
    if (p & SNP_POLICY_MIGRATE_MA) != 0 && !policy.allow_migration_agent {
        return Err(TeeError::SnpMigrationAgentForbidden);
    }
    if att.vmpl > policy.max_vmpl {
        return Err(TeeError::SnpVmplNotAllowed(att.vmpl));
    }
    if att.guest_svn < policy.min_guest_svn {
        return Err(TeeError::SnpGuestSvnBelowMinimum {
            actual: att.guest_svn,
            min: policy.min_guest_svn,
        });
    }

    let measurement = sha256(&att.launch_measurement);
    if !ct_eq(&measurement, &policy.expected_measurement) {
        return Err(TeeError::MeasurementMismatch);
    }

    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.AMD_SNP/v1",
        &measurement,
        &att.report_data,
        &att.report_chip_id,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::AmdSevSnp(policy.product),
        measurement,
        report_data: att.report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: None,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 3. Intel TDX 1.0/1.5 Gate (CAP-24 + CAP-26 MR_SERVICETD + RTMR Policy Pin)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxMeasurementPin {
    pub mr_td: [u8; 48],
    pub rt_mr0: [u8; 48],
    pub rt_mr1: [u8; 48],
    pub rt_mr2: [u8; 48],
    /// Optional RTMR3 pin (`None` matches Chutes default where RTMR3 is runtime event log).
    pub pin_rtmr3: Option<[u8; 48]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxPolicy {
    pub pinned_intel_root_sha256: [u8; 32],
    pub measurement_pin: IntelTdxMeasurementPin,
    pub accepted_tcb_statuses: Vec<String>,
    /// Allowed nonzero TD 1.5 `MR_SERVICETD` values (`CAP-26`). Empty = only `NO_SERVICE_TD` allowed.
    pub accepted_service_tds: Vec<[u8; 48]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxAttestation {
    /// `[Intel SGX Root CA, Platform/Processor CA, PCK leaf]`
    pub pck_cert_chain: Vec<CertRecord>,
    pub dcap_quote_sig_ok: bool,
    pub tcb_status: String,
    pub mr_td: [u8; 48],
    pub rt_mr0: [u8; 48],
    pub rt_mr1: [u8; 48],
    pub rt_mr2: [u8; 48],
    pub rt_mr3: [u8; 48],
    /// TD 1.5 `MR_SERVICETD` (`None` for TD 1.0 quotes; `Some([0; 48])` for TD 1.5 without service TD).
    pub mr_servicetd: Option<[u8; 48]>,
    pub report_data: [u8; 64],
}

/// Hardened Intel TDX 1.0/1.5 verification gate closing **`CAP-24`** & **`CAP-26`**.
pub fn verify_intel_tdx(
    policy: &IntelTdxPolicy,
    att: &IntelTdxAttestation,
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    // CAP-26: Fail closed on clock error (never silently fall back to 0).
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    verify_rfc5280_cert_chain(&att.pck_cert_chain, &policy.pinned_intel_root_sha256, now_secs)?;
    if !att.dcap_quote_sig_ok {
        return Err(TeeError::ReportSignatureInvalid);
    }
    if !policy.accepted_tcb_statuses.iter().any(|s| s == &att.tcb_status) {
        return Err(TeeError::TdxTcbStatusRejected(att.tcb_status.clone()));
    }

    // CAP-26: Custom TD 1.5 MR_SERVICETD allowlist policy (accepts NO_SERVICE_TD or pinned service TD).
    if let Some(svc_td) = att.mr_servicetd {
        if svc_td != NO_SERVICE_TD
            && !policy.accepted_service_tds.iter().any(|allowed| ct_eq(allowed, &svc_td))
        {
            return Err(TeeError::TdxServiceTdNotPinned);
        }
    }

    // CAP-26: Pin MRTD and RTMR0..2 (plus optional RTMR3).
    let pin = &policy.measurement_pin;
    if !ct_eq(&att.mr_td, &pin.mr_td) {
        return Err(TeeError::TdxMrtdMismatch);
    }
    if !ct_eq(&att.rt_mr0, &pin.rt_mr0) {
        return Err(TeeError::TdxRtmrMismatch(0));
    }
    if !ct_eq(&att.rt_mr1, &pin.rt_mr1) {
        return Err(TeeError::TdxRtmrMismatch(1));
    }
    if !ct_eq(&att.rt_mr2, &pin.rt_mr2) {
        return Err(TeeError::TdxRtmrMismatch(2));
    }
    if let Some(expected_rtmr3) = &pin.pin_rtmr3 {
        if !ct_eq(&att.rt_mr3, expected_rtmr3) {
            return Err(TeeError::TdxRtmrMismatch(3));
        }
    }

    let measurement = fold_tdx_measurement(&att.mr_td, &att.rt_mr0, &att.rt_mr1, &att.rt_mr2);
    let svc_bytes = att.mr_servicetd.unwrap_or(NO_SERVICE_TD);
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.INTEL_TDX/v1",
        &measurement,
        &att.report_data,
        &svc_bytes,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::IntelTdx,
        measurement,
        report_data: att.report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: None,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 4. NVIDIA Hopper (H100) & Blackwell (B200) SPDM + RIM FWID Gate (CAP-24 & CAP-26)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NvidiaOcspStatus {
    Good,
    Revoked,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaOcspResponse {
    pub cert_sha256: [u8; 32],
    pub status: NvidiaOcspStatus,
    pub this_update: u64,
    pub next_update: u64,
    pub sig_verified: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaRimManifest {
    pub arch: GpuArch,
    pub version: String,
    pub cert_chain: Vec<CertRecord>,
    pub rim_sig_ok: bool,
    pub expected_fwid: [u8; 48],
    pub golden_measurements: BTreeMap<u8, Vec<Vec<u8>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaGpuPolicy {
    pub arch: GpuArch,
    pub pinned_device_root_sha256: [u8; 32],
    pub pinned_corim_root_sha256: [u8; 32],
    pub expected_driver_version: String,
    pub expected_vbios_version: String,
    pub pinned_fwid: [u8; 48],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaGpuAttestation {
    /// Raw SPDM 1.1 `GET_MEASUREMENTS` `request(37) || response` wire bytes.
    pub spdm_report_bytes: Vec<u8>,
    /// `[NVIDIA Device Identity CA, intermediates..., Device Attestation Leaf]`
    pub device_cert_chain: Vec<CertRecord>,
    pub spdm_sig_ok: bool,
    pub driver_rim: NvidiaRimManifest,
    pub vbios_rim: NvidiaRimManifest,
    pub ocsp_responses: Vec<NvidiaOcspResponse>,
}

fn check_ocsp_chain_good(
    chain: &[CertRecord],
    start_idx: usize,
    ocsp_responses: &[NvidiaOcspResponse],
    now_secs: u64,
) -> Result<(), TeeError> {
    for cert in &chain[start_idx..] {
        let resp = ocsp_responses
            .iter()
            .find(|r| ct_eq(&r.cert_sha256, &cert.cert_sha256))
            .ok_or(TeeError::GpuOcspMissing)?;
        if !resp.sig_verified {
            return Err(TeeError::GpuOcspSignatureInvalid);
        }
        if resp.this_update > now_secs
            || resp.next_update <= now_secs
            || resp.this_update >= resp.next_update
        {
            return Err(TeeError::GpuOcspNotCurrent);
        }
        if resp.status != NvidiaOcspStatus::Good {
            return Err(TeeError::GpuOcspRevoked);
        }
    }
    Ok(())
}

/// Hardened NVIDIA Hopper (`H100`/`GH100`) & Blackwell (`B200`/`GB200`) SPDM + RIM `FWID` gate,
/// closing **`CAP-24`** & **`CAP-26`**.
pub fn verify_nvidia_gpu(
    policy: &NvidiaGpuPolicy,
    att: &NvidiaGpuAttestation,
    expected_nonce: &[u8; SPDM_NONCE_LEN],
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    // 1. Parse SPDM 1.1 report strictly (exact lengths, unique DMTF blocks, 0 trailing bytes).
    let report = parse_spdm_gpu_report(&att.spdm_report_bytes)?;

    // 2. CAP-24: RFC 5280 BasicConstraints/KeyUsage on device chain + driver RIM + VBIOS RIM.
    verify_rfc5280_cert_chain(
        &att.device_cert_chain,
        &policy.pinned_device_root_sha256,
        now_secs,
    )?;
    if !att.spdm_sig_ok {
        return Err(TeeError::ReportSignatureInvalid);
    }
    if !ct_eq(&report.request_nonce, expected_nonce) {
        return Err(TeeError::GpuNonceMismatch);
    }

    // 3. OCSP revocation check for device chain (non-root certs) and both RIM chains.
    check_ocsp_chain_good(&att.device_cert_chain, 1, &att.ocsp_responses, now_secs)?;

    // 4. Verify driver & VBIOS RIM manifests (chain + sig + OCSP + architecture + version).
    for (rim, expected_ver) in [
        (&att.driver_rim, &policy.expected_driver_version),
        (&att.vbios_rim, &policy.expected_vbios_version),
    ] {
        if rim.arch != policy.arch {
            return Err(TeeError::GpuRimArchMismatch);
        }
        if &rim.version != expected_ver {
            return Err(TeeError::GpuRimVersionMismatch);
        }
        verify_rfc5280_cert_chain(&rim.cert_chain, &policy.pinned_corim_root_sha256, now_secs)?;
        if !rim.rim_sig_ok {
            return Err(TeeError::ReportSignatureInvalid);
        }
        check_ocsp_chain_good(&rim.cert_chain, 1, &att.ocsp_responses, now_secs)?;
    }

    // 5. CAP-26: 3-way FWID pin: SPDM TLV 20 == leaf TCG DICE extension == RIM/policy expected_fwid.
    let spdm_fwid = report.fwid().ok_or(TeeError::GpuMissingFwid)?;
    let leaf = att.device_cert_chain.last().ok_or(TeeError::GpuMissingFwid)?;
    let leaf_ext = leaf
        .dice_fwid_ext_der
        .as_deref()
        .ok_or(TeeError::GpuMissingFwid)?;
    let cert_fwid = extract_der_dice_fwid(leaf_ext).ok_or(TeeError::GpuMissingFwid)?;
    if !ct_eq(&spdm_fwid, &cert_fwid) {
        return Err(TeeError::GpuFwidCertMismatch);
    }
    if !ct_eq(&spdm_fwid, &policy.pinned_fwid)
        || !ct_eq(&spdm_fwid, &att.driver_rim.expected_fwid)
        || !ct_eq(&spdm_fwid, &att.vbios_rim.expected_fwid)
    {
        return Err(TeeError::GpuFwidRimPinMismatch);
    }

    // 6. Merge golden measurements from signed driver & VBIOS RIMs; require 100% coverage.
    let mut merged_goldens: BTreeMap<u8, Vec<Vec<u8>>> = BTreeMap::new();
    for (idx, vals) in &att.driver_rim.golden_measurements {
        merged_goldens.entry(*idx).or_default().extend(vals.iter().cloned());
    }
    for (idx, vals) in &att.vbios_rim.golden_measurements {
        merged_goldens.entry(*idx).or_default().extend(vals.iter().cloned());
    }
    for (&idx, measured) in &report.measurements {
        let Some(accepted) = merged_goldens.get(&idx) else {
            return Err(TeeError::GpuUncoveredMeasurement(idx));
        };
        if !accepted.iter().any(|g| ct_eq(g, measured)) {
            return Err(TeeError::GpuMeasurementMismatch(idx));
        }
    }
    for &idx in merged_goldens.keys() {
        if !report.measurements.contains_key(&idx) {
            return Err(TeeError::GpuMissingGoldenMeasurement(idx));
        }
    }

    // Fold measurement deterministically from (arch_tag, FWID, sorted measurements).
    let mut m_hasher = Sha256::new();
    m_hasher.update(b"OBEND.TEE.NVIDIA_GPU.MEASUREMENT/v1");
    m_hasher.update(policy.arch.rim_product().as_bytes());
    m_hasher.update(&spdm_fwid);
    for (&idx, val) in &report.measurements {
        m_hasher.update(&[idx]);
        m_hasher.update(&(val.len() as u32).to_be_bytes());
        m_hasher.update(val);
    }
    let measurement = m_hasher.finalize();

    // Carry the verified fresh 32-byte SPDM request nonce in report_data[0..32].
    let mut report_data = [0u8; 64];
    report_data[..32].copy_from_slice(&report.request_nonce);
    report_data[32..].copy_from_slice(&report.response_nonce);

    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.NVIDIA_GPU/v1",
        &measurement,
        &report_data,
        &spdm_fwid,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::NvidiaGpu(policy.arch),
        measurement,
        report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: Some(spdm_fwid),
        verified_at: now_secs,
        evidence_digest,
    })
}
