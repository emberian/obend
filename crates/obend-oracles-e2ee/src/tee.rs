//! Hardened Multi-Vendor TEE & GPU Attestation Gate (`CAP-24`, `CAP-25`, `CAP-26` closed) with
//! real spec-compliant binary & ASN.1/CBOR/XML wire parsers and pure-Rust cryptographic signature
//! verification (`0` external crates, `0` boolean shortcuts, `0` synthetic signed preimages):
//! - **RFC 5280 X.509 & CRL + RFC 6960 OCSP** (`CertRecord::from_der`, `AmdSnpCrl::from_der`,
//!   `NvidiaOcspResponse::from_der`).
//! - **AWS Nitro Enclaves**: RFC 9052 CBOR `COSE_Sign1` (`Sig_structure = ["Signature1",
//!   protected_bstr, h"", payload_bstr]`, `ES384` `ECDSA-P384-SHA384`) + CBOR `AttestationDocument`.
//! - **AMD SEV-SNP**: ABI Table 21/22 `1184`-byte (`0x4A0`) `ATTESTATION_REPORT` (`ECDSA-P384-SHA384`
//!   over `report[0x000..0x2A0]`, little-endian 72-byte `r`/`s` @ `0x2A0..0x330`) + real AMD KDS
//!   VCEK OIDs (`1.3.6.1.4.1.3704.1.3.{1,2,3,8,9}`, `1.3.6.1.4.1.3704.1.4`) + mandatory ARK CRL.
//! - **Intel TDX DCAP v4/v5**: `48`-byte `QuoteHeader` + `584`/`648`-byte `TDQuoteBody` +
//!   `384`-byte SGX `EnclaveReportBody` (`ECDSA-P256-SHA256` two-hop `PCK -> QE -> AK -> Quote`
//!   with `qe_report.report_data[0..32] == SHA-256(att_pub_key_64 || qe_auth_data)`).
//! - **NVIDIA Hopper / Blackwell**: SPDM 1.1 `GET_MEASUREMENTS` (`ECDSA-P384-SHA384`) + RFC 6960
//!   OCSP + ISO 19770-2 SWID XML-DSig (`Canonical XML 1.1` + `ecdsa-sha384`) CoRIM manifests.

use std::collections::{BTreeMap, BTreeSet};

use crate::curves::{
    der_encode, der_encode_uint, der_uint, verify_ecdsa_raw, verify_signature, FixtureSigner,
    HashAlg, SignatureAlgorithm, SubjectPublicKey,
};
use crate::sha256::{base64_decode_strict, ct_eq, hex_decode_strict, hex_encode_lower, sha256, Sha256};
use crate::sha512::sha384;

// ---------------------------------------------------------------------------
// Constants, Bitmasks, & ASN.1 OIDs
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

/// Canonical CBOR protected header `{1: -35}` selecting COSE `ES384` (`ECDSA-P384-SHA384`).
pub const COSE_PROTECTED_ES384: &[u8] = &[0xa1, 0x01, 0x38, 0x22];

/// Intel DCAP TDX TEE type (`0x00000081`) and Intel QE vendor UUID (`939a7233...`).
pub const TEE_TYPE_TDX: u32 = 0x0000_0081;
pub const INTEL_QE_VENDOR_ID: [u8; 16] = [
    0x93, 0x9a, 0x72, 0x33, 0xf7, 0x9c, 0x4c, 0xa9, 0x94, 0x0a, 0x0d, 0xb3, 0x95, 0x7f, 0x06, 0x07,
];
pub const TDX_QUOTE_HEADER_LEN: usize = 48;
pub const TDX_TD10_BODY_LEN: usize = 584;
pub const TDX_TD15_BODY_LEN: usize = 648;
pub const SGX_QE_REPORT_BODY_LEN: usize = 384;

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

/// AMD SEV-SNP ABI Table 21/22 `ATTESTATION_REPORT` size (`0x4A0` = 1184 bytes) & signed prefix (`0x2A0` = 672 bytes).
pub const SNP_REPORT_LEN: usize = 1184;
pub const SNP_SIGNED_BODY_LEN: usize = 0x2A0;
pub const SNP_POLICY_SMT: u64 = 1 << 16;
pub const SNP_POLICY_RESERVED_MBO: u64 = 1 << 17;
pub const SNP_POLICY_MIGRATE_MA: u64 = 1 << 18;
pub const SNP_POLICY_DEBUG: u64 = 1 << 19;
pub const SNP_POLICY_SINGLE_SOCKET: u64 = 1 << 20;
pub const SNP_POLICY_CXL_ALLOW: u64 = 1 << 21;
pub const SNP_POLICY_MEM_AES_256_XTS: u64 = 1 << 22;
pub const SNP_POLICY_RAPL_DIS: u64 = 1 << 23;
pub const SNP_POLICY_CIPHERTEXT_HIDING: u64 = 1 << 24;
pub const SNP_POLICY_PAGE_SWAP_DISABLE: u64 = 1 << 25;
pub const SNP_POLICY_KNOWN_MASK: u64 = (1 << 26) - 1;
pub const SNP_SIGNING_KEY_VCEK: u8 = 0;

// Standard X.509 / PKIX / TCG DICE / AMD KDS / OCSP OID content bytes (without 0x06 tag/length).
const OID_COMMON_NAME: &[u8] = &[0x55, 0x04, 0x03]; // 2.5.4.3
const OID_SUBJECT_KEY_ID: &[u8] = &[0x55, 0x1d, 0x0e]; // 2.5.29.14
const OID_KEY_USAGE: &[u8] = &[0x55, 0x1d, 0x0f]; // 2.5.29.15
const OID_BASIC_CONSTRAINTS: &[u8] = &[0x55, 0x1d, 0x13]; // 2.5.29.19
const OID_AUTHORITY_KEY_ID: &[u8] = &[0x55, 0x1d, 0x23]; // 2.5.29.35
const OID_EXT_KEY_USAGE: &[u8] = &[0x55, 0x1d, 0x25]; // 2.5.29.37
const OID_KP_OCSP_SIGNING: &[u8] = &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x09]; // 1.3.6.1.5.5.7.3.9
const OID_OCSP_BASIC: &[u8] = &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x30, 0x01, 0x01]; // 1.3.6.1.5.5.7.48.1.1
const OID_SHA256: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]; // 2.16.840.1.101.3.4.2.1
const OID_SHA384: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02]; // 2.16.840.1.101.3.4.2.2
const OID_TCG_DICE_TCB_INFO: &[u8] = &[0x67, 0x81, 0x05, 0x05, 0x04, 0x01]; // 2.23.133.5.4.1
const OID_TCG_DICE_FWID: &[u8] = &[0x67, 0x81, 0x05, 0x05, 0x04, 0x01, 0x01]; // 2.23.133.5.4.1.1

// Real AMD KDS VCEK X.509 extension OIDs (AMD pub. 57230, arc 1.3.6.1.4.1.3704.1):
const OID_AMD_VCEK_BL_SPL: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x03, 0x01];
const OID_AMD_VCEK_TEE_SPL: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x03, 0x02];
const OID_AMD_VCEK_SNP_SPL: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x03, 0x03];
const OID_AMD_VCEK_UCODE_SPL: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x03, 0x08];
const OID_AMD_VCEK_FMC_SPL: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x03, 0x09];
const OID_AMD_VCEK_HW_ID: &[u8] = &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x9c, 0x78, 0x01, 0x04];

// ---------------------------------------------------------------------------
// Strict ASN.1 DER Primitives, PEM Decoder, & Calendar Time Conversion
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

/// Parse one strict DER TLV returning `(tag, full_raw_tlv, value_slice, rest_slice)`.
fn parse_der_tlv_raw(input: &[u8]) -> Option<(u8, &[u8], &[u8], &[u8])> {
    let &tag = input.first()?;
    if tag & 0x1f == 0x1f {
        return None;
    }
    let &len_byte = input.get(1)?;
    let (len, hdr_len) = if (len_byte & 0x80) == 0 {
        (usize::from(len_byte), 2usize)
    } else {
        let num_octets = usize::from(len_byte & 0x7f);
        if num_octets == 0 || num_octets > 4 {
            return None;
        }
        let len_slice = input.get(2..2 + num_octets)?;
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
    let raw = input.get(..end)?;
    let value = &raw[hdr_len..];
    let rest = input.get(end..)?;
    Some((tag, raw, value, rest))
}

fn parse_der_tlv(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let (tag, _, val, rest) = parse_der_tlv_raw(input)?;
    Some((tag, val, rest))
}

fn parse_der_u8_integer(der: &[u8]) -> Option<u8> {
    let (tag, val, rest) = parse_der_tlv(der)?;
    if tag != 0x02 || !rest.is_empty() {
        return None;
    }
    match val {
        [b] if (*b & 0x80) == 0 => Some(*b),
        [0x00, b] if (*b & 0x80) != 0 => Some(*b),
        _ => None,
    }
}

fn encode_der_u8_integer(v: u8) -> Vec<u8> {
    if (v & 0x80) == 0 {
        vec![0x02, 0x01, v]
    } else {
        vec![0x02, 0x02, 0x00, v]
    }
}

fn base64_encode_std(bytes: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b0 = chunk[0];
        let b1 = *chunk.get(1).unwrap_or(&0);
        let b2 = *chunk.get(2).unwrap_or(&0);
        out.push(TABLE[(b0 >> 2) as usize] as char);
        out.push(TABLE[(((b0 & 0x03) << 4) | (b1 >> 4)) as usize] as char);
        if chunk.len() > 1 {
            out.push(TABLE[(((b1 & 0x0f) << 2) | (b2 >> 6)) as usize] as char);
        } else {
            out.push('=');
        }
        if chunk.len() > 2 {
            out.push(TABLE[(b2 & 0x3f) as usize] as char);
        } else {
            out.push('=');
        }
    }
    out
}

/// Parse one or more PEM `CERTIFICATE` blocks into [`CertRecord`]s (fail-closed on non-cert blocks
/// or non-whitespace garbage outside blocks).
pub fn parse_pem_cert_records(pem_bytes: &[u8]) -> Result<Vec<CertRecord>, CertChainError> {
    const BEGIN: &str = "-----BEGIN CERTIFICATE-----";
    const END: &str = "-----END CERTIFICATE-----";
    let text = std::str::from_utf8(pem_bytes).map_err(|_| CertChainError::MalformedCertDer)?;
    let mut rest = text;
    let mut out = Vec::new();
    while let Some(b_idx) = rest.find("-----BEGIN ") {
        if !rest[..b_idx]
            .bytes()
            .all(|b| b.is_ascii_whitespace() || b == b'#')
        {
            // Allow leading `#` provenance comments at line starts only
            for line in rest[..b_idx].lines() {
                let t = line.trim();
                if !t.is_empty() && !t.starts_with('#') {
                    return Err(CertChainError::MalformedCertDer);
                }
            }
        }
        rest = &rest[b_idx..];
        if !rest.starts_with(BEGIN) {
            return Err(CertChainError::MalformedCertDer);
        }
        rest = &rest[BEGIN.len()..];
        let e_idx = rest.find(END).ok_or(CertChainError::MalformedCertDer)?;
        let b64_clean: String = rest[..e_idx]
            .chars()
            .filter(|c| !c.is_ascii_whitespace())
            .collect();
        let der = base64_decode_strict(&b64_clean).ok_or(CertChainError::MalformedCertDer)?;
        out.push(CertRecord::from_der(&der)?);
        rest = &rest[e_idx + END.len()..];
    }
    for line in rest.lines() {
        let t = line.trim();
        if !t.is_empty() && !t.starts_with('#') {
            return Err(CertChainError::MalformedCertDer);
        }
    }
    if out.is_empty() {
        return Err(CertChainError::EmptyChain);
    }
    Ok(out)
}

fn encode_pem_cert(cert: &CertRecord) -> String {
    let b64 = base64_encode_std(cert.cert_der());
    let mut out = String::from("-----BEGIN CERTIFICATE-----\n");
    for chunk in b64.as_bytes().chunks(64) {
        out.push_str(std::str::from_utf8(chunk).expect("ascii b64"));
        out.push('\n');
    }
    out.push_str("-----END CERTIFICATE-----\n");
    out
}

const fn is_leap_year(y: i64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0)
}

const fn days_in_month(y: i64, m: u32) -> u32 {
    match m {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(y) {
                29
            } else {
                28
            }
        }
        _ => 0,
    }
}

fn civil_to_unix_secs(y: i64, mo: u32, d: u32, h: u32, mi: u32, se: u32) -> Option<u64> {
    if y < 1970 || !(1..=12).contains(&mo) || d < 1 || d > days_in_month(y, mo) {
        return None;
    }
    if h > 23 || mi > 59 || se > 59 {
        return None;
    }
    let yy = if mo <= 2 { y - 1 } else { y };
    let era = yy.div_euclid(400);
    let yoe = yy - era * 400;
    let mp = (i64::from(mo) + 9) % 12;
    let doy = (153 * mp + 2) / 5 + i64::from(d) - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    if days < 0 {
        return None;
    }
    let secs = (days as u64)
        .checked_mul(86_400)?
        .checked_add(u64::from(h) * 3_600 + u64::from(mi) * 60 + u64::from(se))?;
    Some(secs)
}

fn unix_secs_to_civil(ts: u64) -> (i64, u32, u32, u32, u32, u32) {
    let days = (ts / 86_400) as i64;
    let rem = (ts % 86_400) as u32;
    let h = rem / 3_600;
    let mi = (rem % 3_600) / 60;
    let se = rem % 60;

    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let mo = (if mp < 10 { mp + 3 } else { mp - 9 }) as u32;
    let year = if mo <= 2 { y + 1 } else { y };
    (year, mo, d, h, mi, se)
}

/// Parse RFC 5280 §4.1.2.5 `Time` (`UTCTime` for `1970..=2049`, `GeneralizedTime` for `>= 2050`).
fn parse_x509_time_tlv(input: &[u8]) -> Option<(u64, &[u8])> {
    let (tag, val, rest) = parse_der_tlv(input)?;
    let s = std::str::from_utf8(val).ok()?;
    let ts = match tag {
        0x17 => {
            if s.len() != 13 || !s.ends_with('Z') || !s[..12].bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let yy: i64 = s[0..2].parse().ok()?;
            let year = if yy >= 50 { 1900 + yy } else { 2000 + yy };
            let mo: u32 = s[2..4].parse().ok()?;
            let d: u32 = s[4..6].parse().ok()?;
            let h: u32 = s[6..8].parse().ok()?;
            let mi: u32 = s[8..10].parse().ok()?;
            let se: u32 = s[10..12].parse().ok()?;
            civil_to_unix_secs(year, mo, d, h, mi, se)?
        }
        0x18 => {
            if s.len() != 15 || !s.ends_with('Z') || !s[..14].bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let year: i64 = s[0..4].parse().ok()?;
            let mo: u32 = s[4..6].parse().ok()?;
            let d: u32 = s[6..8].parse().ok()?;
            let h: u32 = s[8..10].parse().ok()?;
            let mi: u32 = s[10..12].parse().ok()?;
            let se: u32 = s[12..14].parse().ok()?;
            civil_to_unix_secs(year, mo, d, h, mi, se)?
        }
        _ => return None,
    };
    Some((ts, rest))
}

/// Parse RFC 6960 `GeneralizedTime` (`0x18`, `YYYYMMDDHHMMSSZ`) for OCSP timestamps.
fn parse_ocsp_generalized_time_tlv(input: &[u8]) -> Option<(u64, &[u8])> {
    let (tag, val, rest) = parse_der_tlv(input)?;
    if tag != 0x18 {
        return None;
    }
    let s = std::str::from_utf8(val).ok()?;
    if s.len() != 15 || !s.ends_with('Z') || !s[..14].bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let year: i64 = s[0..4].parse().ok()?;
    let mo: u32 = s[4..6].parse().ok()?;
    let d: u32 = s[6..8].parse().ok()?;
    let h: u32 = s[8..10].parse().ok()?;
    let mi: u32 = s[10..12].parse().ok()?;
    let se: u32 = s[12..14].parse().ok()?;
    Some((civil_to_unix_secs(year, mo, d, h, mi, se)?, rest))
}

fn encode_x509_time_der(ts: u64) -> Vec<u8> {
    let (year, mo, d, h, mi, se) = unix_secs_to_civil(ts);
    if year < 2050 {
        let yy = year % 100;
        let s = format!("{yy:02}{mo:02}{d:02}{h:02}{mi:02}{se:02}Z");
        der_encode(0x17, s.as_bytes())
    } else {
        let s = format!("{year:04}{mo:02}{d:02}{h:02}{mi:02}{se:02}Z");
        der_encode(0x18, s.as_bytes())
    }
}

fn encode_generalized_time_der(ts: u64) -> Vec<u8> {
    let (year, mo, d, h, mi, se) = unix_secs_to_civil(ts);
    let s = format!("{year:04}{mo:02}{d:02}{h:02}{mi:02}{se:02}Z");
    der_encode(0x18, s.as_bytes())
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
        if val != [0xFF] {
            return None;
        }
        is_ca = true;
        cur = rest;
    }
    if !cur.is_empty() {
        if !is_ca {
            return None;
        }
        let (int_tag, val, rest) = parse_der_tlv(cur)?;
        if int_tag != 0x02 || !rest.is_empty() || val.is_empty() || val.len() > 2 {
            return None;
        }
        if (val[0] & 0x80) != 0 {
            return None;
        }
        if val.len() == 2 && (val[0] != 0x00 || (val[1] & 0x80) == 0) {
            return None;
        }
        let n = if val.len() == 1 { val[0] } else { val[1] };
        path_len_constraint = Some(n);
    }
    Some(BasicConstraints {
        is_ca,
        path_len_constraint,
    })
}

/// Encode canonical DER `BasicConstraints` (`cA DEFAULT FALSE` omitted when `false`).
pub fn encode_der_basic_constraints(bc: BasicConstraints) -> Vec<u8> {
    let mut body = Vec::new();
    if bc.is_ca {
        body.extend_from_slice(&[0x01, 0x01, 0xFF]);
    }
    if let Some(p) = bc.path_len_constraint {
        body.extend_from_slice(&der_encode_uint(&[p]));
    }
    der_encode(0x30, &body)
}

/// Strictly parse RFC 5280 `KeyUsage ::= BIT STRING` into bit flags (`KEY_USAGE_*`).
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

/// Encode canonical DER `KeyUsage ::= BIT STRING` with minimal trailing-zero-bit stripping.
pub fn encode_der_key_usage(ku: KeyUsage) -> Vec<u8> {
    let mut b0 = 0u8;
    let mut b1 = 0u8;
    for bit_idx in 0..16u16 {
        if (ku.bits & (1u16 << bit_idx)) != 0 {
            if bit_idx < 8 {
                b0 |= 1u8 << (7 - bit_idx);
            } else {
                b1 |= 1u8 << (15 - bit_idx);
            }
        }
    }
    if b1 != 0 {
        let unused = b1.trailing_zeros() as u8;
        der_encode(0x03, &[unused, b0, b1])
    } else if b0 != 0 {
        let unused = b0.trailing_zeros() as u8;
        der_encode(0x03, &[unused, b0])
    } else {
        der_encode(0x03, &[0x07, 0x00])
    }
}

fn extract_fwid_inner(der: &[u8], depth: usize) -> Option<[u8; 48]> {
    if depth > 6 {
        return None;
    }
    let mut cur = der;
    let mut found: Option<[u8; 48]> = None;
    while !cur.is_empty() {
        let (tag, body, rest) = parse_der_tlv(cur)?;
        if tag == 0x04 && body.len() == 48 {
            let mut fwid = [0u8; 48];
            fwid.copy_from_slice(body);
            if fwid.iter().any(|&b| b != 0) {
                found = Some(fwid);
            }
        } else if tag == 0x30 || tag == 0x31 || (tag & 0xE0) == 0xA0 {
            if let Some(nested) = extract_fwid_inner(body, depth + 1) {
                found = Some(nested);
            }
        }
        cur = rest;
    }
    found
}

/// Extract the 48-byte TCG DICE `FWID` digest from a valid DER-encoded DICE extension value
/// (supporting direct `OCTET STRING(48)`, NVIDIA Hopper nested `SEQUENCE { OID, OCTET STRING(48) }`,
/// and Blackwell `TCBInfo` `fwids [6] IMPLICIT FWIDLIST`).
pub fn extract_der_dice_fwid(ext_value: &[u8]) -> Option<[u8; 48]> {
    let (_, _, trailing) = parse_der_tlv(ext_value)?;
    if !trailing.is_empty() {
        return None;
    }
    extract_fwid_inner(ext_value, 0)
}

fn parse_amd_vcek_hwid(ext_val: &[u8]) -> Option<[u8; 64]> {
    let bytes = if ext_val.len() == 64 || ext_val.len() == 8 {
        ext_val
    } else {
        let (tag, body, rest) = parse_der_tlv(ext_val)?;
        if tag != 0x04 || !rest.is_empty() || (body.len() != 64 && body.len() != 8) {
            return None;
        }
        body
    };
    let mut out = [0u8; 64];
    out[..bytes.len()].copy_from_slice(bytes);
    Some(out)
}

fn parse_x509_serial_bytes(ser_val: &[u8]) -> Option<Vec<u8>> {
    let mag = der_uint(ser_val).ok()?;
    if mag.len() > 20 {
        return None;
    }
    if mag.is_empty() {
        Some(vec![0x00])
    } else {
        Some(mag.to_vec())
    }
}

fn parse_x509_name_der(name_body: &[u8]) -> Option<String> {
    if name_body.is_empty() {
        return None;
    }
    let mut rdns = Vec::new();
    let mut cur = name_body;
    while !cur.is_empty() {
        let (set_tag, set_val, rest) = parse_der_tlv(cur)?;
        if set_tag != 0x31 || set_val.is_empty() {
            return None;
        }
        let mut set_cur = set_val;
        while !set_cur.is_empty() {
            let (seq_tag, seq_val, s_rest) = parse_der_tlv(set_cur)?;
            if seq_tag != 0x30 {
                return None;
            }
            let (oid_tag, oid_val, attr_rest) = parse_der_tlv(seq_val)?;
            let (val_tag, val_bytes, end_rest) = parse_der_tlv(attr_rest)?;
            if oid_tag != 0x06 || !end_rest.is_empty() {
                return None;
            }
            if !matches!(val_tag, 0x0c | 0x13 | 0x16) {
                return None;
            }
            let text = std::str::from_utf8(val_bytes).ok()?;
            if oid_val == OID_COMMON_NAME {
                rdns.push(format!("CN={text}"));
            } else {
                rdns.push(format!("OID({oid_val:02x?})={text}"));
            }
            set_cur = s_rest;
        }
        cur = rest;
    }
    Some(rdns.join(","))
}

fn encode_x509_name_cn(cn: &str) -> Vec<u8> {
    let clean = cn.strip_prefix("CN=").unwrap_or(cn);
    let mut atv = der_encode(0x06, OID_COMMON_NAME);
    atv.extend_from_slice(&der_encode(0x0c, clean.as_bytes()));
    let rdn_seq = der_encode(0x30, &atv);
    let rdn_set = der_encode(0x31, &rdn_seq);
    der_encode(0x30, &rdn_set)
}

// ---------------------------------------------------------------------------
// RFC 5280 Certificate Parsing & Chain Gate (CAP-24 + Real Cryptographic Signatures)
// ---------------------------------------------------------------------------

/// Parsed, unforgeable RFC 5280 DER X.509 certificate (`CertRecord::from_der`).
/// All fields are private so callers cannot fabricate boolean flags or splice unparsed metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertRecord {
    cert_der: Vec<u8>,
    tbs_der: Vec<u8>,
    signature_alg: SignatureAlgorithm,
    signature_bytes: Vec<u8>,
    spki: SubjectPublicKey,
    spki_bitstring_bytes: Vec<u8>,
    subject: String,
    issuer: String,
    subject_der: Vec<u8>,
    issuer_der: Vec<u8>,
    serial: Vec<u8>,
    cert_sha256: [u8; 32],
    not_before: u64,
    not_after: u64,
    basic_constraints: Option<BasicConstraints>,
    key_usage: Option<KeyUsage>,
    has_ocsp_signing_eku: bool,
    eku_only_ocsp: bool,
    dice_fwid: Option<[u8; 48]>,
    amd_vcek_ext: Option<(AmdSnpTcbVersion, [u8; 64])>,
    amd_vcek_has_fmc: bool,
}

impl CertRecord {
    /// Strictly parse a full RFC 5280 DER X.509 `Certificate` (checking outer == inner
    /// `AlgorithmIdentifier`, positive serial, valid `Name`s, valid `SubjectPublicKeyInfo`,
    /// unique extensions, real AMD KDS VCEK OIDs, and refusing unrecognized critical extensions).
    pub fn from_der(cert_der: &[u8]) -> Result<Self, CertChainError> {
        let (outer_tag, _, cert_body, trailing) =
            parse_der_tlv_raw(cert_der).ok_or(CertChainError::MalformedCertDer)?;
        if outer_tag != 0x30 || !trailing.is_empty() {
            return Err(CertChainError::MalformedCertDer);
        }

        let (tbs_tag, tbs_raw, tbs_body, rest) =
            parse_der_tlv_raw(cert_body).ok_or(CertChainError::MalformedCertDer)?;
        if tbs_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let (alg_tag, outer_alg_raw, _, rest) =
            parse_der_tlv_raw(rest).ok_or(CertChainError::MalformedCertDer)?;
        if alg_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let (sig_tag, sig_val, rest) =
            parse_der_tlv(rest).ok_or(CertChainError::MalformedCertDer)?;
        if sig_tag != 0x03 || !rest.is_empty() || sig_val.first() != Some(&0x00) {
            return Err(CertChainError::MalformedCertDer);
        }
        let signature_alg = SignatureAlgorithm::from_algorithm_identifier_der(outer_alg_raw)
            .map_err(|_| CertChainError::UnsupportedSignatureAlgorithm)?;
        let signature_bytes = sig_val[1..].to_vec();

        let mut cur = tbs_body;
        let mut version = 0u8;
        if cur.first() == Some(&0xA0) {
            let (_, ver_box, next) = parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
            let (vtag, vbytes, vrest) =
                parse_der_tlv(ver_box).ok_or(CertChainError::MalformedCertDer)?;
            if vtag != 0x02 || !vrest.is_empty() || vbytes.len() != 1 {
                return Err(CertChainError::MalformedCertDer);
            }
            if vbytes[0] != 1 && vbytes[0] != 2 {
                return Err(CertChainError::MalformedCertDer);
            }
            version = vbytes[0];
            cur = next;
        }

        let (ser_tag, ser_val, next) =
            parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
        if ser_tag != 0x02 {
            return Err(CertChainError::MalformedCertDer);
        }
        let serial_vec =
            parse_x509_serial_bytes(ser_val).ok_or(CertChainError::MalformedCertDer)?;
        cur = next;

        let (in_alg_tag, inner_alg_raw, _, next) =
            parse_der_tlv_raw(cur).ok_or(CertChainError::MalformedCertDer)?;
        if in_alg_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        if inner_alg_raw != outer_alg_raw {
            return Err(CertChainError::SignatureAlgMismatch);
        }
        cur = next;

        let (iss_tag, iss_raw, iss_body, next) =
            parse_der_tlv_raw(cur).ok_or(CertChainError::MalformedCertDer)?;
        if iss_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let issuer = parse_x509_name_der(iss_body).ok_or(CertChainError::MalformedCertDer)?;
        cur = next;

        let (val_tag, val_body, next) =
            parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
        if val_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let (not_before, val_rest) =
            parse_x509_time_tlv(val_body).ok_or(CertChainError::MalformedCertDer)?;
        let (not_after, val_end) =
            parse_x509_time_tlv(val_rest).ok_or(CertChainError::MalformedCertDer)?;
        if !val_end.is_empty() || not_before > not_after {
            return Err(CertChainError::MalformedCertDer);
        }
        cur = next;

        let (sub_tag, sub_raw, sub_body, next) =
            parse_der_tlv_raw(cur).ok_or(CertChainError::MalformedCertDer)?;
        if sub_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let subject = parse_x509_name_der(sub_body).ok_or(CertChainError::MalformedCertDer)?;
        cur = next;

        let (spki_tag, spki_raw, spki_body, next) =
            parse_der_tlv_raw(cur).ok_or(CertChainError::MalformedCertDer)?;
        if spki_tag != 0x30 {
            return Err(CertChainError::MalformedCertDer);
        }
        let spki = SubjectPublicKey::from_spki_der(spki_raw)
            .map_err(|_| CertChainError::MalformedSpkiDer)?;
        let (_, _, spki_rest) = parse_der_tlv(spki_body).ok_or(CertChainError::MalformedSpkiDer)?;
        let (pk_bs_tag, pk_bs, spki_end) =
            parse_der_tlv(spki_rest).ok_or(CertChainError::MalformedSpkiDer)?;
        if pk_bs_tag != 0x03 || !spki_end.is_empty() || pk_bs.first() != Some(&0x00) {
            return Err(CertChainError::MalformedSpkiDer);
        }
        let spki_bitstring_bytes = pk_bs[1..].to_vec();
        cur = next;

        if cur.first() == Some(&0x81) {
            if version < 1 {
                return Err(CertChainError::MalformedCertDer);
            }
            let (_, _, next) = parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
            cur = next;
        }
        if cur.first() == Some(&0x82) {
            if version < 1 {
                return Err(CertChainError::MalformedCertDer);
            }
            let (_, _, next) = parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
            cur = next;
        }

        let mut basic_constraints = None;
        let mut key_usage = None;
        let mut has_ocsp_signing_eku = false;
        let mut eku_only_ocsp = false;
        let mut dice_fwid = None;
        let mut amd_bl = None;
        let mut amd_tee = None;
        let mut amd_snp = None;
        let mut amd_ucode = None;
        let mut amd_fmc = None;
        let mut amd_hwid = None;

        if !cur.is_empty() {
            if version != 2 {
                return Err(CertChainError::MalformedCertDer);
            }
            let (ext_ctx_tag, ext_ctx_body, trailing_tbs) =
                parse_der_tlv(cur).ok_or(CertChainError::MalformedCertDer)?;
            if ext_ctx_tag != 0xA3 || !trailing_tbs.is_empty() {
                return Err(CertChainError::MalformedCertDer);
            }
            let (exts_tag, exts_body, exts_end) =
                parse_der_tlv(ext_ctx_body).ok_or(CertChainError::MalformedCertDer)?;
            if exts_tag != 0x30 || !exts_end.is_empty() || exts_body.is_empty() {
                return Err(CertChainError::MalformedCertDer);
            }
            let mut seen_oids = BTreeSet::new();
            let mut ext_cur = exts_body;
            while !ext_cur.is_empty() {
                let (etag, ebody, erest) =
                    parse_der_tlv(ext_cur).ok_or(CertChainError::MalformedCertDer)?;
                if etag != 0x30 {
                    return Err(CertChainError::MalformedCertDer);
                }
                let (oid_tag, oid_bytes, mut inner) =
                    parse_der_tlv(ebody).ok_or(CertChainError::MalformedCertDer)?;
                if oid_tag != 0x06 || oid_bytes.is_empty() {
                    return Err(CertChainError::MalformedCertDer);
                }
                if !seen_oids.insert(oid_bytes.to_vec()) {
                    return Err(CertChainError::DuplicateExtension);
                }
                let mut critical = false;
                if inner.first() == Some(&0x01) {
                    let (_, bval, next_in) =
                        parse_der_tlv(inner).ok_or(CertChainError::MalformedCertDer)?;
                    if bval != [0xFF] {
                        return Err(CertChainError::MalformedCertDer);
                    }
                    critical = true;
                    inner = next_in;
                }
                let (vtag, extn_val, end_in) =
                    parse_der_tlv(inner).ok_or(CertChainError::MalformedCertDer)?;
                if vtag != 0x04 || !end_in.is_empty() {
                    return Err(CertChainError::MalformedCertDer);
                }

                if oid_bytes == OID_BASIC_CONSTRAINTS {
                    basic_constraints = Some(
                        parse_der_basic_constraints(extn_val)
                            .ok_or(CertChainError::MalformedBasicConstraintsDer)?,
                    );
                } else if oid_bytes == OID_KEY_USAGE {
                    key_usage = Some(
                        parse_der_key_usage(extn_val)
                            .ok_or(CertChainError::MalformedKeyUsageDer)?,
                    );
                } else if oid_bytes == OID_EXT_KEY_USAGE {
                    let (st, sbody, srest) =
                        parse_der_tlv(extn_val).ok_or(CertChainError::MalformedCertDer)?;
                    if st != 0x30 || !srest.is_empty() || sbody.is_empty() {
                        return Err(CertChainError::MalformedCertDer);
                    }
                    let mut kp_cur = sbody;
                    let mut saw_non_ocsp = false;
                    while !kp_cur.is_empty() {
                        let (kt, kval, krest) =
                            parse_der_tlv(kp_cur).ok_or(CertChainError::MalformedCertDer)?;
                        if kt != 0x06 || kval.is_empty() {
                            return Err(CertChainError::MalformedCertDer);
                        }
                        if kval == OID_KP_OCSP_SIGNING {
                            has_ocsp_signing_eku = true;
                        } else {
                            saw_non_ocsp = true;
                        }
                        kp_cur = krest;
                    }
                    eku_only_ocsp = has_ocsp_signing_eku && !saw_non_ocsp;
                } else if oid_bytes == OID_TCG_DICE_TCB_INFO || oid_bytes == OID_TCG_DICE_FWID {
                    dice_fwid = Some(
                        extract_der_dice_fwid(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_BL_SPL {
                    amd_bl = Some(
                        parse_der_u8_integer(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_TEE_SPL {
                    amd_tee = Some(
                        parse_der_u8_integer(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_SNP_SPL {
                    amd_snp = Some(
                        parse_der_u8_integer(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_UCODE_SPL {
                    amd_ucode = Some(
                        parse_der_u8_integer(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_FMC_SPL {
                    amd_fmc = Some(
                        parse_der_u8_integer(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_AMD_VCEK_HW_ID {
                    amd_hwid = Some(
                        parse_amd_vcek_hwid(extn_val).ok_or(CertChainError::MalformedCertDer)?,
                    );
                } else if oid_bytes == OID_SUBJECT_KEY_ID || oid_bytes == OID_AUTHORITY_KEY_ID {
                    let (_, _, r) =
                        parse_der_tlv(extn_val).ok_or(CertChainError::MalformedCertDer)?;
                    if !r.is_empty() {
                        return Err(CertChainError::MalformedCertDer);
                    }
                    if critical {
                        return Err(CertChainError::UnsupportedCriticalExtension);
                    }
                } else if critical {
                    return Err(CertChainError::UnsupportedCriticalExtension);
                }

                ext_cur = erest;
            }
        }

        let any_amd = amd_bl.is_some()
            || amd_tee.is_some()
            || amd_snp.is_some()
            || amd_ucode.is_some()
            || amd_fmc.is_some()
            || amd_hwid.is_some();
        let amd_vcek_has_fmc = amd_fmc.is_some();
        let amd_vcek_ext = if any_amd {
            let (Some(bootloader), Some(tee), Some(snp), Some(microcode), Some(hw_id)) =
                (amd_bl, amd_tee, amd_snp, amd_ucode, amd_hwid)
            else {
                return Err(CertChainError::MalformedCertDer);
            };
            Some((
                AmdSnpTcbVersion {
                    fmc: amd_fmc.unwrap_or(0),
                    bootloader,
                    tee,
                    snp,
                    microcode,
                },
                hw_id,
            ))
        } else {
            None
        };

        Ok(Self {
            cert_der: cert_der.to_vec(),
            tbs_der: tbs_raw.to_vec(),
            signature_alg,
            signature_bytes,
            spki,
            spki_bitstring_bytes,
            subject,
            issuer,
            subject_der: sub_raw.to_vec(),
            issuer_der: iss_raw.to_vec(),
            serial: serial_vec,
            cert_sha256: sha256(cert_der),
            not_before,
            not_after,
            basic_constraints,
            key_usage,
            has_ocsp_signing_eku,
            eku_only_ocsp,
            dice_fwid,
            amd_vcek_ext,
            amd_vcek_has_fmc,
        })
    }

    pub fn cert_der(&self) -> &[u8] {
        &self.cert_der
    }
    pub fn tbs_der(&self) -> &[u8] {
        &self.tbs_der
    }
    pub fn signature_alg(&self) -> SignatureAlgorithm {
        self.signature_alg
    }
    pub fn signature_bytes(&self) -> &[u8] {
        &self.signature_bytes
    }
    pub fn spki(&self) -> &SubjectPublicKey {
        &self.spki
    }
    pub fn spki_bitstring_bytes(&self) -> &[u8] {
        &self.spki_bitstring_bytes
    }
    pub fn subject(&self) -> &str {
        &self.subject
    }
    pub fn issuer(&self) -> &str {
        &self.issuer
    }
    pub fn subject_der(&self) -> &[u8] {
        &self.subject_der
    }
    pub fn issuer_der(&self) -> &[u8] {
        &self.issuer_der
    }
    pub fn serial(&self) -> &[u8] {
        &self.serial
    }
    pub fn cert_sha256(&self) -> [u8; 32] {
        self.cert_sha256
    }
    pub fn not_before(&self) -> u64 {
        self.not_before
    }
    pub fn not_after(&self) -> u64 {
        self.not_after
    }
    pub fn basic_constraints(&self) -> Option<BasicConstraints> {
        self.basic_constraints
    }
    pub fn key_usage(&self) -> Option<KeyUsage> {
        self.key_usage
    }
    pub fn has_ocsp_signing_eku(&self) -> bool {
        self.has_ocsp_signing_eku
    }
    pub fn dice_fwid(&self) -> Option<[u8; 48]> {
        self.dice_fwid
    }
    pub fn amd_vcek_ext(&self) -> Option<(AmdSnpTcbVersion, [u8; 64])> {
        self.amd_vcek_ext
    }
    pub fn amd_vcek_has_fmc(&self) -> bool {
        self.amd_vcek_has_fmc
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertChainError {
    InvalidClock,
    EmptyChain,
    SingleCertChainDisallowed,
    MalformedCertDer,
    MalformedSpkiDer,
    SignatureAlgMismatch,
    UnsupportedSignatureAlgorithm,
    DuplicateExtension,
    UnsupportedCriticalExtension,
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
/// against `pinned_root_sha256` at `now_secs`, closing **`CAP-24`** with real cryptographic
/// `verify_signature` verification at every link (including root self-signature).
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
    if root.subject_der != root.issuer_der {
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
        if i == 0 {
            verify_signature(
                &root.spki,
                root.signature_alg,
                &root.tbs_der,
                &root.signature_bytes,
            )
            .map_err(|_| CertChainError::BadChainSignature { index: 0 })?;
        } else {
            let issuer_cert = &chain_root_to_leaf[i - 1];
            if cert.issuer_der != issuer_cert.subject_der {
                return Err(CertChainError::IssuerSubjectMismatch { index: i });
            }
            verify_signature(
                &issuer_cert.spki,
                cert.signature_alg,
                &cert.tbs_der,
                &cert.signature_bytes,
            )
            .map_err(|_| CertChainError::BadChainSignature { index: i })?;
        }

        if i < last {
            let Some(bc) = cert.basic_constraints else {
                return Err(CertChainError::MissingCaBasicConstraints { index: i });
            };
            if !bc.is_ca {
                return Err(CertChainError::NonCaIssuer { index: i });
            }
            let ku = cert
                .key_usage
                .ok_or(CertChainError::MissingKeyCertSign { index: i })?;
            if !ku.key_cert_sign() {
                return Err(CertChainError::MissingKeyCertSign { index: i });
            }
            if let Some(max_len) = bc.path_len_constraint {
                ca_path_lens.push((i, max_len));
            }
        } else {
            if let Some(bc) = cert.basic_constraints {
                if bc.is_ca {
                    return Err(CertChainError::LeafMustNotBeCa);
                }
            }
            if cert.eku_only_ocsp {
                return Err(CertChainError::LeafMissingDigitalSignature);
            }
            match cert.key_usage {
                Some(ku) => {
                    if !ku.digital_signature() {
                        return Err(CertChainError::LeafMissingDigitalSignature);
                    }
                }
                // AMD KDS Milan/Genoa VCEK leaf profile omits KeyUsage while carrying AMD VCEK OIDs.
                None if cert.amd_vcek_ext.is_some() => {}
                None => return Err(CertChainError::LeafMissingDigitalSignature),
            }
        }
    }

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

pub fn parse_spdm_gpu_report(report: &[u8]) -> Result<SpdmGpuReport, TeeError> {
    if report.len() <= SPDM_REQUEST_LEN + SPDM_SIGNATURE_LEN {
        return Err(TeeError::SpdmMalformed);
    }
    let (req, resp) = report.split_at(SPDM_REQUEST_LEN);
    if req[0] != 0x11 || req[1] != SPDM_GET_MEASUREMENTS_REQUEST {
        return Err(TeeError::SpdmMalformed);
    }
    let mut request_nonce = [0u8; SPDM_NONCE_LEN];
    request_nonce.copy_from_slice(&req[4..4 + SPDM_NONCE_LEN]);

    let mut at = 0usize;
    let hdr = spdm_take(resp, &mut at, 4)?;
    if hdr[0] != 0x11 || hdr[1] != SPDM_MEASUREMENTS_RESPONSE {
        return Err(TeeError::SpdmMalformed);
    }
    let nblocks = usize::from(spdm_take(resp, &mut at, 1)?[0]);
    if nblocks == 0 {
        return Err(TeeError::SpdmMalformed);
    }
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
    let mut seen_opaque = BTreeSet::new();
    let mut o = 0usize;
    while o < opaque_bytes.len() {
        let ty = spdm_le(spdm_take(opaque_bytes, &mut o, 2)?) as u16;
        if !seen_opaque.insert(ty) {
            return Err(TeeError::SpdmMalformed);
        }
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
    VerifiedFloor,
    NoPolicyOnPlatform,
}

/// Sealed, unforgeable verified TEE / confidential-GPU attestation token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedTeeEvidence {
    vendor: TeeVendor,
    measurement: [u8; 32],
    report_data: [u8; 64],
    tcb_posture: TcbPosture,
    gpu_fwid: Option<[u8; 48]>,
    policy_root_sha256: [u8; 32],
    leaf_spki_sha256: [u8; 32],
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
    pub fn policy_root_sha256(&self) -> [u8; 32] {
        self.policy_root_sha256
    }
    pub fn leaf_spki_sha256(&self) -> [u8; 32] {
        self.leaf_spki_sha256
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
    // Nitro (RFC 9052 COSE_Sign1 + CBOR AttDoc)
    NitroMalformedCose,
    NitroMalformedCoseHeader,
    NitroMalformedPayload,
    NitroMissingPcr(u8),
    NitroInconsistentPcrWidth,
    NitroFutureTimestamp { ahead_secs: u64 },
    NitroStaleDoc { age_secs: u64, max_age_secs: u64 },
    // AMD SEV-SNP (CAP-25, 1184-byte ABI Table 21/22 report)
    SnpMalformedReport,
    SnpChainLengthInvalid,
    SnpMissingCrl,
    SnpMissingArkCrl,
    SnpMalformedCrlDer,
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
    // Intel TDX (CAP-26, DCAP v4/v5 binary Quote)
    TdxMalformedQuote,
    TdxDebugTdForbidden,
    TdxQeReportSignatureInvalid,
    TdxTcbStatusRejected(String),
    TdxServiceTdNotPinned,
    TdxMrtdMismatch,
    TdxRtmrMismatch(u8),
    // NVIDIA GPU (CAP-24 / CAP-26, SPDM 1.1 + OCSP + SWID XML-DSig RIM)
    SpdmMalformed,
    SpdmDuplicateBlock(u8),
    SpdmTrailingBytes(usize),
    GpuNonceMismatch,
    GpuMissingFwid,
    GpuFwidCertMismatch,
    GpuFwidRimPinMismatch,
    GpuMalformedRimXml,
    GpuRimArchMismatch,
    GpuRimVersionMismatch,
    GpuMeasurementMismatch(u8),
    GpuUncoveredMeasurement(u8),
    GpuMissingGoldenMeasurement(u8),
    GpuMalformedOcspDer,
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
// 1. AWS Nitro Enclaves Gate (Real RFC 9052 CBOR COSE_Sign1 ES384 + AttDoc)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwsNitroPolicy {
    pub pinned_root_sha256: [u8; 32],
    pub expected_measurement: [u8; 32],
    pub max_age_secs: Option<u64>,
}

/// Real AWS Nitro Enclaves attestation document (`COSE_Sign1` CBOR binary wire format).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwsNitroAttestation {
    pub cose_sign1_bytes: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CborVal {
    Uint(u64),
    Nint(i64),
    Bytes(Vec<u8>),
    Text(String),
    Array(Vec<CborVal>),
    Map(Vec<(CborVal, CborVal)>),
    Null,
    Bool(bool),
}

const MAX_NITRO_CBOR_BYTES: usize = 256 * 1024;
const MAX_CBOR_DEPTH: usize = 8;

fn cbor_read_arg(buf: &[u8], pos: &mut usize, ai: u8) -> Option<Option<u64>> {
    match ai {
        0..=23 => Some(Some(u64::from(ai))),
        24 => {
            let v = *buf.get(*pos)?;
            *pos += 1;
            if v < 24 {
                return None;
            }
            Some(Some(u64::from(v)))
        }
        25 => {
            let s = buf.get(*pos..*pos + 2)?;
            *pos += 2;
            let v = u16::from_be_bytes([s[0], s[1]]);
            if v <= 0xff {
                return None;
            }
            Some(Some(u64::from(v)))
        }
        26 => {
            let s = buf.get(*pos..*pos + 4)?;
            *pos += 4;
            let v = u32::from_be_bytes([s[0], s[1], s[2], s[3]]);
            if v <= 0xffff {
                return None;
            }
            Some(Some(u64::from(v)))
        }
        27 => {
            let s = buf.get(*pos..*pos + 8)?;
            *pos += 8;
            let v = u64::from_be_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
            if v <= 0xffff_ffff {
                return None;
            }
            Some(Some(v))
        }
        31 => Some(None),
        _ => None,
    }
}

fn cbor_decode_item(buf: &[u8], pos: &mut usize, depth: usize) -> Option<CborVal> {
    if depth > MAX_CBOR_DEPTH {
        return None;
    }
    let ib = *buf.get(*pos)?;
    *pos += 1;
    if ib == 0xff {
        return None;
    }
    let mt = ib >> 5;
    let ai = ib & 0x1f;
    match mt {
        0 => Some(CborVal::Uint(cbor_read_arg(buf, pos, ai)??)),
        1 => {
            let n = cbor_read_arg(buf, pos, ai)??;
            let v = -1i64 - i64::try_from(n).ok()?;
            Some(CborVal::Nint(v))
        }
        2 => {
            let len = usize::try_from(cbor_read_arg(buf, pos, ai)??).ok()?;
            let end = pos.checked_add(len)?;
            let slice = buf.get(*pos..end)?;
            *pos = end;
            Some(CborVal::Bytes(slice.to_vec()))
        }
        3 => {
            let len = usize::try_from(cbor_read_arg(buf, pos, ai)??).ok()?;
            let end = pos.checked_add(len)?;
            let slice = buf.get(*pos..end)?;
            *pos = end;
            let s = std::str::from_utf8(slice).ok()?.to_owned();
            Some(CborVal::Text(s))
        }
        4 => {
            let maybe_len = cbor_read_arg(buf, pos, ai)?;
            let mut items = Vec::new();
            match maybe_len {
                Some(len) => {
                    let n = usize::try_from(len).ok()?;
                    if n > 4096 {
                        return None;
                    }
                    for _ in 0..n {
                        items.push(cbor_decode_item(buf, pos, depth + 1)?);
                    }
                }
                None => loop {
                    if *buf.get(*pos)? == 0xff {
                        *pos += 1;
                        break;
                    }
                    if items.len() >= 4096 {
                        return None;
                    }
                    items.push(cbor_decode_item(buf, pos, depth + 1)?);
                },
            }
            Some(CborVal::Array(items))
        }
        5 => {
            let maybe_len = cbor_read_arg(buf, pos, ai)?;
            let mut entries: Vec<(CborVal, CborVal)> = Vec::new();
            let push_unique = |entries: &mut Vec<(CborVal, CborVal)>, k: CborVal, v: CborVal| -> Option<()> {
                if entries.iter().any(|(ek, _)| ek == &k) {
                    return None;
                }
                entries.push((k, v));
                Some(())
            };
            match maybe_len {
                Some(len) => {
                    let n = usize::try_from(len).ok()?;
                    if n > 4096 {
                        return None;
                    }
                    for _ in 0..n {
                        let k = cbor_decode_item(buf, pos, depth + 1)?;
                        let v = cbor_decode_item(buf, pos, depth + 1)?;
                        push_unique(&mut entries, k, v)?;
                    }
                }
                None => loop {
                    if *buf.get(*pos)? == 0xff {
                        *pos += 1;
                        break;
                    }
                    if entries.len() >= 4096 {
                        return None;
                    }
                    let k = cbor_decode_item(buf, pos, depth + 1)?;
                    let v = cbor_decode_item(buf, pos, depth + 1)?;
                    push_unique(&mut entries, k, v)?;
                },
            }
            Some(CborVal::Map(entries))
        }
        6 => {
            let tag_num = cbor_read_arg(buf, pos, ai)??;
            // Only RFC 9052 tag 18 (`COSE_Sign1`) is permitted at top level.
            if tag_num != 18 || depth != 0 {
                return None;
            }
            cbor_decode_item(buf, pos, depth + 1)
        }
        7 => match ai {
            20 => Some(CborVal::Bool(false)),
            21 => Some(CborVal::Bool(true)),
            22 => Some(CborVal::Null),
            _ => None,
        },
        _ => None,
    }
}

fn cbor_decode_exact(buf: &[u8]) -> Option<CborVal> {
    if buf.is_empty() || buf.len() > MAX_NITRO_CBOR_BYTES {
        return None;
    }
    let mut pos = 0usize;
    let v = cbor_decode_item(buf, &mut pos, 0)?;
    if pos != buf.len() {
        return None;
    }
    Some(v)
}

fn cbor_push_head(out: &mut Vec<u8>, mt: u8, n: u64) {
    let base = mt << 5;
    if n < 24 {
        out.push(base | (n as u8));
    } else if n <= 0xff {
        out.extend_from_slice(&[base | 24, n as u8]);
    } else if n <= 0xffff {
        out.push(base | 25);
        out.extend_from_slice(&(n as u16).to_be_bytes());
    } else if n <= 0xffff_ffff {
        out.push(base | 26);
        out.extend_from_slice(&(n as u32).to_be_bytes());
    } else {
        out.push(base | 27);
        out.extend_from_slice(&n.to_be_bytes());
    }
}

fn cbor_push_bstr(out: &mut Vec<u8>, bytes: &[u8]) {
    cbor_push_head(out, 2, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

fn cbor_push_tstr(out: &mut Vec<u8>, s: &str) {
    cbor_push_head(out, 3, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

/// Canonical RFC 9052 §4.4 `Sig_structure` (`["Signature1", body_protected, h"", payload]`).
pub fn aws_nitro_cose_sig_structure(protected_header: &[u8], payload: &[u8]) -> Vec<u8> {
    let mut sig_structure = Vec::with_capacity(24 + protected_header.len() + payload.len());
    sig_structure.push(0x84); // CBOR array(4)
    cbor_push_tstr(&mut sig_structure, "Signature1");
    cbor_push_bstr(&mut sig_structure, protected_header);
    sig_structure.push(0x40); // empty external_aad bstr(0)
    cbor_push_bstr(&mut sig_structure, payload);
    sig_structure
}

fn map_get<'a>(entries: &'a [(CborVal, CborVal)], key: &str) -> Option<&'a CborVal> {
    entries.iter().find_map(|(k, v)| match k {
        CborVal::Text(s) if s == key => Some(v),
        _ => None,
    })
}

/// Verify a real RFC 9052 CBOR `COSE_Sign1` AWS Nitro Enclaves attestation document against
/// `policy.pinned_root_sha256` (`ES384` `ECDSA-P384-SHA384` + X.509 `cabundle` + `PCR0..2` pin).
pub fn verify_aws_nitro(
    policy: &AwsNitroPolicy,
    att: &AwsNitroAttestation,
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    let top = cbor_decode_exact(&att.cose_sign1_bytes).ok_or(TeeError::NitroMalformedCose)?;
    let CborVal::Array(cose_elems) = top else {
        return Err(TeeError::NitroMalformedCose);
    };
    if cose_elems.len() != 4 {
        return Err(TeeError::NitroMalformedCose);
    }
    let CborVal::Bytes(protected) = &cose_elems[0] else {
        return Err(TeeError::NitroMalformedCose);
    };
    let CborVal::Map(unprotected) = &cose_elems[1] else {
        return Err(TeeError::NitroMalformedCose);
    };
    let CborVal::Bytes(payload) = &cose_elems[2] else {
        return Err(TeeError::NitroMalformedCose);
    };
    let CborVal::Bytes(signature) = &cose_elems[3] else {
        return Err(TeeError::NitroMalformedCose);
    };
    if protected.as_slice() != COSE_PROTECTED_ES384 || !unprotected.is_empty() {
        return Err(TeeError::NitroMalformedCoseHeader);
    }
    if signature.len() != 96 {
        return Err(TeeError::ReportSignatureInvalid);
    }

    let doc_val = cbor_decode_exact(payload).ok_or(TeeError::NitroMalformedPayload)?;
    let CborVal::Map(doc_map) = doc_val else {
        return Err(TeeError::NitroMalformedPayload);
    };

    let Some(CborVal::Text(module_id)) = map_get(&doc_map, "module_id") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    if module_id.is_empty() {
        return Err(TeeError::NitroMalformedPayload);
    }
    let Some(CborVal::Text(digest_alg)) = map_get(&doc_map, "digest") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    if digest_alg != "SHA384" {
        return Err(TeeError::NitroMalformedPayload);
    }
    let Some(&CborVal::Uint(doc_timestamp_ms)) = map_get(&doc_map, "timestamp") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    let doc_ts_secs = doc_timestamp_ms / 1000;
    if doc_ts_secs == 0 {
        return Err(TeeError::NitroMalformedPayload);
    }

    let Some(CborVal::Bytes(leaf_der)) = map_get(&doc_map, "certificate") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    let Some(CborVal::Array(cabundle_vals)) = map_get(&doc_map, "cabundle") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    if cabundle_vals.is_empty() {
        return Err(TeeError::NitroMalformedPayload);
    }
    let mut cert_chain = Vec::with_capacity(cabundle_vals.len() + 1);
    for item in cabundle_vals {
        let CborVal::Bytes(c_der) = item else {
            return Err(TeeError::NitroMalformedPayload);
        };
        cert_chain.push(CertRecord::from_der(c_der)?);
    }
    cert_chain.push(CertRecord::from_der(leaf_der)?);
    verify_rfc5280_cert_chain(&cert_chain, &policy.pinned_root_sha256, doc_ts_secs)?;
    let leaf = cert_chain
        .last()
        .ok_or(TeeError::CertChain(CertChainError::EmptyChain))?;

    let sig_structure = aws_nitro_cose_sig_structure(protected, payload);
    verify_ecdsa_raw(
        leaf.spki(),
        SignatureAlgorithm::EcdsaP384Sha384,
        &sig_structure,
        signature,
    )
    .map_err(|_| TeeError::ReportSignatureInvalid)?;

    if doc_ts_secs > now_secs {
        let ahead = doc_ts_secs - now_secs;
        if ahead > MAX_FUTURE_SKEW_SECS {
            return Err(TeeError::NitroFutureTimestamp { ahead_secs: ahead });
        }
    } else if let Some(max_age) = policy.max_age_secs {
        let age = now_secs - doc_ts_secs;
        if age > max_age {
            return Err(TeeError::NitroStaleDoc {
                age_secs: age,
                max_age_secs: max_age,
            });
        }
    }
    // Enforce AWS attestation §3.2.3.1: certificate chain MUST also be valid at `now_secs`!
    verify_rfc5280_cert_chain(&cert_chain, &policy.pinned_root_sha256, now_secs)?;

    let Some(CborVal::Map(pcr_entries)) = map_get(&doc_map, "pcrs") else {
        return Err(TeeError::NitroMalformedPayload);
    };
    let mut expected_pcr_width: Option<usize> = None;
    for (pk, pv) in pcr_entries {
        let (CborVal::Uint(idx), CborVal::Bytes(b)) = (pk, pv) else {
            return Err(TeeError::NitroMalformedPayload);
        };
        if *idx > 31 || !matches!(b.len(), 32 | 48 | 64) {
            return Err(TeeError::NitroInconsistentPcrWidth);
        }
        if let Some(w) = expected_pcr_width {
            if b.len() != w {
                return Err(TeeError::NitroInconsistentPcrWidth);
            }
        } else {
            expected_pcr_width = Some(b.len());
        }
    }
    let get_pcr = |idx: u8| -> Result<&[u8], TeeError> {
        pcr_entries
            .iter()
            .find_map(|(k, v)| match (k, v) {
                (CborVal::Uint(i), CborVal::Bytes(b)) if *i == u64::from(idx) => Some(b.as_slice()),
                _ => None,
            })
            .ok_or(TeeError::NitroMissingPcr(idx))
    };
    let pcr0 = get_pcr(0)?;
    let pcr1 = get_pcr(1)?;
    let pcr2 = get_pcr(2)?;

    // Optional fields type-checked (`public_key`, `nonce`, `user_data`).
    if let Some(v) = map_get(&doc_map, "public_key") {
        if !matches!(v, CborVal::Bytes(_) | CborVal::Null) {
            return Err(TeeError::NitroMalformedPayload);
        }
    }
    if let Some(v) = map_get(&doc_map, "nonce") {
        if !matches!(v, CborVal::Bytes(_) | CborVal::Null) {
            return Err(TeeError::NitroMalformedPayload);
        }
    }
    let ud_slice: &[u8] = match map_get(&doc_map, "user_data") {
        None | Some(CborVal::Null) => &[],
        Some(CborVal::Bytes(b)) if b.len() <= 512 => b.as_slice(),
        _ => return Err(TeeError::NitroMalformedPayload),
    };
    let mut user_data = [0u8; 64];
    let copy_len = ud_slice.len().min(64);
    user_data[..copy_len].copy_from_slice(&ud_slice[..copy_len]);

    let measurement = fold_nitro_pcrs(pcr0, pcr1, pcr2);
    if !ct_eq(&measurement, &policy.expected_measurement) {
        return Err(TeeError::MeasurementMismatch);
    }

    let leaf_spki_sha256 = sha256(&leaf.spki().to_spki_der());
    let mut extra = Vec::with_capacity(88 + ud_slice.len());
    extra.extend_from_slice(&policy.pinned_root_sha256);
    extra.extend_from_slice(&leaf_spki_sha256);
    extra.extend_from_slice(&doc_timestamp_ms.to_be_bytes());
    extra.extend_from_slice(&(ud_slice.len() as u64).to_be_bytes());
    extra.extend_from_slice(ud_slice);
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.EVIDENCE.NITRO/v1",
        &measurement,
        &user_data,
        &extra,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::AwsNitro,
        measurement,
        report_data: user_data,
        tcb_posture: TcbPosture::NoPolicyOnPlatform,
        gpu_fwid: None,
        policy_root_sha256: policy.pinned_root_sha256,
        leaf_spki_sha256,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 2. AMD SEV-SNP Gate (Real 1184-Byte ABI Table 21/22 Report + DER CRL + VCEK)
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

    pub const fn from_amd_report_bytes(b: [u8; 8], product: AmdSnpProduct) -> Self {
        match product {
            AmdSnpProduct::Milan | AmdSnpProduct::Genoa => Self {
                fmc: 0,
                bootloader: b[0],
                tee: b[1],
                snp: b[6],
                microcode: b[7],
            },
            AmdSnpProduct::Turin => Self {
                fmc: b[0],
                bootloader: b[1],
                tee: b[2],
                snp: b[3],
                microcode: b[7],
            },
        }
    }

    pub const fn to_amd_report_bytes(self, product: AmdSnpProduct) -> [u8; 8] {
        let mut b = [0u8; 8];
        match product {
            AmdSnpProduct::Milan | AmdSnpProduct::Genoa => {
                b[0] = self.bootloader;
                b[1] = self.tee;
                b[6] = self.snp;
                b[7] = self.microcode;
            }
            AmdSnpProduct::Turin => {
                b[0] = self.fmc;
                b[1] = self.bootloader;
                b[2] = self.tee;
                b[3] = self.snp;
                b[7] = self.microcode;
            }
        }
        b
    }
}

/// Parsed, unforgeable RFC 5280 DER `CertificateList` (CRL) for AMD SEV-SNP (`AmdSnpCrl::from_der`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmdSnpCrl {
    tbs_der: Vec<u8>,
    signature_alg: SignatureAlgorithm,
    signature_bytes: Vec<u8>,
    issuer: String,
    issuer_der: Vec<u8>,
    last_update: u64,
    next_update: u64,
    revoked_serials: Vec<Vec<u8>>,
}

impl AmdSnpCrl {
    pub fn from_der(crl_der: &[u8]) -> Result<Self, TeeError> {
        let (outer_tag, _, crl_body, trailing) =
            parse_der_tlv_raw(crl_der).ok_or(TeeError::SnpMalformedCrlDer)?;
        if outer_tag != 0x30 || !trailing.is_empty() {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        let (tbs_tag, tbs_raw, tbs_body, rest) =
            parse_der_tlv_raw(crl_body).ok_or(TeeError::SnpMalformedCrlDer)?;
        if tbs_tag != 0x30 {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        let (alg_tag, outer_alg_raw, _, rest) =
            parse_der_tlv_raw(rest).ok_or(TeeError::SnpMalformedCrlDer)?;
        if alg_tag != 0x30 {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        let (sig_tag, sig_val, rest) =
            parse_der_tlv(rest).ok_or(TeeError::SnpMalformedCrlDer)?;
        if sig_tag != 0x03 || !rest.is_empty() || sig_val.first() != Some(&0x00) {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        let signature_alg = SignatureAlgorithm::from_algorithm_identifier_der(outer_alg_raw)
            .map_err(|_| TeeError::SnpMalformedCrlDer)?;
        let signature_bytes = sig_val[1..].to_vec();

        let mut cur = tbs_body;
        let mut version = 0u8;
        if cur.first() == Some(&0x02) {
            let (_, vval, next) = parse_der_tlv(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
            if vval != [0x01] {
                return Err(TeeError::SnpMalformedCrlDer);
            }
            version = 1;
            cur = next;
        }
        let (in_alg_tag, inner_alg_raw, _, next) =
            parse_der_tlv_raw(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
        if in_alg_tag != 0x30 || inner_alg_raw != outer_alg_raw {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        cur = next;

        let (iss_tag, iss_raw, iss_body, next) =
            parse_der_tlv_raw(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
        if iss_tag != 0x30 {
            return Err(TeeError::SnpMalformedCrlDer);
        }
        let issuer = parse_x509_name_der(iss_body).ok_or(TeeError::SnpMalformedCrlDer)?;
        cur = next;

        let (last_update, next) =
            parse_x509_time_tlv(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
        let (next_update, mut cur) =
            parse_x509_time_tlv(next).ok_or(TeeError::SnpMalformedCrlDer)?;

        let mut revoked_serials = Vec::new();
        if cur.first() == Some(&0x30) {
            let (_, rev_body, next) = parse_der_tlv(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
            if rev_body.is_empty() {
                return Err(TeeError::SnpMalformedCrlDer);
            }
            let mut rcur = rev_body;
            while !rcur.is_empty() {
                let (etag, ebody, rnext) =
                    parse_der_tlv(rcur).ok_or(TeeError::SnpMalformedCrlDer)?;
                if etag != 0x30 {
                    return Err(TeeError::SnpMalformedCrlDer);
                }
                let (stag, sval, erest) =
                    parse_der_tlv(ebody).ok_or(TeeError::SnpMalformedCrlDer)?;
                if stag != 0x02 {
                    return Err(TeeError::SnpMalformedCrlDer);
                }
                let ser =
                    parse_x509_serial_bytes(sval).ok_or(TeeError::SnpMalformedCrlDer)?;
                let (_, erest) =
                    parse_x509_time_tlv(erest).ok_or(TeeError::SnpMalformedCrlDer)?;
                if !erest.is_empty() {
                    let (ext_tag, ext_seq, end_r) =
                        parse_der_tlv(erest).ok_or(TeeError::SnpMalformedCrlDer)?;
                    if ext_tag != 0x30 || !end_r.is_empty() {
                        return Err(TeeError::SnpMalformedCrlDer);
                    }
                    check_no_critical_extensions(ext_seq)
                        .map_err(|_| TeeError::SnpMalformedCrlDer)?;
                }
                revoked_serials.push(ser);
                rcur = rnext;
            }
            cur = next;
        }
        if !cur.is_empty() {
            if version != 1 {
                return Err(TeeError::SnpMalformedCrlDer);
            }
            let (ctag, cbody, cend) = parse_der_tlv(cur).ok_or(TeeError::SnpMalformedCrlDer)?;
            if ctag != 0xA0 || !cend.is_empty() {
                return Err(TeeError::SnpMalformedCrlDer);
            }
            let (stag, sbody, send) = parse_der_tlv(cbody).ok_or(TeeError::SnpMalformedCrlDer)?;
            if stag != 0x30 || !send.is_empty() {
                return Err(TeeError::SnpMalformedCrlDer);
            }
            check_no_critical_extensions(sbody).map_err(|_| TeeError::SnpMalformedCrlDer)?;
        }

        Ok(Self {
            tbs_der: tbs_raw.to_vec(),
            signature_alg,
            signature_bytes,
            issuer,
            issuer_der: iss_raw.to_vec(),
            last_update,
            next_update,
            revoked_serials,
        })
    }

    pub fn issuer(&self) -> &str {
        &self.issuer
    }
    pub fn issuer_der(&self) -> &[u8] {
        &self.issuer_der
    }
    pub fn last_update(&self) -> u64 {
        self.last_update
    }
    pub fn next_update(&self) -> u64 {
        self.next_update
    }
    pub fn revoked_serials(&self) -> &[Vec<u8>] {
        &self.revoked_serials
    }
    pub fn tbs_der(&self) -> &[u8] {
        &self.tbs_der
    }
    pub fn signature_alg(&self) -> SignatureAlgorithm {
        self.signature_alg
    }
    pub fn signature_bytes(&self) -> &[u8] {
        &self.signature_bytes
    }
}

fn check_no_critical_extensions(mut cur: &[u8]) -> Result<(), ()> {
    if cur.is_empty() {
        return Err(());
    }
    while !cur.is_empty() {
        let (etag, ebody, erest) = parse_der_tlv(cur).ok_or(())?;
        if etag != 0x30 {
            return Err(());
        }
        let (otag, _, inner) = parse_der_tlv(ebody).ok_or(())?;
        if otag != 0x06 {
            return Err(());
        }
        if inner.first() == Some(&0x01) {
            let _ = parse_der_tlv(inner).ok_or(())?;
            return Err(());
        }
        let (vtag, _, end_in) = parse_der_tlv(inner).ok_or(())?;
        if vtag != 0x04 || !end_in.is_empty() {
            return Err(());
        }
        cur = erest;
    }
    Ok(())
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
    /// Raw 1184-byte (`0x4A0`) AMD SEV-SNP ABI Table 21/22 `ATTESTATION_REPORT`.
    pub report_bytes: Vec<u8>,
    /// Exact 3-cert AMD KDS chain: `[ARK, ASK, VCEK]`.
    pub cert_chain: Vec<CertRecord>,
    /// Mandatory non-empty list of RFC 5280 DER-parsed CRLs (`CAP-25`).
    pub crls: Vec<AmdSnpCrl>,
}

/// Parsed fields of an AMD SEV-SNP ABI Table 21/22 `1184`-byte `ATTESTATION_REPORT`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedAmdSnpReport {
    pub version: u32,
    pub guest_svn: u32,
    pub guest_policy: u64,
    pub family_id: [u8; 16],
    pub image_id: [u8; 16],
    pub vmpl: u8,
    pub signature_algo: u32,
    pub current_tcb: AmdSnpTcbVersion,
    pub platform_info: u64,
    pub signing_key: u8,
    pub report_data: [u8; 64],
    pub launch_measurement: [u8; 48],
    pub host_data: [u8; 32],
    pub reported_tcb: AmdSnpTcbVersion,
    pub chip_id: [u8; 64],
    /// Big-endian `r || s` (96 bytes) converted from AMD's two 72-byte little-endian fields.
    pub signature_be: [u8; 96],
}

fn le_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

fn le_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes([
        b[off],
        b[off + 1],
        b[off + 2],
        b[off + 3],
        b[off + 4],
        b[off + 5],
        b[off + 6],
        b[off + 7],
    ])
}

/// Parse the real 1184-byte (`0x4A0`) AMD SEV-SNP ABI Table 21/22 `ATTESTATION_REPORT`.
pub fn parse_amd_snp_report(
    bytes: &[u8],
    product: AmdSnpProduct,
) -> Result<ParsedAmdSnpReport, TeeError> {
    if bytes.len() != SNP_REPORT_LEN {
        return Err(TeeError::SnpMalformedReport);
    }
    let version = le_u32(bytes, 0x000);
    if !matches!(version, 2 | 3 | 5) {
        return Err(TeeError::SnpMalformedReport);
    }
    let guest_svn = le_u32(bytes, 0x004);
    let guest_policy = le_u64(bytes, 0x008);
    let mut family_id = [0u8; 16];
    family_id.copy_from_slice(&bytes[0x010..0x020]);
    let mut image_id = [0u8; 16];
    image_id.copy_from_slice(&bytes[0x020..0x030]);
    let vmpl_u32 = le_u32(bytes, 0x030);
    if vmpl_u32 > 3 {
        return Err(TeeError::SnpMalformedReport);
    }
    let signature_algo = le_u32(bytes, 0x034);
    if signature_algo != 1 {
        return Err(TeeError::ReportSignatureInvalid);
    }
    let mut cur_tcb_raw = [0u8; 8];
    cur_tcb_raw.copy_from_slice(&bytes[0x038..0x040]);
    let platform_info = le_u64(bytes, 0x040);
    let key_info = le_u32(bytes, 0x048);
    let signing_key = ((key_info >> 2) & 0b111) as u8;

    let mut report_data = [0u8; 64];
    report_data.copy_from_slice(&bytes[0x050..0x090]);
    let mut launch_measurement = [0u8; 48];
    launch_measurement.copy_from_slice(&bytes[0x090..0x0C0]);
    let mut host_data = [0u8; 32];
    host_data.copy_from_slice(&bytes[0x0C0..0x0E0]);
    let mut rep_tcb_raw = [0u8; 8];
    rep_tcb_raw.copy_from_slice(&bytes[0x180..0x188]);
    let mut chip_id = [0u8; 64];
    chip_id.copy_from_slice(&bytes[0x1A0..0x1E0]);

    // AMD SEV-SNP ABI Table 23 `SIGNATURE`: `r` @ `0x2A0..0x2E8` (72B LE), `s` @ `0x2E8..0x330` (72B LE),
    // reserved `0x330..0x4A0` (368B MBZ). Upper 24 bytes of each 72-byte scalar MUST be zero.
    let r_le = &bytes[0x2A0..0x2E8];
    let s_le = &bytes[0x2E8..0x330];
    if r_le[48..].iter().any(|&b| b != 0)
        || s_le[48..].iter().any(|&b| b != 0)
        || bytes[0x330..0x4A0].iter().any(|&b| b != 0)
    {
        return Err(TeeError::ReportSignatureInvalid);
    }
    let mut signature_be = [0u8; 96];
    for i in 0..48 {
        signature_be[i] = r_le[47 - i];
        signature_be[48 + i] = s_le[47 - i];
    }

    Ok(ParsedAmdSnpReport {
        version,
        guest_svn,
        guest_policy,
        family_id,
        image_id,
        vmpl: vmpl_u32 as u8,
        signature_algo,
        current_tcb: AmdSnpTcbVersion::from_amd_report_bytes(cur_tcb_raw, product),
        platform_info,
        signing_key,
        report_data,
        launch_measurement,
        host_data,
        reported_tcb: AmdSnpTcbVersion::from_amd_report_bytes(rep_tcb_raw, product),
        chip_id,
        signature_be,
    })
}

/// Hardened AMD SEV-SNP verification gate over the real `1184`-byte `ATTESTATION_REPORT` (`CAP-24`/`25`).
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
    let report = parse_amd_snp_report(&att.report_bytes, policy.product)?;
    verify_rfc5280_cert_chain(&att.cert_chain, &policy.pinned_ark_sha256, now_secs)?;

    if att.crls.is_empty() {
        return Err(TeeError::SnpMissingCrl);
    }
    let ark = &att.cert_chain[0];
    let ask = &att.cert_chain[1];
    let vcek = &att.cert_chain[2];

    let mut has_ark_crl = false;
    for crl in &att.crls {
        let (issuer_cert, is_ark) = if crl.issuer_der() == ark.subject_der() {
            (ark, true)
        } else if crl.issuer_der() == ask.subject_der() {
            (ask, false)
        } else {
            return Err(TeeError::SnpCrlIssuerUnauthorized);
        };
        let issuer_ku = issuer_cert
            .key_usage()
            .ok_or(TeeError::SnpCrlIssuerUnauthorized)?;
        if !issuer_ku.crl_sign() {
            return Err(TeeError::SnpCrlIssuerUnauthorized);
        }
        verify_signature(
            issuer_cert.spki(),
            crl.signature_alg(),
            crl.tbs_der(),
            crl.signature_bytes(),
        )
        .map_err(|_| TeeError::SnpCrlSignatureInvalid)?;
        if crl.last_update() > now_secs
            || crl.next_update() <= now_secs
            || crl.last_update() >= crl.next_update()
        {
            return Err(TeeError::SnpCrlNotCurrent);
        }
        if is_ark {
            has_ark_crl = true;
            for revoked in crl.revoked_serials() {
                if revoked.as_slice() == ask.serial() || revoked.as_slice() == vcek.serial() {
                    return Err(TeeError::SnpCertificateRevoked);
                }
            }
        } else {
            for revoked in crl.revoked_serials() {
                if revoked.as_slice() == vcek.serial() {
                    return Err(TeeError::SnpCertificateRevoked);
                }
            }
        }
    }
    if !has_ark_crl {
        return Err(TeeError::SnpMissingArkCrl);
    }

    if report.signing_key != SNP_SIGNING_KEY_VCEK {
        return Err(TeeError::SnpSigningKeyNotVcek(report.signing_key));
    }
    verify_ecdsa_raw(
        vcek.spki(),
        SignatureAlgorithm::EcdsaP384Sha384,
        &att.report_bytes[..SNP_SIGNED_BODY_LEN],
        &report.signature_be,
    )
    .map_err(|_| TeeError::ReportSignatureInvalid)?;

    let Some((cert_tcb, cert_hw_id)) = vcek.amd_vcek_ext() else {
        return Err(TeeError::SnpTcbNotCorroborated);
    };
    if policy.product == AmdSnpProduct::Turin && !vcek.amd_vcek_has_fmc() {
        return Err(TeeError::SnpTcbNotCorroborated);
    }
    if report.reported_tcb != cert_tcb {
        return Err(TeeError::SnpTcbNotCorroborated);
    }
    if !cert_tcb.meets(policy.min_tcb) {
        return Err(TeeError::SnpTcbBelowFloor);
    }
    if !ct_eq(&report.chip_id, &cert_hw_id) || report.chip_id.iter().all(|&b| b == 0) {
        return Err(TeeError::SnpChipIdNotCorroborated);
    }

    let p = report.guest_policy;
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
    if report.vmpl > policy.max_vmpl {
        return Err(TeeError::SnpVmplNotAllowed(report.vmpl));
    }
    if report.guest_svn < policy.min_guest_svn {
        return Err(TeeError::SnpGuestSvnBelowMinimum {
            actual: report.guest_svn,
            min: policy.min_guest_svn,
        });
    }

    let measurement = sha256(&report.launch_measurement);
    if !ct_eq(&measurement, &policy.expected_measurement) {
        return Err(TeeError::MeasurementMismatch);
    }

    let leaf_spki_sha256 = sha256(&vcek.spki().to_spki_der());
    let mut extra = Vec::with_capacity(160);
    extra.extend_from_slice(&policy.pinned_ark_sha256);
    extra.extend_from_slice(&leaf_spki_sha256);
    extra.extend_from_slice(&report.chip_id);
    extra.extend_from_slice(&cert_tcb.to_amd_report_bytes(policy.product));
    extra.extend_from_slice(&report.guest_policy.to_le_bytes());
    extra.push(report.vmpl);
    extra.extend_from_slice(&report.guest_svn.to_le_bytes());
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.EVIDENCE.AMD_SNP/v1",
        &measurement,
        &report.report_data,
        &extra,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::AmdSevSnp(policy.product),
        measurement,
        report_data: report.report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: None,
        policy_root_sha256: policy.pinned_ark_sha256,
        leaf_spki_sha256,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 3. Intel TDX DCAP v4/v5 Binary Quote Gate (`48`B Header + `584`/`648`B Body + `384`B QE)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxMeasurementPin {
    pub mr_td: [u8; 48],
    pub rt_mr0: [u8; 48],
    pub rt_mr1: [u8; 48],
    pub rt_mr2: [u8; 48],
    pub pin_rtmr3: Option<[u8; 48]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxPolicy {
    pub pinned_intel_root_sha256: [u8; 32],
    pub measurement_pin: IntelTdxMeasurementPin,
    pub accepted_tcb_statuses: Vec<String>,
    pub accepted_service_tds: Vec<[u8; 48]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntelTdxAttestation {
    /// Raw Intel DCAP v4/v5 TDX Quote binary (`QuoteHeader(48)` + `TDQuoteBody(584/648)` +
    /// `Ecdsa256BitQuoteAuthData` carrying `quote_sig`, `att_pub_key_64`, `EnclaveReportBody(384)`,
    /// `qe_report_sig`, `qe_auth_data`, and PEM PCK certificate chain).
    pub quote_bytes: Vec<u8>,
    pub tcb_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedIntelTdxQuote {
    pub version: u16,
    pub tee_tcb_svn: [u8; 16],
    pub mr_seam: [u8; 48],
    pub td_attributes: u64,
    pub xfam: u64,
    pub mr_td: [u8; 48],
    pub mr_config_id: [u8; 48],
    pub mr_owner: [u8; 48],
    pub mr_owner_config: [u8; 48],
    pub rt_mr0: [u8; 48],
    pub rt_mr1: [u8; 48],
    pub rt_mr2: [u8; 48],
    pub rt_mr3: [u8; 48],
    pub report_data: [u8; 64],
    pub tee_tcb_svn2: Option<[u8; 16]>,
    pub mr_servicetd: Option<[u8; 48]>,
    pub signed_quote_len: usize,
    pub quote_signature: [u8; 64],
    pub att_pub_key_64: [u8; 64],
    pub qe_report_body: [u8; SGX_QE_REPORT_BODY_LEN],
    pub qe_report_signature: [u8; 64],
    pub qe_auth_data: Vec<u8>,
    pub pck_cert_chain_root_to_leaf: Vec<CertRecord>,
}

/// Parse the real Intel DCAP v4 / v5 TDX Quote binary layout.
pub fn parse_intel_tdx_quote(quote: &[u8]) -> Result<ParsedIntelTdxQuote, TeeError> {
    if quote.len() < TDX_QUOTE_HEADER_LEN + TDX_TD10_BODY_LEN + 4 {
        return Err(TeeError::TdxMalformedQuote);
    }
    let version = u16::from_le_bytes([quote[0], quote[1]]);
    let att_key_type = u16::from_le_bytes([quote[2], quote[3]]);
    let tee_type = le_u32(quote, 4);
    if att_key_type != 2 || tee_type != TEE_TYPE_TDX {
        return Err(TeeError::TdxMalformedQuote);
    }
    if quote[12..28] != INTEL_QE_VENDOR_ID {
        return Err(TeeError::TdxMalformedQuote);
    }

    let (body, signed_quote_len, tee_tcb_svn2, mr_servicetd) = match version {
        4 => (&quote[48..632], 632usize, None, None),
        5 => {
            if quote.len() < 54 + TDX_TD10_BODY_LEN + 4 {
                return Err(TeeError::TdxMalformedQuote);
            }
            let body_type = u16::from_le_bytes([quote[48], quote[49]]);
            let body_size = le_u32(quote, 50) as usize;
            match (body_type, body_size) {
                (2, TDX_TD10_BODY_LEN) => (&quote[54..54 + TDX_TD10_BODY_LEN], 54 + TDX_TD10_BODY_LEN, None, None),
                (3, TDX_TD15_BODY_LEN) => {
                    let end = 54 + TDX_TD15_BODY_LEN;
                    let b = quote.get(54..end).ok_or(TeeError::TdxMalformedQuote)?;
                    let mut svn2 = [0u8; 16];
                    svn2.copy_from_slice(&b[584..600]);
                    let mut svc = [0u8; 48];
                    svc.copy_from_slice(&b[600..648]);
                    (b, end, Some(svn2), Some(svc))
                }
                _ => return Err(TeeError::TdxMalformedQuote),
            }
        }
        _ => return Err(TeeError::TdxMalformedQuote),
    };

    let grab48 = |off: usize| -> [u8; 48] {
        let mut a = [0u8; 48];
        a.copy_from_slice(&body[off..off + 48]);
        a
    };
    let mut tee_tcb_svn = [0u8; 16];
    tee_tcb_svn.copy_from_slice(&body[0..16]);
    let mr_seam = grab48(16);
    let td_attributes = le_u64(body, 120);
    let xfam = le_u64(body, 128);
    let mr_td = grab48(136);
    let mr_config_id = grab48(184);
    let mr_owner = grab48(232);
    let mr_owner_config = grab48(280);
    let rt_mr0 = grab48(328);
    let rt_mr1 = grab48(376);
    let rt_mr2 = grab48(424);
    let rt_mr3 = grab48(472);
    let mut report_data = [0u8; 64];
    report_data.copy_from_slice(&body[520..584]);

    let sig_len_end = signed_quote_len
        .checked_add(4)
        .ok_or(TeeError::TdxMalformedQuote)?;
    if quote.len() < sig_len_end {
        return Err(TeeError::TdxMalformedQuote);
    }
    let sig_data_len = le_u32(quote, signed_quote_len) as usize;
    let auth_end = sig_len_end
        .checked_add(sig_data_len)
        .ok_or(TeeError::TdxMalformedQuote)?;
    let auth = quote
        .get(sig_len_end..auth_end)
        .ok_or(TeeError::TdxMalformedQuote)?;
    // `/dev/tdx_guest` buffers may carry trailing NUL padding after `sig_data_len`; any non-zero
    // trailing byte is rejected.
    if quote[auth_end..].iter().any(|&b| b != 0) {
        return Err(TeeError::TdxMalformedQuote);
    }
    if auth.len() < 64 + 64 + 6 {
        return Err(TeeError::TdxMalformedQuote);
    }

    let mut quote_signature = [0u8; 64];
    quote_signature.copy_from_slice(&auth[0..64]);
    let mut att_pub_key_64 = [0u8; 64];
    att_pub_key_64.copy_from_slice(&auth[64..128]);

    // Outer CertificationData: type 6 (`QE_REPORT_CERT_DATA`)
    let outer_cert_type = u16::from_le_bytes([auth[128], auth[129]]);
    let outer_cert_size = le_u32(auth, 130) as usize;
    if outer_cert_type != 6 || 134usize.checked_add(outer_cert_size) != Some(auth.len()) {
        return Err(TeeError::TdxMalformedQuote);
    }
    let qe_box = &auth[134..];
    if qe_box.len() < SGX_QE_REPORT_BODY_LEN + 64 + 2 + 6 {
        return Err(TeeError::TdxMalformedQuote);
    }
    let mut qe_report_body = [0u8; SGX_QE_REPORT_BODY_LEN];
    qe_report_body.copy_from_slice(&qe_box[0..SGX_QE_REPORT_BODY_LEN]);
    let mut qe_report_signature = [0u8; 64];
    qe_report_signature.copy_from_slice(&qe_box[SGX_QE_REPORT_BODY_LEN..SGX_QE_REPORT_BODY_LEN + 64]);
    let auth_sz_off = SGX_QE_REPORT_BODY_LEN + 64;
    let auth_sz = u16::from_le_bytes([qe_box[auth_sz_off], qe_box[auth_sz_off + 1]]) as usize;
    let auth_data_start = auth_sz_off + 2;
    let auth_data_end = auth_data_start
        .checked_add(auth_sz)
        .ok_or(TeeError::TdxMalformedQuote)?;
    let qe_auth_data = qe_box
        .get(auth_data_start..auth_data_end)
        .ok_or(TeeError::TdxMalformedQuote)?
        .to_vec();

    let inner_hdr = qe_box
        .get(auth_data_end..auth_data_end + 6)
        .ok_or(TeeError::TdxMalformedQuote)?;
    let inner_cert_type = u16::from_le_bytes([inner_hdr[0], inner_hdr[1]]);
    let inner_cert_size = u32::from_le_bytes([inner_hdr[2], inner_hdr[3], inner_hdr[4], inner_hdr[5]]) as usize;
    let pem_start = auth_data_end + 6;
    if inner_cert_type != 5 || pem_start.checked_add(inner_cert_size) != Some(qe_box.len()) {
        return Err(TeeError::TdxMalformedQuote);
    }
    let pem_slice = &qe_box[pem_start..];
    let pem_trimmed = match pem_slice.iter().position(|&b| b == 0) {
        Some(z) => {
            if pem_slice[z..].iter().any(|&b| b != 0) {
                return Err(TeeError::TdxMalformedQuote);
            }
            &pem_slice[..z]
        }
        None => pem_slice,
    };
    let mut certs = parse_pem_cert_records(pem_trimmed)?;
    // DCAP quote cert_type=5 carries `[PCK Leaf, PCK CA, Intel SGX Root CA]`; normalize to root-first.
    if certs.len() >= 2
        && certs[0].subject_der() != certs[0].issuer_der()
        && certs.last().is_some_and(|c| c.subject_der() == c.issuer_der())
    {
        certs.reverse();
    }

    Ok(ParsedIntelTdxQuote {
        version,
        tee_tcb_svn,
        mr_seam,
        td_attributes,
        xfam,
        mr_td,
        mr_config_id,
        mr_owner,
        mr_owner_config,
        rt_mr0,
        rt_mr1,
        rt_mr2,
        rt_mr3,
        report_data,
        tee_tcb_svn2,
        mr_servicetd,
        signed_quote_len,
        quote_signature,
        att_pub_key_64,
        qe_report_body,
        qe_report_signature,
        qe_auth_data,
        pck_cert_chain_root_to_leaf: certs,
    })
}

/// Hardened Intel TDX 1.0/1.5 verification gate over the real DCAP v4/v5 binary Quote (`CAP-24`/`26`).
pub fn verify_intel_tdx(
    policy: &IntelTdxPolicy,
    att: &IntelTdxAttestation,
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    let q = parse_intel_tdx_quote(&att.quote_bytes)?;
    // TDX `TD_ATTRIBUTES` bit 0 (`TUD.DEBUG`) allows host VMM debug access; always refuse.
    if (q.td_attributes & 1) != 0 {
        return Err(TeeError::TdxDebugTdForbidden);
    }

    verify_rfc5280_cert_chain(
        &q.pck_cert_chain_root_to_leaf,
        &policy.pinned_intel_root_sha256,
        now_secs,
    )?;
    let pck_leaf = q
        .pck_cert_chain_root_to_leaf
        .last()
        .ok_or(TeeError::CertChain(CertChainError::EmptyChain))?;

    // 1. Refuse SGX debug QE enclaves (`ATTRIBUTES.DEBUG` bit 1 @ offset 48) and verify PCK leaf's
    //    ECDSA-P256-SHA256 signature over the 384-byte SGX `EnclaveReportBody`.
    if (q.qe_report_body[48] & 0x02) != 0 {
        return Err(TeeError::TdxQeReportSignatureInvalid);
    }
    verify_ecdsa_raw(
        pck_leaf.spki(),
        SignatureAlgorithm::EcdsaP256Sha256,
        &q.qe_report_body,
        &q.qe_report_signature,
    )
    .map_err(|_| TeeError::TdxQeReportSignatureInvalid)?;

    // 2. Enforce DCAP attestation-key binding: `qe_report.report_data[0..32] == SHA-256(att_pub_key_64 || qe_auth_data)`
    //    and `qe_report.report_data[32..64] == 0`.
    let mut ak_hash = Sha256::new();
    ak_hash.update(&q.att_pub_key_64);
    ak_hash.update(&q.qe_auth_data);
    let expected_qe_rd = ak_hash.finalize();
    if !ct_eq(&q.qe_report_body[320..352], &expected_qe_rd)
        || q.qe_report_body[352..384].iter().any(|&b| b != 0)
    {
        return Err(TeeError::TdxQeReportSignatureInvalid);
    }

    // 3. Verify `att_pub_key_64` (strict SEC1 on-curve P-256) signed `quote_bytes[0..signed_quote_len]`.
    let mut att_sec1 = [0u8; 65];
    att_sec1[0] = 0x04;
    att_sec1[1..].copy_from_slice(&q.att_pub_key_64);
    let att_spki = SubjectPublicKey::P256(att_sec1);
    verify_ecdsa_raw(
        &att_spki,
        SignatureAlgorithm::EcdsaP256Sha256,
        &att.quote_bytes[..q.signed_quote_len],
        &q.quote_signature,
    )
    .map_err(|_| TeeError::ReportSignatureInvalid)?;

    if !policy
        .accepted_tcb_statuses
        .iter()
        .any(|s| s == &att.tcb_status)
    {
        return Err(TeeError::TdxTcbStatusRejected(att.tcb_status.clone()));
    }

    if let Some(svc_td) = q.mr_servicetd {
        if svc_td != NO_SERVICE_TD
            && !policy
                .accepted_service_tds
                .iter()
                .any(|allowed| ct_eq(allowed, &svc_td))
        {
            return Err(TeeError::TdxServiceTdNotPinned);
        }
    }

    let pin = &policy.measurement_pin;
    if !ct_eq(&q.mr_td, &pin.mr_td) {
        return Err(TeeError::TdxMrtdMismatch);
    }
    if !ct_eq(&q.rt_mr0, &pin.rt_mr0) {
        return Err(TeeError::TdxRtmrMismatch(0));
    }
    if !ct_eq(&q.rt_mr1, &pin.rt_mr1) {
        return Err(TeeError::TdxRtmrMismatch(1));
    }
    if !ct_eq(&q.rt_mr2, &pin.rt_mr2) {
        return Err(TeeError::TdxRtmrMismatch(2));
    }
    if let Some(expected_rtmr3) = &pin.pin_rtmr3 {
        if !ct_eq(&q.rt_mr3, expected_rtmr3) {
            return Err(TeeError::TdxRtmrMismatch(3));
        }
    }

    let measurement = fold_tdx_measurement(&q.mr_td, &q.rt_mr0, &q.rt_mr1, &q.rt_mr2);
    let svc_bytes = q.mr_servicetd.unwrap_or(NO_SERVICE_TD);
    let leaf_spki_sha256 = sha256(&pck_leaf.spki().to_spki_der());
    let mut extra = Vec::with_capacity(240 + att.tcb_status.len());
    extra.extend_from_slice(&policy.pinned_intel_root_sha256);
    extra.extend_from_slice(&leaf_spki_sha256);
    extra.extend_from_slice(&att_sec1);
    extra.extend_from_slice(&q.rt_mr3);
    extra.extend_from_slice(&svc_bytes);
    extra.extend_from_slice(&(att.tcb_status.len() as u64).to_be_bytes());
    extra.extend_from_slice(att.tcb_status.as_bytes());
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.EVIDENCE.INTEL_TDX/v1",
        &measurement,
        &q.report_data,
        &extra,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::IntelTdx,
        measurement,
        report_data: q.report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: None,
        policy_root_sha256: policy.pinned_intel_root_sha256,
        leaf_spki_sha256,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// 4. NVIDIA Hopper / Blackwell SPDM + RFC 6960 OCSP + ISO 19770-2 SWID XML-DSig RIM
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NvidiaOcspStatus {
    Good,
    Revoked,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum OcspResponderId {
    ByName(Vec<u8>),
    ByKeySha1([u8; 20]),
    ByKeySha256([u8; 32]),
}

/// Pure-Rust FIPS 180-4 SHA-1 used **solely** for RFC 6960 §4.2.1 `ResponderID.byKey` (`KeyHash`
/// 20-byte public-key identifier matching; NEVER used for cryptographic signature verification).
fn sha1_rfc6960_key_hash(data: &[u8]) -> [u8; 20] {
    let mut h: [u32; 5] = [
        0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0,
    ];
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity((data.len() + 9 + 63) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    for block in padded.chunks_exact(64) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[4 * i],
                block[4 * i + 1],
                block[4 * i + 2],
                block[4 * i + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let [mut a, mut b, mut c, mut d, mut e] = h;
        for (i, &wi) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | ((!b) & d), 0x5A827999u32),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1u32),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDCu32),
                _ => (b ^ c ^ d, 0xCA62C1D6u32),
            };
            let temp = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = temp;
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
    }
    let mut out = [0u8; 20];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OcspSingleEntry {
    hash_alg: HashAlg,
    issuer_name_hash: Vec<u8>,
    issuer_key_hash: Vec<u8>,
    serial_number: Vec<u8>,
    status: NvidiaOcspStatus,
    this_update: u64,
    next_update: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaOcspResponse {
    tbs_der: Vec<u8>,
    signature_alg: SignatureAlgorithm,
    signature_bytes: Vec<u8>,
    responder_id: OcspResponderId,
    produced_at: u64,
    delegated_cert: Option<CertRecord>,
    entries: Vec<OcspSingleEntry>,
}

impl NvidiaOcspResponse {
    pub fn from_der(ocsp_der: &[u8]) -> Result<Self, TeeError> {
        let (otag, _, obody, oend) =
            parse_der_tlv_raw(ocsp_der).ok_or(TeeError::GpuMalformedOcspDer)?;
        if otag != 0x30 || !oend.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (st_tag, st_val, rest) =
            parse_der_tlv(obody).ok_or(TeeError::GpuMalformedOcspDer)?;
        if st_tag != 0x0A || st_val != [0x00] {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (rb_ctx_tag, rb_ctx_val, rest) =
            parse_der_tlv(rest).ok_or(TeeError::GpuMalformedOcspDer)?;
        if rb_ctx_tag != 0xA0 || !rest.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (rb_tag, rb_body, rb_end) =
            parse_der_tlv(rb_ctx_val).ok_or(TeeError::GpuMalformedOcspDer)?;
        if rb_tag != 0x30 || !rb_end.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (rt_tag, rt_oid, rb_rest) =
            parse_der_tlv(rb_body).ok_or(TeeError::GpuMalformedOcspDer)?;
        let (ro_tag, basic_der, rb_end2) =
            parse_der_tlv(rb_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
        if rt_tag != 0x06 || rt_oid != OID_OCSP_BASIC || ro_tag != 0x04 || !rb_end2.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }

        let (btag, _, bbody, bend) =
            parse_der_tlv_raw(basic_der).ok_or(TeeError::GpuMalformedOcspDer)?;
        if btag != 0x30 || !bend.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (tbs_tag, tbs_raw, tbs_body, rest) =
            parse_der_tlv_raw(bbody).ok_or(TeeError::GpuMalformedOcspDer)?;
        if tbs_tag != 0x30 {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (alg_tag, alg_raw, _, rest) =
            parse_der_tlv_raw(rest).ok_or(TeeError::GpuMalformedOcspDer)?;
        if alg_tag != 0x30 {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let signature_alg = SignatureAlgorithm::from_algorithm_identifier_der(alg_raw)
            .map_err(|_| TeeError::GpuMalformedOcspDer)?;
        let (sig_tag, sig_val, mut rest) =
            parse_der_tlv(rest).ok_or(TeeError::GpuMalformedOcspDer)?;
        if sig_tag != 0x03 || sig_val.first() != Some(&0x00) {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let signature_bytes = sig_val[1..].to_vec();

        let mut delegated_cert = None;
        if !rest.is_empty() {
            let (ctag, cbody, cend) = parse_der_tlv(rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            if ctag != 0xA0 || !cend.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (stag, sbody, send) = parse_der_tlv(cbody).ok_or(TeeError::GpuMalformedOcspDer)?;
            if stag != 0x30 || !send.is_empty() || sbody.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (_, cert_raw, _, cert_rest) =
                parse_der_tlv_raw(sbody).ok_or(TeeError::GpuMalformedOcspDer)?;
            if !cert_rest.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            delegated_cert = Some(CertRecord::from_der(cert_raw)?);
            rest = cend;
        }
        let _ = rest;

        let mut cur = tbs_body;
        if cur.first() == Some(&0xA0) {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let (rid_tag, rid_val, next) = parse_der_tlv(cur).ok_or(TeeError::GpuMalformedOcspDer)?;
        let responder_id = match rid_tag {
            0xA1 => {
                let (ntag, nraw, nbody, nrest) =
                    parse_der_tlv_raw(rid_val).ok_or(TeeError::GpuMalformedOcspDer)?;
                if ntag != 0x30 || !nrest.is_empty() || parse_x509_name_der(nbody).is_none() {
                    return Err(TeeError::GpuMalformedOcspDer);
                }
                OcspResponderId::ByName(nraw.to_vec())
            }
            0xA2 => {
                let (ktag, kval, krest) =
                    parse_der_tlv(rid_val).ok_or(TeeError::GpuMalformedOcspDer)?;
                if ktag != 0x04 || !krest.is_empty() {
                    return Err(TeeError::GpuMalformedOcspDer);
                }
                match kval.len() {
                    20 => {
                        let mut kh = [0u8; 20];
                        kh.copy_from_slice(kval);
                        OcspResponderId::ByKeySha1(kh)
                    }
                    32 => {
                        let mut kh = [0u8; 32];
                        kh.copy_from_slice(kval);
                        OcspResponderId::ByKeySha256(kh)
                    }
                    _ => return Err(TeeError::GpuMalformedOcspDer),
                }
            }
            _ => return Err(TeeError::GpuMalformedOcspDer),
        };
        cur = next;

        let (produced_at, next) =
            parse_ocsp_generalized_time_tlv(cur).ok_or(TeeError::GpuMalformedOcspDer)?;
        cur = next;

        let (rs_tag, rs_body, next) = parse_der_tlv(cur).ok_or(TeeError::GpuMalformedOcspDer)?;
        if rs_tag != 0x30 || rs_body.is_empty() {
            return Err(TeeError::GpuMalformedOcspDer);
        }
        let mut entries = Vec::new();
        let mut rcur = rs_body;
        while !rcur.is_empty() {
            let (sr_tag, sr_body, rnext) =
                parse_der_tlv(rcur).ok_or(TeeError::GpuMalformedOcspDer)?;
            if sr_tag != 0x30 {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (cid_tag, cid_body, sr_rest) =
                parse_der_tlv(sr_body).ok_or(TeeError::GpuMalformedOcspDer)?;
            if cid_tag != 0x30 {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (ha_tag, ha_body, cid_rest) =
                parse_der_tlv(cid_body).ok_or(TeeError::GpuMalformedOcspDer)?;
            if ha_tag != 0x30 {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (oid_tag, oid_val, ha_param) =
                parse_der_tlv(ha_body).ok_or(TeeError::GpuMalformedOcspDer)?;
            if oid_tag != 0x06 || !(ha_param.is_empty() || ha_param == [0x05, 0x00]) {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let hash_alg = if oid_val == OID_SHA256 {
                HashAlg::Sha256
            } else if oid_val == OID_SHA384 {
                HashAlg::Sha384
            } else {
                return Err(TeeError::GpuMalformedOcspDer);
            };
            let (inh_tag, inh_val, cid_rest) =
                parse_der_tlv(cid_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            let (ikh_tag, ikh_val, cid_rest) =
                parse_der_tlv(cid_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            let (ser_tag, ser_val, cid_end) =
                parse_der_tlv(cid_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            if inh_tag != 0x04
                || ikh_tag != 0x04
                || ser_tag != 0x02
                || !cid_end.is_empty()
                || inh_val.len() != hash_alg.output_len()
                || ikh_val.len() != hash_alg.output_len()
            {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let serial_vec =
                parse_x509_serial_bytes(ser_val).ok_or(TeeError::GpuMalformedOcspDer)?;

            let (cs_tag, cs_val, sr_rest) =
                parse_der_tlv(sr_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            let status = match cs_tag {
                0x80 if cs_val.is_empty() => NvidiaOcspStatus::Good,
                0xA1 => {
                    let (_, rev_rest) = parse_ocsp_generalized_time_tlv(cs_val)
                        .ok_or(TeeError::GpuMalformedOcspDer)?;
                    if !rev_rest.is_empty() {
                        let (rt, rv, re) =
                            parse_der_tlv(rev_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
                        if rt != 0xA0 || !re.is_empty() {
                            return Err(TeeError::GpuMalformedOcspDer);
                        }
                        let (et, ev, ee) =
                            parse_der_tlv(rv).ok_or(TeeError::GpuMalformedOcspDer)?;
                        if et != 0x0A || ev.len() != 1 || !ee.is_empty() {
                            return Err(TeeError::GpuMalformedOcspDer);
                        }
                    }
                    NvidiaOcspStatus::Revoked
                }
                0x82 if cs_val.is_empty() => NvidiaOcspStatus::Unknown,
                _ => return Err(TeeError::GpuMalformedOcspDer),
            };
            let (this_update, sr_rest) =
                parse_ocsp_generalized_time_tlv(sr_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            let (nu_ctx_tag, nu_ctx_val, sr_rest) =
                parse_der_tlv(sr_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
            if nu_ctx_tag != 0xA0 {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (next_update, nu_end) =
                parse_ocsp_generalized_time_tlv(nu_ctx_val).ok_or(TeeError::GpuMalformedOcspDer)?;
            if !nu_end.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            if !sr_rest.is_empty() {
                let (se_tag, se_val, se_end) =
                    parse_der_tlv(sr_rest).ok_or(TeeError::GpuMalformedOcspDer)?;
                if se_tag != 0xA1 || !se_end.is_empty() {
                    return Err(TeeError::GpuMalformedOcspDer);
                }
                let (st, sb, se2) = parse_der_tlv(se_val).ok_or(TeeError::GpuMalformedOcspDer)?;
                if st != 0x30 || !se2.is_empty() {
                    return Err(TeeError::GpuMalformedOcspDer);
                }
                check_no_critical_extensions(sb).map_err(|_| TeeError::GpuMalformedOcspDer)?;
            }

            entries.push(OcspSingleEntry {
                hash_alg,
                issuer_name_hash: inh_val.to_vec(),
                issuer_key_hash: ikh_val.to_vec(),
                serial_number: serial_vec,
                status,
                this_update,
                next_update,
            });
            rcur = rnext;
        }

        if !next.is_empty() {
            let (re_tag, re_val, re_end) =
                parse_der_tlv(next).ok_or(TeeError::GpuMalformedOcspDer)?;
            if re_tag != 0xA1 || !re_end.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            let (st, sb, se) = parse_der_tlv(re_val).ok_or(TeeError::GpuMalformedOcspDer)?;
            if st != 0x30 || !se.is_empty() {
                return Err(TeeError::GpuMalformedOcspDer);
            }
            check_no_critical_extensions(sb).map_err(|_| TeeError::GpuMalformedOcspDer)?;
        }

        Ok(Self {
            tbs_der: tbs_raw.to_vec(),
            signature_alg,
            signature_bytes,
            responder_id,
            produced_at,
            delegated_cert,
            entries,
        })
    }

    pub fn tbs_der(&self) -> &[u8] {
        &self.tbs_der
    }
    pub fn signature_alg(&self) -> SignatureAlgorithm {
        self.signature_alg
    }
    pub fn signature_bytes(&self) -> &[u8] {
        &self.signature_bytes
    }
}

// --- Pure-Rust ISO 19770-2 SWID + Canonical XML 1.1 + W3C XML-DSig ECDSA-SHA384 Verifier ---

const NS_SWID: &str = "http://standards.iso.org/iso/19770/-2/2015/schema.xsd";
const NS_DSIG: &str = "http://www.w3.org/2000/09/xmldsig#";
const NS_HASH384: &str = "http://www.w3.org/2001/04/xmlenc#sha384";
const ALG_C14N11: &str = "http://www.w3.org/2006/12/xml-c14n11";
const ALG_ECDSA_SHA384: &str = "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha384";
const ALG_ENVELOPED: &str = "http://www.w3.org/2000/09/xmldsig#enveloped-signature";
const ALG_SHA384: &str = "http://www.w3.org/2001/04/xmldsig-more#sha384";

/// Signed NVIDIA Reference Integrity Manifest (ISO 19770-2 SWID XML with enveloped W3C XML-DSig).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NvidiaRimManifest {
    pub swid_xml: Vec<u8>,
}

#[derive(Debug, Clone)]
enum XmlNode {
    Elem(XmlElem),
    Text(String),
}

#[derive(Debug, Clone)]
struct XmlAttr {
    qname: String,
    value: String,
}

#[derive(Debug, Clone)]
struct XmlElem {
    qname: String,
    decls: Vec<(String, String)>,
    attrs: Vec<XmlAttr>,
    kids: Vec<XmlNode>,
}

struct XmlParser<'a> {
    s: &'a str,
    at: usize,
}

fn is_xml_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == ':'
}
fn is_xml_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '.' | '-')
}

impl<'a> XmlParser<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.at..]
    }
    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }
    fn eat(&mut self, lit: &str) -> bool {
        if self.rest().starts_with(lit) {
            self.at += lit.len();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, lit: &str) -> Option<()> {
        if self.eat(lit) { Some(()) } else { None }
    }
    fn ws(&mut self) -> bool {
        let start = self.at;
        while matches!(self.peek(), Some(' ' | '\t' | '\n')) {
            self.at += 1;
        }
        self.at > start
    }
    fn name(&mut self) -> Option<String> {
        let start = self.at;
        match self.peek() {
            Some(c) if is_xml_name_start(c) => self.at += 1,
            _ => return None,
        }
        while matches!(self.peek(), Some(c) if is_xml_name_char(c)) {
            self.at += 1;
        }
        let n = &self.s[start..self.at];
        if n.matches(':').count() > 1 || n.starts_with(':') || n.ends_with(':') {
            return None;
        }
        Some(n.to_string())
    }
    fn reference(&mut self) -> Option<char> {
        let end = self.rest().find(';')?;
        let body = &self.rest()[..end];
        let c = match body {
            "amp" => '&',
            "lt" => '<',
            "gt" => '>',
            "quot" => '"',
            "apos" => '\'',
            _ => {
                let code = if let Some(h) = body.strip_prefix("#x") {
                    u32::from_str_radix(h, 16).ok()?
                } else if let Some(d) = body.strip_prefix('#') {
                    d.parse::<u32>().ok()?
                } else {
                    return None;
                };
                let c = char::from_u32(code)?;
                if (c as u32) < 0x20 && !matches!(c, '\t' | '\n' | '\r') {
                    return None;
                }
                c
            }
        };
        self.at += end + 1;
        Some(c)
    }
    fn attr_value(&mut self) -> Option<String> {
        let q = match self.peek()? {
            q @ ('"' | '\'') => q,
            _ => return None,
        };
        self.at += 1;
        let mut v = String::new();
        loop {
            let c = self.peek()?;
            self.at += c.len_utf8();
            match c {
                _ if c == q => return Some(v),
                '<' => return None,
                '&' => v.push(self.reference()?),
                '\t' | '\n' => v.push(' '),
                _ => v.push(c),
            }
        }
    }
    fn element(&mut self, depth: usize) -> Option<XmlElem> {
        if depth > 32 {
            return None;
        }
        self.expect("<")?;
        let qname = self.name()?;
        let mut decls = Vec::new();
        let mut seen_decls = BTreeSet::new();
        let mut attrs: Vec<XmlAttr> = Vec::new();
        let mut seen_attrs = BTreeSet::new();
        loop {
            let had_ws = self.ws();
            if self.eat("/>") {
                return Some(XmlElem {
                    qname,
                    decls,
                    attrs,
                    kids: Vec::new(),
                });
            }
            if self.eat(">") {
                break;
            }
            if !had_ws {
                return None;
            }
            let an = self.name()?;
            self.ws();
            self.expect("=")?;
            self.ws();
            let av = self.attr_value()?;
            if an == "xmlns" {
                if !seen_decls.insert(String::new()) {
                    return None;
                }
                decls.push((String::new(), av));
            } else if let Some(p) = an.strip_prefix("xmlns:") {
                if av.is_empty() || p == "xml" || p == "xmlns" || !seen_decls.insert(p.to_string()) {
                    return None;
                }
                decls.push((p.to_string(), av));
            } else {
                if an.starts_with("xml:") || !seen_attrs.insert(an.clone()) {
                    return None;
                }
                attrs.push(XmlAttr { qname: an, value: av });
            }
        }
        let mut kids = Vec::new();
        let mut text = String::new();
        loop {
            if self.rest().starts_with("</") {
                if !text.is_empty() {
                    kids.push(XmlNode::Text(std::mem::take(&mut text)));
                }
                self.at += 2;
                let close = self.name()?;
                if close != qname {
                    return None;
                }
                self.ws();
                self.expect(">")?;
                return Some(XmlElem {
                    qname,
                    decls,
                    attrs,
                    kids,
                });
            }
            if self.rest().starts_with("<!") || self.rest().starts_with("<?") {
                return None;
            }
            if self.rest().starts_with('<') {
                if !text.is_empty() {
                    kids.push(XmlNode::Text(std::mem::take(&mut text)));
                }
                kids.push(XmlNode::Elem(self.element(depth + 1)?));
                continue;
            }
            let c = self.peek()?;
            self.at += c.len_utf8();
            match c {
                '&' => text.push(self.reference()?),
                '>' if text.ends_with("]]") => return None,
                _ => text.push(c),
            }
        }
    }
}

fn parse_swid_xml_doc(xml: &[u8]) -> Option<XmlElem> {
    if xml.len() > 4 * 1024 * 1024 {
        return None;
    }
    let raw_s = std::str::from_utf8(xml).ok()?;
    if raw_s.starts_with('\u{feff}') {
        return None;
    }
    // W3C XML 1.0 §2.11 line-ending normalization (`\r\n` and `\r` -> `\n`) prior to parsing.
    let norm_buf;
    let s: &str = if raw_s.contains('\r') {
        let mut buf = String::with_capacity(raw_s.len());
        let mut chars = raw_s.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\r' {
                if chars.peek() == Some(&'\n') {
                    chars.next();
                }
                buf.push('\n');
            } else {
                buf.push(c);
            }
        }
        norm_buf = buf;
        &norm_buf
    } else {
        raw_s
    };
    let mut p = XmlParser { s, at: 0 };
    if let Some(after_xml) = p.rest().strip_prefix("<?xml") {
        // Only strip a true XMLDecl (`<?xml ...?>`), NEVER a processing instruction like `<?xml-stylesheet...?>`.
        if !matches!(after_xml.chars().next(), Some(' ' | '\t' | '\n' | '?')) {
            return None;
        }
        let end = p.rest().find("?>")?;
        let decl = &p.rest()[5..end];
        if decl.contains('<') || decl.contains('&') {
            return None;
        }
        p.at += end + 2;
    }
    p.ws();
    if !p.rest().starts_with('<') || p.rest().starts_with("<!") || p.rest().starts_with("<?") {
        return None;
    }
    let root = p.element(0)?;
    p.ws();
    if p.at != s.len() {
        return None;
    }
    Some(root)
}

type XmlScope = BTreeMap<String, String>;

fn xml_extend_scope(scope: &XmlScope, e: &XmlElem) -> XmlScope {
    let mut s = scope.clone();
    for (p, u) in &e.decls {
        s.insert(p.clone(), u.clone());
    }
    s
}

fn xml_split_qname(q: &str) -> (&str, &str) {
    q.split_once(':').unwrap_or(("", q))
}

fn xml_elem_name<'s>(e: &'s XmlElem, scope: &'s XmlScope) -> Option<(&'s str, &'s str)> {
    let (p, l) = xml_split_qname(&e.qname);
    let uri = scope
        .get(p)
        .map(String::as_str)
        .or(if p.is_empty() { Some("") } else { None })?;
    Some((uri, l))
}

fn xml_attr_name<'s>(a: &'s XmlAttr, scope: &'s XmlScope) -> Option<(&'s str, &'s str)> {
    let (p, l) = xml_split_qname(&a.qname);
    if p.is_empty() {
        return Some(("", l));
    }
    Some((scope.get(p)?.as_str(), l))
}

fn xml_esc_attr(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '"' => out.push_str("&quot;"),
            '\t' => out.push_str("&#x9;"),
            '\n' => out.push_str("&#xA;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
}

fn xml_esc_text(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
}

fn xml_c14n(e: &XmlElem, inherited: &XmlScope, skip_sig: bool) -> Option<String> {
    let mut out = String::new();
    xml_c14n_into(e, inherited, &XmlScope::new(), true, skip_sig, &mut out)?;
    Some(out)
}

fn xml_c14n_into(
    e: &XmlElem,
    parent_scope: &XmlScope,
    rendered: &XmlScope,
    apex: bool,
    skip_root_sig: bool,
    out: &mut String,
) -> Option<()> {
    let scope = xml_extend_scope(parent_scope, e);
    let candidates: Vec<(String, String)> = if apex {
        scope.iter().map(|(p, u)| (p.clone(), u.clone())).collect()
    } else {
        e.decls.clone()
    };
    let mut ns: Vec<(String, String)> = candidates
        .into_iter()
        .filter(|(p, u)| rendered.get(p).map(String::as_str).unwrap_or("") != u.as_str())
        .collect();
    ns.sort();
    let mut now_rendered = rendered.clone();
    out.push('<');
    out.push_str(&e.qname);
    for (p, u) in &ns {
        out.push_str(if p.is_empty() { " xmlns" } else { " xmlns:" });
        out.push_str(p);
        out.push_str("=\"");
        xml_esc_attr(u, out);
        out.push('"');
        now_rendered.insert(p.clone(), u.clone());
    }
    xml_elem_name(e, &scope)?;
    let mut attrs = Vec::with_capacity(e.attrs.len());
    for a in &e.attrs {
        let (u, l) = xml_attr_name(a, &scope)?;
        attrs.push(((u.to_string(), l.to_string()), a));
    }
    attrs.sort_by(|x, y| x.0.cmp(&y.0));
    if attrs.windows(2).any(|w| w[0].0 == w[1].0) {
        return None;
    }
    for (_, a) in attrs {
        out.push(' ');
        out.push_str(&a.qname);
        out.push_str("=\"");
        xml_esc_attr(&a.value, out);
        out.push('"');
    }
    out.push('>');
    for k in &e.kids {
        match k {
            XmlNode::Text(t) => xml_esc_text(t, out),
            XmlNode::Elem(c) => {
                if apex && skip_root_sig {
                    let cs = xml_extend_scope(&scope, c);
                    if xml_elem_name(c, &cs)? == (NS_DSIG, "Signature") {
                        continue;
                    }
                }
                xml_c14n_into(c, &scope, &now_rendered, false, false, out)?;
            }
        }
    }
    out.push_str("</");
    out.push_str(&e.qname);
    out.push('>');
    Some(())
}

fn xml_child_elems(e: &XmlElem) -> impl Iterator<Item = &XmlElem> {
    e.kids.iter().filter_map(|k| match k {
        XmlNode::Elem(c) => Some(c),
        XmlNode::Text(_) => None,
    })
}

fn xml_text_of(e: &XmlElem) -> Option<String> {
    let mut s = String::new();
    for k in &e.kids {
        match k {
            XmlNode::Text(t) => s.push_str(t),
            XmlNode::Elem(_) => return None,
        }
    }
    Some(s)
}

fn xml_req_attr<'e>(e: &'e XmlElem, scope: &XmlScope, ns: &str, local: &str) -> Option<&'e str> {
    for a in &e.attrs {
        if xml_attr_name(a, scope)? == (ns, local) {
            return Some(&a.value);
        }
    }
    None
}

fn xml_exact_children<'e>(
    e: &'e XmlElem,
    scope: &XmlScope,
    want: &[(&str, &str)],
) -> Option<Vec<(&'e XmlElem, XmlScope)>> {
    let kids: Vec<&XmlElem> = xml_child_elems(e).collect();
    if kids.len() != want.len() {
        return None;
    }
    let mut out = Vec::with_capacity(want.len());
    for (k, w) in kids.into_iter().zip(want) {
        let ks = xml_extend_scope(scope, k);
        if xml_elem_name(k, &ks)? != *w {
            return None;
        }
        out.push((k, ks));
    }
    Some(out)
}

fn xml_count_ns(e: &XmlElem, scope: &XmlScope, ns: &str) -> Option<usize> {
    let s = xml_extend_scope(scope, e);
    let mut n = usize::from(xml_elem_name(e, &s)?.0 == ns);
    for c in xml_child_elems(e) {
        n += xml_count_ns(c, &s, ns)?;
    }
    Some(n)
}

fn decode_xml_b64(s: &str) -> Option<Vec<u8>> {
    let clean: String = s.chars().filter(|c| !c.is_ascii_whitespace()).collect();
    base64_decode_strict(&clean)
}

/// Sealed, unforgeable verified NVIDIA CoRIM SWID manifest (private fields; only
/// [`verify_nvidia_rim_swid`] can construct one).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedSwidRim {
    product: String,
    colloquial_version: String,
    active_measurements: BTreeMap<u8, Vec<Vec<u8>>>,
    inactive_indices: BTreeSet<u8>,
    cert_chain_root_to_leaf: Vec<CertRecord>,
}

impl VerifiedSwidRim {
    pub fn product(&self) -> &str {
        &self.product
    }
    pub fn colloquial_version(&self) -> &str {
        &self.colloquial_version
    }
    pub fn active_measurements(&self) -> &BTreeMap<u8, Vec<Vec<u8>>> {
        &self.active_measurements
    }
    pub fn inactive_indices(&self) -> &BTreeSet<u8> {
        &self.inactive_indices
    }
    pub fn cert_chain_root_to_leaf(&self) -> &[CertRecord] {
        &self.cert_chain_root_to_leaf
    }
}

pub fn verify_nvidia_rim_swid(
    xml: &[u8],
    pinned_corim_root_sha256: &[u8; 32],
    now_secs: u64,
) -> Result<VerifiedSwidRim, TeeError> {
    let root = parse_swid_xml_doc(xml).ok_or(TeeError::GpuMalformedRimXml)?;
    let empty = XmlScope::new();
    let rscope = xml_extend_scope(&empty, &root);
    if xml_elem_name(&root, &rscope) != Some((NS_SWID, "SoftwareIdentity")) {
        return Err(TeeError::GpuMalformedRimXml);
    }
    let _tag_id = xml_req_attr(&root, &rscope, "", "tagId").ok_or(TeeError::GpuMalformedRimXml)?;

    let mut sig_elems = Vec::new();
    for c in xml_child_elems(&root) {
        let cs = xml_extend_scope(&rscope, c);
        if xml_elem_name(c, &cs).ok_or(TeeError::GpuMalformedRimXml)? == (NS_DSIG, "Signature") {
            sig_elems.push((c, cs));
        }
    }
    if sig_elems.len() != 1 {
        return Err(TeeError::GpuMalformedRimXml);
    }
    let (sig, sscope) = &sig_elems[0];
    let dsig_total = xml_count_ns(&root, &empty, NS_DSIG).ok_or(TeeError::GpuMalformedRimXml)?;
    let dsig_in_sig = xml_count_ns(sig, &rscope, NS_DSIG).ok_or(TeeError::GpuMalformedRimXml)?;
    if dsig_total != dsig_in_sig {
        return Err(TeeError::GpuMalformedRimXml);
    }

    let parts = xml_exact_children(
        sig,
        sscope,
        &[
            (NS_DSIG, "SignedInfo"),
            (NS_DSIG, "SignatureValue"),
            (NS_DSIG, "KeyInfo"),
        ],
    )
    .ok_or(TeeError::GpuMalformedRimXml)?;
    let (signed_info, si_scope) = (&parts[0].0, &parts[0].1);
    let si = xml_exact_children(
        signed_info,
        si_scope,
        &[
            (NS_DSIG, "CanonicalizationMethod"),
            (NS_DSIG, "SignatureMethod"),
            (NS_DSIG, "Reference"),
        ],
    )
    .ok_or(TeeError::GpuMalformedRimXml)?;
    let check_alg = |e: &XmlElem, sc: &XmlScope, want: &str| -> Result<(), TeeError> {
        if xml_child_elems(e).next().is_some()
            || e.attrs.len() != 1
            || xml_req_attr(e, sc, "", "Algorithm") != Some(want)
        {
            return Err(TeeError::GpuMalformedRimXml);
        }
        Ok(())
    };
    check_alg(si[0].0, &si[0].1, ALG_C14N11)?;
    check_alg(si[1].0, &si[1].1, ALG_ECDSA_SHA384)?;

    let (reference, ref_scope) = (si[2].0, &si[2].1);
    if reference.attrs.len() != 1 || xml_req_attr(reference, ref_scope, "", "URI") != Some("") {
        return Err(TeeError::GpuMalformedRimXml);
    }
    let rparts = xml_exact_children(
        reference,
        ref_scope,
        &[
            (NS_DSIG, "Transforms"),
            (NS_DSIG, "DigestMethod"),
            (NS_DSIG, "DigestValue"),
        ],
    )
    .ok_or(TeeError::GpuMalformedRimXml)?;
    let tf = xml_exact_children(
        rparts[0].0,
        &rparts[0].1,
        &[(NS_DSIG, "Transform"), (NS_DSIG, "Transform")],
    )
    .ok_or(TeeError::GpuMalformedRimXml)?;
    check_alg(tf[0].0, &tf[0].1, ALG_ENVELOPED)?;
    check_alg(tf[1].0, &tf[1].1, ALG_C14N11)?;
    check_alg(rparts[1].0, &rparts[1].1, ALG_SHA384)?;
    let digest_value = xml_text_of(rparts[2].0)
        .and_then(|t| decode_xml_b64(&t))
        .ok_or(TeeError::GpuMalformedRimXml)?;
    if digest_value.len() != 48 {
        return Err(TeeError::GpuMalformedRimXml);
    }

    // 1. Verify SHA-384 digest over Canonical XML 1.1 of `<SoftwareIdentity>` minus `<ds:Signature>`.
    let doc_c14n = xml_c14n(&root, &empty, true).ok_or(TeeError::GpuMalformedRimXml)?;
    let actual_digest = sha384(doc_c14n.as_bytes());
    if !ct_eq(&actual_digest, &digest_value) {
        return Err(TeeError::ReportSignatureInvalid);
    }

    // 2. Parse `<ds:KeyInfo><ds:X509Data>` chain (leaf-first in SWID XML; normalize to root-first)
    //    and verify X.509 chain + ECDSA-P384-SHA384 signature over Canonical XML 1.1 `<ds:SignedInfo>`.
    let sig_value = xml_text_of(parts[1].0)
        .and_then(|t| decode_xml_b64(&t))
        .ok_or(TeeError::GpuMalformedRimXml)?;
    let key_info = xml_exact_children(parts[2].0, &parts[2].1, &[(NS_DSIG, "X509Data")])
        .ok_or(TeeError::GpuMalformedRimXml)?;
    let (x509data, xd_scope) = (key_info[0].0, &key_info[0].1);
    let mut certs = Vec::new();
    for c in xml_child_elems(x509data) {
        let cs = xml_extend_scope(xd_scope, c);
        if xml_elem_name(c, &cs) != Some((NS_DSIG, "X509Certificate")) {
            return Err(TeeError::GpuMalformedRimXml);
        }
        let der = xml_text_of(c)
            .and_then(|t| decode_xml_b64(&t))
            .ok_or(TeeError::GpuMalformedRimXml)?;
        certs.push(CertRecord::from_der(&der)?);
    }
    if certs.len() >= 2
        && certs[0].subject_der() != certs[0].issuer_der()
        && certs.last().is_some_and(|c| c.subject_der() == c.issuer_der())
    {
        certs.reverse();
    }
    verify_rfc5280_cert_chain(&certs, pinned_corim_root_sha256, now_secs)?;
    let rim_leaf = certs
        .last()
        .ok_or(TeeError::CertChain(CertChainError::EmptyChain))?;

    let si_c14n = xml_c14n(signed_info, sscope, false).ok_or(TeeError::GpuMalformedRimXml)?;
    verify_ecdsa_raw(
        rim_leaf.spki(),
        SignatureAlgorithm::EcdsaP384Sha384,
        si_c14n.as_bytes(),
        &sig_value,
    )
    .map_err(|_| TeeError::ReportSignatureInvalid)?;

    // 3. Extract `product`, `colloquialVersion`, and `Resource` measurements from the verified tree.
    let mut product = None;
    let mut colloquial_version = None;
    let mut active_measurements = BTreeMap::new();
    let mut inactive_indices = BTreeSet::new();
    let mut seen_rim_indices = BTreeSet::new();
    let mut payloads = 0usize;

    for c in xml_child_elems(&root) {
        let cs = xml_extend_scope(&rscope, c);
        match xml_elem_name(c, &cs).ok_or(TeeError::GpuMalformedRimXml)? {
            (NS_SWID, "Meta") => {
                if colloquial_version.is_some() {
                    return Err(TeeError::GpuMalformedRimXml);
                }
                colloquial_version = Some(
                    xml_req_attr(c, &cs, "", "colloquialVersion")
                        .ok_or(TeeError::GpuMalformedRimXml)?
                        .to_string(),
                );
                product = Some(
                    xml_req_attr(c, &cs, "", "product")
                        .ok_or(TeeError::GpuMalformedRimXml)?
                        .to_string(),
                );
            }
            (NS_SWID, "Payload") => {
                payloads += 1;
                for r in xml_child_elems(c) {
                    let rs = xml_extend_scope(&cs, r);
                    if xml_elem_name(r, &rs) != Some((NS_SWID, "Resource"))
                        || xml_child_elems(r).next().is_some()
                        || xml_req_attr(r, &rs, "", "type") != Some("Measurement")
                    {
                        return Err(TeeError::GpuMalformedRimXml);
                    }
                    let rim_idx: u8 = xml_req_attr(r, &rs, "", "index")
                        .and_then(|s| s.parse().ok())
                        .ok_or(TeeError::GpuMalformedRimXml)?;
                    if rim_idx == 255 || !seen_rim_indices.insert(rim_idx) {
                        return Err(TeeError::GpuMalformedRimXml);
                    }
                    let spdm_idx = rim_idx + 1;
                    let active = match xml_req_attr(r, &rs, "", "active") {
                        Some("True") => true,
                        Some("False") => false,
                        _ => return Err(TeeError::GpuMalformedRimXml),
                    };
                    let alts: usize = xml_req_attr(r, &rs, "", "alternatives")
                        .and_then(|s| s.parse().ok())
                        .ok_or(TeeError::GpuMalformedRimXml)?;
                    if alts == 0
                        || alts > 16
                        || xml_req_attr(r, &rs, "", "size") != Some("48")
                        || xml_req_attr(r, &rs, "", "name").is_none()
                    {
                        return Err(TeeError::GpuMalformedRimXml);
                    }
                    let mut vals = Vec::with_capacity(alts);
                    for k in 0..alts {
                        let h_hex = xml_req_attr(r, &rs, NS_HASH384, &format!("Hash{k}"))
                            .ok_or(TeeError::GpuMalformedRimXml)?;
                        let v = hex_decode_strict(h_hex).ok_or(TeeError::GpuMalformedRimXml)?;
                        if v.len() != 48 {
                            return Err(TeeError::GpuMalformedRimXml);
                        }
                        vals.push(v);
                    }
                    let hash_attr_count = r
                        .attrs
                        .iter()
                        .filter(|a| matches!(xml_attr_name(a, &rs), Some((NS_HASH384, _))))
                        .count();
                    if hash_attr_count != alts {
                        return Err(TeeError::GpuMalformedRimXml);
                    }
                    if active {
                        active_measurements.insert(spdm_idx, vals);
                    } else {
                        inactive_indices.insert(spdm_idx);
                    }
                }
            }
            _ => {}
        }
    }
    if payloads != 1 {
        return Err(TeeError::GpuMalformedRimXml);
    }

    Ok(VerifiedSwidRim {
        product: product.ok_or(TeeError::GpuMalformedRimXml)?,
        colloquial_version: colloquial_version.ok_or(TeeError::GpuMalformedRimXml)?,
        active_measurements,
        inactive_indices,
        cert_chain_root_to_leaf: certs,
    })
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
    pub spdm_report_bytes: Vec<u8>,
    pub device_cert_chain: Vec<CertRecord>,
    pub driver_rim: NvidiaRimManifest,
    pub vbios_rim: NvidiaRimManifest,
    pub ocsp_responses: Vec<NvidiaOcspResponse>,
}

fn responder_matches_cert(rid: &OcspResponderId, cert: &CertRecord) -> bool {
    match rid {
        OcspResponderId::ByName(name_der) => name_der.as_slice() == cert.subject_der(),
        OcspResponderId::ByKeySha1(kh) => {
            ct_eq(kh, &sha1_rfc6960_key_hash(cert.spki_bitstring_bytes()))
        }
        OcspResponderId::ByKeySha256(kh) => ct_eq(kh, &sha256(cert.spki_bitstring_bytes())),
    }
}

fn check_ocsp_chain_good(
    chain: &[CertRecord],
    start_idx: usize,
    ocsp_responses: &[NvidiaOcspResponse],
    now_secs: u64,
) -> Result<(), TeeError> {
    for idx in start_idx..chain.len() {
        let cert = &chain[idx];
        let issuer = &chain[idx - 1];

        let mut saw_good = false;
        let mut saw_any = false;
        for resp in ocsp_responses {
            for entry in &resp.entries {
                if entry.serial_number.as_slice() != cert.serial()
                    || !ct_eq(
                        &entry.issuer_name_hash,
                        &entry.hash_alg.digest(issuer.subject_der()),
                    )
                    || !ct_eq(
                        &entry.issuer_key_hash,
                        &entry.hash_alg.digest(issuer.spki_bitstring_bytes()),
                    )
                {
                    continue;
                }
                saw_any = true;

                let signer_cert = match &resp.delegated_cert {
                    None => issuer,
                    Some(del) => {
                        if del.issuer_der() != issuer.subject_der()
                            || del.not_before() > now_secs
                            || del.not_after() < now_secs
                            || !del.has_ocsp_signing_eku()
                            || !del
                                .key_usage()
                                .is_some_and(KeyUsage::digital_signature)
                            || del.basic_constraints().is_some_and(|bc| bc.is_ca)
                        {
                            return Err(TeeError::GpuOcspSignatureInvalid);
                        }
                        verify_signature(
                            issuer.spki(),
                            del.signature_alg(),
                            del.tbs_der(),
                            del.signature_bytes(),
                        )
                        .map_err(|_| TeeError::GpuOcspSignatureInvalid)?;
                        del
                    }
                };
                if !responder_matches_cert(&resp.responder_id, signer_cert) {
                    return Err(TeeError::GpuOcspSignatureInvalid);
                }
                verify_signature(
                    signer_cert.spki(),
                    resp.signature_alg(),
                    resp.tbs_der(),
                    resp.signature_bytes(),
                )
                .map_err(|_| TeeError::GpuOcspSignatureInvalid)?;

                if resp.produced_at > now_secs.saturating_add(MAX_FUTURE_SKEW_SECS)
                    || entry.this_update > now_secs
                    || entry.next_update <= now_secs
                    || entry.this_update >= entry.next_update
                {
                    return Err(TeeError::GpuOcspNotCurrent);
                }
                if entry.status != NvidiaOcspStatus::Good {
                    return Err(TeeError::GpuOcspRevoked);
                }
                saw_good = true;
            }
        }
        if !saw_any || !saw_good {
            return Err(TeeError::GpuOcspMissing);
        }
    }
    Ok(())
}

/// Hardened NVIDIA Hopper (`H100`/`GH100`) & Blackwell (`B200`/`GB200`) SPDM + OCSP + SWID RIM gate.
pub fn verify_nvidia_gpu(
    policy: &NvidiaGpuPolicy,
    att: &NvidiaGpuAttestation,
    expected_nonce: &[u8; SPDM_NONCE_LEN],
    now_secs: u64,
) -> Result<VerifiedTeeEvidence, TeeError> {
    if now_secs == 0 {
        return Err(TeeError::InvalidClock);
    }
    let report = parse_spdm_gpu_report(&att.spdm_report_bytes)?;

    verify_rfc5280_cert_chain(
        &att.device_cert_chain,
        &policy.pinned_device_root_sha256,
        now_secs,
    )?;
    let device_leaf = att
        .device_cert_chain
        .last()
        .ok_or(TeeError::GpuMissingFwid)?;

    verify_ecdsa_raw(
        device_leaf.spki(),
        SignatureAlgorithm::EcdsaP384Sha384,
        &report.signed_prefix,
        &report.signature,
    )
    .map_err(|_| TeeError::ReportSignatureInvalid)?;

    if !ct_eq(&report.request_nonce, expected_nonce) {
        return Err(TeeError::GpuNonceMismatch);
    }

    check_ocsp_chain_good(&att.device_cert_chain, 1, &att.ocsp_responses, now_secs)?;

    let drv_rim = verify_nvidia_rim_swid(
        &att.driver_rim.swid_xml,
        &policy.pinned_corim_root_sha256,
        now_secs,
    )?;
    let vbios_rim = verify_nvidia_rim_swid(
        &att.vbios_rim.swid_xml,
        &policy.pinned_corim_root_sha256,
        now_secs,
    )?;
    for (rim, expected_ver) in [
        (&drv_rim, &policy.expected_driver_version),
        (&vbios_rim, &policy.expected_vbios_version),
    ] {
        if rim.product != policy.arch.rim_product() {
            return Err(TeeError::GpuRimArchMismatch);
        }
        if !rim.colloquial_version.eq_ignore_ascii_case(expected_ver) {
            return Err(TeeError::GpuRimVersionMismatch);
        }
        check_ocsp_chain_good(&rim.cert_chain_root_to_leaf, 1, &att.ocsp_responses, now_secs)?;
    }

    let spdm_fwid = report.fwid().ok_or(TeeError::GpuMissingFwid)?;
    let cert_fwid = device_leaf.dice_fwid().ok_or(TeeError::GpuMissingFwid)?;
    if !ct_eq(&spdm_fwid, &cert_fwid) {
        return Err(TeeError::GpuFwidCertMismatch);
    }
    if !ct_eq(&spdm_fwid, &policy.pinned_fwid) {
        return Err(TeeError::GpuFwidRimPinMismatch);
    }

    if drv_rim.active_measurements.is_empty() && vbios_rim.active_measurements.is_empty() {
        return Err(TeeError::GpuMissingGoldenMeasurement(0));
    }
    let mut covered_indices = BTreeSet::new();
    for (&idx, _) in &drv_rim.active_measurements {
        covered_indices.insert(idx);
    }
    for (&idx, _) in &vbios_rim.active_measurements {
        covered_indices.insert(idx);
    }
    for (&idx, measured) in &report.measurements {
        if covered_indices.contains(&idx) {
            if let Some(drv_vals) = drv_rim.active_measurements.get(&idx) {
                if !drv_vals.iter().any(|g| ct_eq(g, measured)) {
                    return Err(TeeError::GpuMeasurementMismatch(idx));
                }
            }
            if let Some(vb_vals) = vbios_rim.active_measurements.get(&idx) {
                if !vb_vals.iter().any(|g| ct_eq(g, measured)) {
                    return Err(TeeError::GpuMeasurementMismatch(idx));
                }
            }
        } else if drv_rim.inactive_indices.contains(&idx) || vbios_rim.inactive_indices.contains(&idx) {
            // Inactive RIM slots must report all-zero SHA-384 blocks (matching `tee-verify/src/nvidia_rim.rs:977`).
            if measured.len() != 48 || measured.iter().any(|&b| b != 0) {
                return Err(TeeError::GpuMeasurementMismatch(idx));
            }
        } else {
            return Err(TeeError::GpuUncoveredMeasurement(idx));
        }
    }
    for &idx in &covered_indices {
        if !report.measurements.contains_key(&idx) {
            return Err(TeeError::GpuMissingGoldenMeasurement(idx));
        }
    }

    let mut m_hasher = Sha256::new();
    m_hasher.update(b"OBEND.TEE.EVIDENCE.NVIDIA_GPU.MEASUREMENT/v1");
    m_hasher.update(policy.arch.rim_product().as_bytes());
    m_hasher.update(&spdm_fwid);
    for (&idx, val) in &report.measurements {
        m_hasher.update(&[idx]);
        m_hasher.update(&(val.len() as u64).to_be_bytes());
        m_hasher.update(val);
    }
    let measurement = m_hasher.finalize();

    let mut report_data = [0u8; 64];
    report_data[..32].copy_from_slice(&report.request_nonce);
    report_data[32..].copy_from_slice(&report.response_nonce);

    let leaf_spki_sha256 = sha256(&device_leaf.spki().to_spki_der());
    let mut extra = Vec::with_capacity(144);
    extra.extend_from_slice(&policy.pinned_device_root_sha256);
    extra.extend_from_slice(&policy.pinned_corim_root_sha256);
    extra.extend_from_slice(&leaf_spki_sha256);
    extra.extend_from_slice(&spdm_fwid);
    let evidence_digest = compute_evidence_digest(
        b"OBEND.TEE.EVIDENCE.NVIDIA_GPU/v1",
        &measurement,
        &report_data,
        &extra,
    );
    Ok(VerifiedTeeEvidence {
        vendor: TeeVendor::NvidiaGpu(policy.arch),
        measurement,
        report_data,
        tcb_posture: TcbPosture::VerifiedFloor,
        gpu_fwid: Some(spdm_fwid),
        policy_root_sha256: policy.pinned_device_root_sha256,
        leaf_spki_sha256,
        verified_at: now_secs,
        evidence_digest,
    })
}

// ---------------------------------------------------------------------------
// Spec-Compliant DER X.509 / CRL / OCSP & Hardware Wire Fixture Builders
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct FixtureCertSpec<'a> {
    pub subject_cn: &'a str,
    pub issuer_cn: &'a str,
    pub serial: &'a [u8],
    pub not_before: u64,
    pub not_after: u64,
    pub subject_key: SubjectPublicKey,
    pub basic_constraints: Option<BasicConstraints>,
    pub key_usage: Option<KeyUsage>,
    pub ocsp_signing_eku: bool,
    pub dice_fwid: Option<[u8; 48]>,
    pub amd_vcek_ext: Option<(AmdSnpTcbVersion, [u8; 64])>,
}

fn encode_extension_der(oid_body: &[u8], critical: bool, value_bytes: &[u8]) -> Vec<u8> {
    let mut seq = der_encode(0x06, oid_body);
    if critical {
        seq.extend_from_slice(&[0x01, 0x01, 0xFF]);
    }
    seq.extend_from_slice(&der_encode(0x04, value_bytes));
    der_encode(0x30, &seq)
}

/// Issue a real RFC 5280 v3 DER X.509 `Certificate` signed by `issuer_signer` (`FixtureSigner`),
/// using real AMD KDS OIDs (`1.3.6.1.4.1.3704.1.3.{1,2,3,8,9}`, `1.3.6.1.4.1.3704.1.4`) when `amd_vcek_ext` is set.
pub fn fixture_issue_cert_der(
    spec: &FixtureCertSpec<'_>,
    issuer_signer: &FixtureSigner,
    sig_alg: SignatureAlgorithm,
) -> Vec<u8> {
    let mut tbs = Vec::new();
    tbs.extend_from_slice(&der_encode(0xA0, &[0x02, 0x01, 0x02]));
    tbs.extend_from_slice(&der_encode_uint(spec.serial));
    let alg_der = sig_alg.algorithm_identifier_der();
    tbs.extend_from_slice(&alg_der);
    tbs.extend_from_slice(&encode_x509_name_cn(spec.issuer_cn));
    let mut val_seq = encode_x509_time_der(spec.not_before);
    val_seq.extend_from_slice(&encode_x509_time_der(spec.not_after));
    tbs.extend_from_slice(&der_encode(0x30, &val_seq));
    tbs.extend_from_slice(&encode_x509_name_cn(spec.subject_cn));
    tbs.extend_from_slice(&spec.subject_key.to_spki_der());

    let mut exts = Vec::new();
    if let Some(bc) = spec.basic_constraints {
        exts.extend_from_slice(&encode_extension_der(
            OID_BASIC_CONSTRAINTS,
            true,
            &encode_der_basic_constraints(bc),
        ));
    }
    if let Some(ku) = spec.key_usage {
        exts.extend_from_slice(&encode_extension_der(
            OID_KEY_USAGE,
            true,
            &encode_der_key_usage(ku),
        ));
    }
    if spec.ocsp_signing_eku {
        let eku_seq = der_encode(0x30, &der_encode(0x06, OID_KP_OCSP_SIGNING));
        exts.extend_from_slice(&encode_extension_der(OID_EXT_KEY_USAGE, false, &eku_seq));
    }
    if let Some(fwid) = &spec.dice_fwid {
        let fwid_ext = der_encode(0x30, &der_encode(0x04, fwid));
        exts.extend_from_slice(&encode_extension_der(OID_TCG_DICE_TCB_INFO, false, &fwid_ext));
    }
    if let Some((tcb, hw_id)) = &spec.amd_vcek_ext {
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_BL_SPL,
            false,
            &encode_der_u8_integer(tcb.bootloader),
        ));
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_TEE_SPL,
            false,
            &encode_der_u8_integer(tcb.tee),
        ));
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_SNP_SPL,
            false,
            &encode_der_u8_integer(tcb.snp),
        ));
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_UCODE_SPL,
            false,
            &encode_der_u8_integer(tcb.microcode),
        ));
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_FMC_SPL,
            false,
            &encode_der_u8_integer(tcb.fmc),
        ));
        exts.extend_from_slice(&encode_extension_der(
            OID_AMD_VCEK_HW_ID,
            false,
            &der_encode(0x04, hw_id),
        ));
    }
    if !exts.is_empty() {
        tbs.extend_from_slice(&der_encode(0xA3, &der_encode(0x30, &exts)));
    }

    let tbs_der = der_encode(0x30, &tbs);
    let sig = issuer_signer.sign(sig_alg, &tbs_der);
    let mut sig_bs = vec![0x00];
    sig_bs.extend_from_slice(&sig);

    let mut cert = tbs_der;
    cert.extend_from_slice(&alg_der);
    cert.extend_from_slice(&der_encode(0x03, &sig_bs));
    der_encode(0x30, &cert)
}

/// Issue a real RFC 5280 v2 DER `CertificateList` (CRL) signed by `issuer_signer`.
pub fn fixture_issue_crl_der(
    issuer_cn: &str,
    last_update: u64,
    next_update: u64,
    revoked_serials: &[Vec<u8>],
    issuer_signer: &FixtureSigner,
    sig_alg: SignatureAlgorithm,
) -> Vec<u8> {
    let alg_der = sig_alg.algorithm_identifier_der();
    let mut tbs = Vec::new();
    tbs.extend_from_slice(&[0x02, 0x01, 0x01]);
    tbs.extend_from_slice(&alg_der);
    tbs.extend_from_slice(&encode_x509_name_cn(issuer_cn));
    tbs.extend_from_slice(&encode_x509_time_der(last_update));
    tbs.extend_from_slice(&encode_x509_time_der(next_update));
    if !revoked_serials.is_empty() {
        let mut entries = Vec::new();
        for ser in revoked_serials {
            let mut e = der_encode_uint(ser);
            e.extend_from_slice(&encode_x509_time_der(last_update));
            entries.extend_from_slice(&der_encode(0x30, &e));
        }
        tbs.extend_from_slice(&der_encode(0x30, &entries));
    }
    let tbs_der = der_encode(0x30, &tbs);
    let sig = issuer_signer.sign(sig_alg, &tbs_der);
    let mut sig_bs = vec![0x00];
    sig_bs.extend_from_slice(&sig);

    let mut crl = tbs_der;
    crl.extend_from_slice(&alg_der);
    crl.extend_from_slice(&der_encode(0x03, &sig_bs));
    der_encode(0x30, &crl)
}

/// Issue a real RFC 6960 DER `OCSPResponse` (`BasicOCSPResponse`) signed directly by `issuer_signer`.
pub fn fixture_issue_ocsp_der(
    issuer_cert: &CertRecord,
    subject_cert: &CertRecord,
    status: NvidiaOcspStatus,
    this_update: u64,
    next_update: u64,
    issuer_signer: &FixtureSigner,
    sig_alg: SignatureAlgorithm,
) -> Vec<u8> {
    let mut sha256_alg = der_encode(0x06, OID_SHA256);
    sha256_alg.extend_from_slice(&[0x05, 0x00]);
    let mut cert_id = der_encode(0x30, &sha256_alg);
    cert_id.extend_from_slice(&der_encode(0x04, &sha256(issuer_cert.subject_der())));
    cert_id.extend_from_slice(&der_encode(0x04, &sha256(issuer_cert.spki_bitstring_bytes())));
    cert_id.extend_from_slice(&der_encode_uint(subject_cert.serial()));

    let mut single = der_encode(0x30, &cert_id);
    match status {
        NvidiaOcspStatus::Good => single.extend_from_slice(&[0x80, 0x00]),
        NvidiaOcspStatus::Revoked => {
            single.extend_from_slice(&der_encode(0xA1, &encode_generalized_time_der(this_update)));
        }
        NvidiaOcspStatus::Unknown => single.extend_from_slice(&[0x82, 0x00]),
    }
    single.extend_from_slice(&encode_generalized_time_der(this_update));
    single.extend_from_slice(&der_encode(0xA0, &encode_generalized_time_der(next_update)));
    let single_seq = der_encode(0x30, &der_encode(0x30, &single));

    let mut tbs = Vec::new();
    tbs.extend_from_slice(&der_encode(0xA1, issuer_cert.subject_der()));
    tbs.extend_from_slice(&encode_generalized_time_der(this_update));
    tbs.extend_from_slice(&single_seq);
    let tbs_der = der_encode(0x30, &tbs);

    let alg_der = sig_alg.algorithm_identifier_der();
    let sig = issuer_signer.sign(sig_alg, &tbs_der);
    let mut sig_bs = vec![0x00];
    sig_bs.extend_from_slice(&sig);

    let mut basic = tbs_der;
    basic.extend_from_slice(&alg_der);
    basic.extend_from_slice(&der_encode(0x03, &sig_bs));
    let basic_der = der_encode(0x30, &basic);

    let mut resp_bytes = der_encode(0x06, OID_OCSP_BASIC);
    resp_bytes.extend_from_slice(&der_encode(0x04, &basic_der));
    let mut outer = vec![0x0A, 0x01, 0x00];
    outer.extend_from_slice(&der_encode(0xA0, &der_encode(0x30, &resp_bytes)));
    der_encode(0x30, &outer)
}

#[derive(Debug, Clone)]
pub struct FixtureNitroDocFields<'a> {
    pub module_id: &'a str,
    pub cert_chain_root_to_leaf: &'a [CertRecord],
    pub doc_timestamp_ms: u64,
    pub pcr0: &'a [u8],
    pub pcr1: &'a [u8],
    pub pcr2: &'a [u8],
    pub user_data: &'a [u8],
}

/// Build & sign a real RFC 9052 CBOR `COSE_Sign1` AWS Nitro `AttestationDocument` (`ES384`).
pub fn fixture_build_aws_nitro_cose(
    f: &FixtureNitroDocFields<'_>,
    leaf_signer: &FixtureSigner,
) -> Vec<u8> {
    assert!(f.cert_chain_root_to_leaf.len() >= 2);
    let leaf = f.cert_chain_root_to_leaf.last().unwrap();
    let cabundle = &f.cert_chain_root_to_leaf[..f.cert_chain_root_to_leaf.len() - 1];

    let mut payload = Vec::new();
    cbor_push_head(&mut payload, 5, 9); // definite map(9)
    cbor_push_tstr(&mut payload, "module_id");
    cbor_push_tstr(&mut payload, f.module_id);
    cbor_push_tstr(&mut payload, "digest");
    cbor_push_tstr(&mut payload, "SHA384");
    cbor_push_tstr(&mut payload, "timestamp");
    cbor_push_head(&mut payload, 0, f.doc_timestamp_ms);
    cbor_push_tstr(&mut payload, "pcrs");
    cbor_push_head(&mut payload, 5, 3);
    cbor_push_head(&mut payload, 0, 0);
    cbor_push_bstr(&mut payload, f.pcr0);
    cbor_push_head(&mut payload, 0, 1);
    cbor_push_bstr(&mut payload, f.pcr1);
    cbor_push_head(&mut payload, 0, 2);
    cbor_push_bstr(&mut payload, f.pcr2);
    cbor_push_tstr(&mut payload, "certificate");
    cbor_push_bstr(&mut payload, leaf.cert_der());
    cbor_push_tstr(&mut payload, "cabundle");
    cbor_push_head(&mut payload, 4, cabundle.len() as u64);
    for ca in cabundle {
        cbor_push_bstr(&mut payload, ca.cert_der());
    }
    cbor_push_tstr(&mut payload, "public_key");
    payload.push(0xf6); // null
    cbor_push_tstr(&mut payload, "user_data");
    cbor_push_bstr(&mut payload, f.user_data);
    cbor_push_tstr(&mut payload, "nonce");
    payload.push(0xf6); // null

    let sig_structure = aws_nitro_cose_sig_structure(COSE_PROTECTED_ES384, &payload);
    let sig = leaf_signer.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP384Sha384, &sig_structure);

    let mut cose = Vec::with_capacity(16 + payload.len() + sig.len());
    cose.push(0x84); // 4-element COSE_Sign1 array
    cbor_push_bstr(&mut cose, COSE_PROTECTED_ES384);
    cose.push(0xa0); // empty unprotected map {}
    cbor_push_bstr(&mut cose, &payload);
    cbor_push_bstr(&mut cose, &sig);
    cose
}

#[derive(Debug, Clone)]
pub struct FixtureSnpReportFields {
    pub guest_svn: u32,
    pub guest_policy: u64,
    pub vmpl: u8,
    pub signing_key: u8,
    pub reported_tcb: AmdSnpTcbVersion,
    pub launch_measurement: [u8; 48],
    pub report_data: [u8; 64],
    pub chip_id: [u8; 64],
}

/// Build & sign a real `1184`-byte (`0x4A0`) AMD SEV-SNP ABI Table 21/22 `ATTESTATION_REPORT`
/// (`ECDSA-P384-SHA384` over `report[0x000..0x2A0]`, 72-byte LE `r`/`s` @ `0x2A0..0x330`).
pub fn fixture_build_amd_snp_report(
    f: &FixtureSnpReportFields,
    product: AmdSnpProduct,
    vcek_signer: &FixtureSigner,
) -> Vec<u8> {
    let mut r = vec![0u8; SNP_REPORT_LEN];
    let version: u32 = if product == AmdSnpProduct::Turin { 3 } else { 2 };
    r[0x000..0x004].copy_from_slice(&version.to_le_bytes());
    r[0x004..0x008].copy_from_slice(&f.guest_svn.to_le_bytes());
    r[0x008..0x010].copy_from_slice(&f.guest_policy.to_le_bytes());
    r[0x030..0x034].copy_from_slice(&u32::from(f.vmpl).to_le_bytes());
    r[0x034..0x038].copy_from_slice(&1u32.to_le_bytes()); // ECDSA-P384-SHA384
    let tcb_bytes = f.reported_tcb.to_amd_report_bytes(product);
    r[0x038..0x040].copy_from_slice(&tcb_bytes);
    r[0x048..0x04C].copy_from_slice(&(u32::from(f.signing_key) << 2).to_le_bytes());
    r[0x050..0x090].copy_from_slice(&f.report_data);
    r[0x090..0x0C0].copy_from_slice(&f.launch_measurement);
    r[0x180..0x188].copy_from_slice(&tcb_bytes);
    r[0x1A0..0x1E0].copy_from_slice(&f.chip_id);

    let sig_be = vcek_signer.sign_ecdsa_raw(
        SignatureAlgorithm::EcdsaP384Sha384,
        &r[..SNP_SIGNED_BODY_LEN],
    );
    for i in 0..48 {
        r[0x2A0 + i] = sig_be[47 - i];
        r[0x2E8 + i] = sig_be[95 - i];
    }
    r
}

#[derive(Debug, Clone)]
pub struct FixtureTdxQuoteFields {
    pub mr_td: [u8; 48],
    pub rt_mr0: [u8; 48],
    pub rt_mr1: [u8; 48],
    pub rt_mr2: [u8; 48],
    pub rt_mr3: [u8; 48],
    pub mr_servicetd: Option<[u8; 48]>,
    pub td_attributes: u64,
    pub report_data: [u8; 64],
    pub qe_auth_data: Vec<u8>,
}

/// Build & sign a real Intel DCAP v4 (TD 1.0, `48`B header + `584`B body) or v5 (TD 1.5, `648`B body
/// when `mr_servicetd.is_some()`) binary TDX Quote with `384`B SGX `EnclaveReportBody` & PEM PCK chain.
pub fn fixture_build_intel_tdx_quote(
    f: &FixtureTdxQuoteFields,
    pck_chain_root_to_leaf: &[CertRecord],
    pck_leaf_signer: &FixtureSigner,
    att_key_signer: &FixtureSigner,
) -> Vec<u8> {
    let SubjectPublicKey::P256(att_sec1) = att_key_signer.public_key() else {
        panic!("fixture_build_intel_tdx_quote: attestation key must be P-256");
    };
    let att_pk_64 = &att_sec1[1..65];

    let mut quote = Vec::with_capacity(4096);
    let version: u16 = if f.mr_servicetd.is_some() { 5 } else { 4 };
    quote.extend_from_slice(&version.to_le_bytes());
    quote.extend_from_slice(&2u16.to_le_bytes()); // ECDSA-256-with-P-256
    quote.extend_from_slice(&TEE_TYPE_TDX.to_le_bytes());
    quote.extend_from_slice(&[0u8; 4]); // qe_svn, pce_svn
    quote.extend_from_slice(&INTEL_QE_VENDOR_ID);
    quote.extend_from_slice(&[0u8; 20]); // user_data
    assert_eq!(quote.len(), TDX_QUOTE_HEADER_LEN);

    let mut body = vec![0u8; if f.mr_servicetd.is_some() { TDX_TD15_BODY_LEN } else { TDX_TD10_BODY_LEN }];
    body[120..128].copy_from_slice(&f.td_attributes.to_le_bytes());
    body[136..184].copy_from_slice(&f.mr_td);
    body[328..376].copy_from_slice(&f.rt_mr0);
    body[376..424].copy_from_slice(&f.rt_mr1);
    body[424..472].copy_from_slice(&f.rt_mr2);
    body[472..520].copy_from_slice(&f.rt_mr3);
    body[520..584].copy_from_slice(&f.report_data);
    if let Some(svc) = &f.mr_servicetd {
        body[600..648].copy_from_slice(svc);
        quote.extend_from_slice(&3u16.to_le_bytes()); // body_type = 3 (TD15)
        quote.extend_from_slice(&(TDX_TD15_BODY_LEN as u32).to_le_bytes());
    }
    quote.extend_from_slice(&body);

    let quote_sig = att_key_signer.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP256Sha256, &quote);

    // 384-byte SGX EnclaveReportBody with `report_data[0..32] = SHA-256(att_pk_64 || qe_auth_data)`
    let mut qe_report = [0u8; SGX_QE_REPORT_BODY_LEN];
    let mut ak_hash = Sha256::new();
    ak_hash.update(att_pk_64);
    ak_hash.update(&f.qe_auth_data);
    qe_report[320..352].copy_from_slice(&ak_hash.finalize());
    let qe_sig = pck_leaf_signer.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP256Sha256, &qe_report);

    // DCAP cert_type=5 PEM chain (leaf -> intermediate -> root)
    let mut pem_chain = String::new();
    for cert in pck_chain_root_to_leaf.iter().rev() {
        pem_chain.push_str(&encode_pem_cert(cert));
    }
    let pem_bytes = pem_chain.into_bytes();

    let mut qe_cert_data = Vec::with_capacity(SGX_QE_REPORT_BODY_LEN + 64 + 8 + f.qe_auth_data.len() + pem_bytes.len());
    qe_cert_data.extend_from_slice(&qe_report);
    qe_cert_data.extend_from_slice(&qe_sig);
    qe_cert_data.extend_from_slice(&(f.qe_auth_data.len() as u16).to_le_bytes());
    qe_cert_data.extend_from_slice(&f.qe_auth_data);
    qe_cert_data.extend_from_slice(&5u16.to_le_bytes()); // cert_type = 5 (PCK PEM chain)
    qe_cert_data.extend_from_slice(&(pem_bytes.len() as u32).to_le_bytes());
    qe_cert_data.extend_from_slice(&pem_bytes);

    let mut auth = Vec::with_capacity(134 + qe_cert_data.len());
    auth.extend_from_slice(&quote_sig);
    auth.extend_from_slice(att_pk_64);
    auth.extend_from_slice(&6u16.to_le_bytes()); // cert_type = 6 (QE_REPORT_CERT_DATA)
    auth.extend_from_slice(&(qe_cert_data.len() as u32).to_le_bytes());
    auth.extend_from_slice(&qe_cert_data);

    quote.extend_from_slice(&(auth.len() as u32).to_le_bytes());
    quote.extend_from_slice(&auth);
    quote
}

/// Fixture helper: sign an SPDM 1.1 `GET_MEASUREMENTS` wire report in-place (trailing 96 bytes).
pub fn fixture_sign_spdm_report(report_bytes: &mut [u8], gpu_leaf_signer: &FixtureSigner) {
    assert!(report_bytes.len() > SPDM_REQUEST_LEN + SPDM_SIGNATURE_LEN);
    let prefix_len = report_bytes.len() - SPDM_SIGNATURE_LEN;
    let raw = gpu_leaf_signer.sign_ecdsa_raw(
        SignatureAlgorithm::EcdsaP384Sha384,
        &report_bytes[..prefix_len],
    );
    report_bytes[prefix_len..].copy_from_slice(&raw);
}

/// Build & sign a real ISO 19770-2 SWID `<SoftwareIdentity>` XML manifest with enveloped W3C
/// XML-DSig (`Canonical XML 1.1` + `ecdsa-sha384` + `sha384` + `<ds:X509Data>` leaf-first chain).
pub fn fixture_build_nvidia_rim_swid_xml(
    arch: GpuArch,
    version: &str,
    cert_chain_root_to_leaf: &[CertRecord],
    golden_measurements: &BTreeMap<u8, Vec<Vec<u8>>>,
    rim_leaf_signer: &FixtureSigner,
) -> NvidiaRimManifest {
    let prod = arch.rim_product();
    let mut payload_xml = String::new();
    for (&spdm_idx, vals) in golden_measurements {
        assert!(spdm_idx >= 1, "SPDM measurement index must be >= 1");
        let rim_idx = spdm_idx - 1;
        let mut hash_attrs = String::new();
        for (k, v) in vals.iter().enumerate() {
            assert_eq!(v.len(), 48, "SWID RIM golden measurement must be 48-byte SHA-384");
            hash_attrs.push_str(&format!(" ns1:Hash{k}=\"{}\"", hex_encode_lower(v)));
        }
        payload_xml.push_str(&format!(
            "<ns0:Resource active=\"True\" alternatives=\"{}\"{hash_attrs} index=\"{rim_idx}\" name=\"M{spdm_idx}\" size=\"48\" type=\"Measurement\"></ns0:Resource>",
            vals.len(),
        ));
    }

    let unsigned_doc = format!(
        "<ns0:SoftwareIdentity xmlns:ns0=\"{NS_SWID}\" xmlns:ns1=\"{NS_HASH384}\" name=\"{prod}\" tagId=\"{prod}-{version}\"><ns0:Meta colloquialVersion=\"{version}\" product=\"{prod}\"></ns0:Meta><ns0:Payload>{payload_xml}</ns0:Payload></ns0:SoftwareIdentity>"
    );
    let root_unsigned = parse_swid_xml_doc(unsigned_doc.as_bytes()).expect("valid unsigned SWID");
    let doc_c14n = xml_c14n(&root_unsigned, &XmlScope::new(), false).expect("c14n unsigned SWID");
    let digest_b64 = base64_encode_std(&sha384(doc_c14n.as_bytes()));

    let signed_info_c14n = format!(
        "<ds:SignedInfo xmlns:ds=\"{NS_DSIG}\" xmlns:ns0=\"{NS_SWID}\" xmlns:ns1=\"{NS_HASH384}\"><ds:CanonicalizationMethod Algorithm=\"{ALG_C14N11}\"></ds:CanonicalizationMethod><ds:SignatureMethod Algorithm=\"{ALG_ECDSA_SHA384}\"></ds:SignatureMethod><ds:Reference URI=\"\"><ds:Transforms><ds:Transform Algorithm=\"{ALG_ENVELOPED}\"></ds:Transform><ds:Transform Algorithm=\"{ALG_C14N11}\"></ds:Transform></ds:Transforms><ds:DigestMethod Algorithm=\"{ALG_SHA384}\"></ds:DigestMethod><ds:DigestValue>{digest_b64}</ds:DigestValue></ds:Reference></ds:SignedInfo>"
    );
    let raw_sig = rim_leaf_signer.sign_ecdsa_raw(
        SignatureAlgorithm::EcdsaP384Sha384,
        signed_info_c14n.as_bytes(),
    );
    let sig_b64 = base64_encode_std(&raw_sig);

    let mut x509_certs = String::new();
    for cert in cert_chain_root_to_leaf.iter().rev() {
        x509_certs.push_str(&format!(
            "<ds:X509Certificate>{}</ds:X509Certificate>",
            base64_encode_std(cert.cert_der())
        ));
    }

    let signed_doc = format!(
        "<ns0:SoftwareIdentity xmlns:ns0=\"{NS_SWID}\" xmlns:ns1=\"{NS_HASH384}\" name=\"{prod}\" tagId=\"{prod}-{version}\"><ns0:Meta colloquialVersion=\"{version}\" product=\"{prod}\"></ns0:Meta><ns0:Payload>{payload_xml}</ns0:Payload><ds:Signature xmlns:ds=\"{NS_DSIG}\"><ds:SignedInfo><ds:CanonicalizationMethod Algorithm=\"{ALG_C14N11}\"></ds:CanonicalizationMethod><ds:SignatureMethod Algorithm=\"{ALG_ECDSA_SHA384}\"></ds:SignatureMethod><ds:Reference URI=\"\"><ds:Transforms><ds:Transform Algorithm=\"{ALG_ENVELOPED}\"></ds:Transform><ds:Transform Algorithm=\"{ALG_C14N11}\"></ds:Transform></ds:Transforms><ds:DigestMethod Algorithm=\"{ALG_SHA384}\"></ds:DigestMethod><ds:DigestValue>{digest_b64}</ds:DigestValue></ds:Reference></ds:SignedInfo><ds:SignatureValue>{sig_b64}</ds:SignatureValue><ds:KeyInfo><ds:X509Data>{x509_certs}</ds:X509Data></ds:KeyInfo></ds:Signature></ns0:SoftwareIdentity>"
    );

    NvidiaRimManifest {
        swid_xml: signed_doc.into_bytes(),
    }
}
