//! Registry-Pinned TLSNotary / `calltree` Session Verifier (`V3` & `V4` closed) and
//! E2EE Prompt/Response Channel Binding (`dregg-chutes-e2ee` hardened).
//!
//! Quarried and hardened from `breadstuffs/{dregg-oracle,zkoracle-live,calltree/verify,dregg-chutes-e2ee}`:
//!
//! - **`V3` closed:** Never trusts a self-asserted `notary_key_hex` inside an untrusted
//!   `ProofEnvelope`. Every TLSNotary presentation MUST verify against a caller-supplied
//!   [`PinnedNotaryRegistry`], pins both HTTP `Host` and request path, and emits only
//!   [`VerificationLeg`] entries for checks that actually executed.
//! - **Notary signature is verified, not asserted:** the envelope carries the notary's public
//!   key and a P-256 ECDSA or Ed25519 signature over [`tlsn_attestation_preimage`]; the registry
//!   pins `SHA-256(SubjectPublicKeyInfo DER)` of that key ([`notary_key_fingerprint`]). The
//!   preimage is an OBEND canonical, length-framed encoding — not the TLSNotary wire format.
//! - **`V4` closed:** Enforces complete body disclosure (refuses any `unauthed_recv_ranges`
//!   or redaction placeholders inside the attested HTTP response body).
//! - **RFC 8259 strict JSON field extraction:** Pure-Rust bounded parser (`MAX_JSON_BODY_BYTES`,
//!   `MAX_JSON_PATH_DEPTH`) that rejects duplicate object keys and control-plane injection bytes.
//! - **E2EE channel binding:** Binds an ML-KEM-768 `e2e_pubkey` + fresh 64-hex nonce to a
//!   sealed [`VerifiedTeeEvidence`] token (`report_data[0..32] == SHA-256(ascii(nonce) || ascii(pubkey_b64))`),
//!   mandates paired GPU attestation by default, derives channel-bound HKDF-SHA256 keys +
//!   mandatory AEAD AAD, and enforces single-use invocation nonces + TTL expiry.

use std::collections::BTreeSet;

use crate::curves::{verify_signature, FixtureSigner, SignatureAlgorithm, SubjectPublicKey};
use crate::sha256::{
    base64_decode_strict, ct_eq, hex_decode_strict, hkdf_sha256_expand, hkdf_sha256_extract,
    sha256, Sha256,
};
use crate::tee::{chutes_report_data_binding, TeeVendor, VerifiedTeeEvidence};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Max authenticated HTTP JSON body accepted for field extraction (1 MiB).
pub const MAX_JSON_BODY_BYTES: usize = 1 << 20;
/// Max dotted JSON extraction path depth.
pub const MAX_JSON_PATH_DEPTH: usize = 64;
/// Max authenticated HTTP request or response wire bytes accepted (1 MiB body + 64 KiB headers).
pub const MAX_HTTP_WIRE_BYTES: usize = MAX_JSON_BODY_BYTES + 65_536;
/// Max unauthenticated range descriptors accepted in an envelope.
pub const MAX_UNAUTHED_RANGES: usize = 1024;
/// Exact length of an ML-KEM-768 public key (FIPS 203).
pub const ML_KEM_768_PUBKEY_LEN: usize = 1184;
/// Exact length of a 32-byte attestation nonce encoded as ASCII hex.
pub const CHUTES_NONCE_HEX_LEN: usize = 64;
/// Minimum ML-KEM ciphertext length required for HKDF salt extraction (`mlkem_ct[..16]`).
pub const ML_KEM_768_CT_LEN: usize = 1088;

/// HKDF info labels matching `breadstuffs/dregg-chutes-e2ee/src/crypto.rs:41-45`.
pub const E2EE_INFO_REQ: &[u8] = b"e2e-req-v1";
pub const E2EE_INFO_RESP: &[u8] = b"e2e-resp-v1";
pub const E2EE_INFO_STREAM: &[u8] = b"e2e-stream-v1";

// ---------------------------------------------------------------------------
// Registry-Pinned TLSNotary Verifier (V3 & V4 Closed)
// ---------------------------------------------------------------------------

/// One caller-pinned TLSNotary authority entry in [`PinnedNotaryRegistry`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedNotaryEntry {
    pub operator_id: String,
    /// [`notary_key_fingerprint`]: SHA-256 of the notary key's DER `SubjectPublicKeyInfo`.
    pub notary_key_sha256: [u8; 32],
    /// Permitted HTTPS server hostnames this notary may attest (non-empty).
    pub allowed_servers: Vec<String>,
    pub valid_from: u64,
    pub valid_until: u64,
}

/// Caller-supplied trust anchor registry for TLSNotary / `calltree` verification.
/// Replaces `dregg-oracle`'s vulnerable self-supplied `notary_key_hex` (`V3`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PinnedNotaryRegistry {
    entries: Vec<PinnedNotaryEntry>,
}

impl PinnedNotaryRegistry {
    pub fn new(entries: Vec<PinnedNotaryEntry>) -> Self {
        Self { entries }
    }

    pub fn push(&mut self, entry: PinnedNotaryEntry) {
        self.entries.push(entry);
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn find_pinned(&self, notary_key_sha256: &[u8; 32]) -> Option<&PinnedNotaryEntry> {
        self.entries
            .iter()
            .find(|e| ct_eq(&e.notary_key_sha256, notary_key_sha256))
    }
}

/// Untrusted TLSNotary HTTPS transcript envelope presented to [`verify_tlsn_transcript`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsnTranscriptEnvelope {
    pub server_name: String,
    pub expected_path: String,
    pub connection_time: u64,
    /// Authenticated HTTP request bytes sent to the server.
    pub sent_bytes: Vec<u8>,
    /// Authenticated HTTP response bytes received from the server.
    pub recv_bytes: Vec<u8>,
    /// Byte ranges `(start, end)` in `recv_bytes` that were NOT authenticated (redacted).
    /// Any range intersecting the HTTP response body is REFUSED (`V4`).
    pub unauthed_recv_ranges: Vec<(usize, usize)>,
    /// Notary verifying key carried by the presentation (P-256 or Ed25519). Trusted only if
    /// [`notary_key_fingerprint`] of it is pinned in the caller's registry.
    pub notary_public_key: SubjectPublicKey,
    /// `EcdsaP256Sha256` (DER signature) or `Ed25519`.
    pub notary_signature_alg: SignatureAlgorithm,
    /// Notary signature over [`tlsn_attestation_preimage`] of this envelope.
    pub notary_signature: Vec<u8>,
    /// Legacy/untrusted `notary_key_hex` field carried inside the wire JSON envelope.
    /// NEVER used as a trust anchor (`V3`); rejected if it does not match a pinned key.
    pub claimed_notary_key_hex: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationLeg {
    pub name: &'static str,
    pub detail: String,
}

/// Sealed verified HTTPS transcript produced exclusively by [`verify_tlsn_transcript`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedHttpsTranscript {
    server_name: String,
    request_path: String,
    notary_operator: String,
    notary_key_sha256: [u8; 32],
    connection_time: u64,
    status_code: u16,
    body_bytes: Vec<u8>,
    extracted_field: Option<String>,
    transcript_digest: [u8; 32],
    legs: Vec<VerificationLeg>,
}

impl VerifiedHttpsTranscript {
    pub fn server_name(&self) -> &str {
        &self.server_name
    }
    pub fn request_path(&self) -> &str {
        &self.request_path
    }
    pub fn notary_operator(&self) -> &str {
        &self.notary_operator
    }
    pub fn notary_key_sha256(&self) -> [u8; 32] {
        self.notary_key_sha256
    }
    pub fn connection_time(&self) -> u64 {
        self.connection_time
    }
    pub fn status_code(&self) -> u16 {
        self.status_code
    }
    pub fn body_bytes(&self) -> &[u8] {
        &self.body_bytes
    }
    pub fn extracted_field(&self) -> Option<&str> {
        self.extracted_field.as_deref()
    }
    pub fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }
    pub fn legs(&self) -> &[VerificationLeg] {
        &self.legs
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleError {
    EmptyNotaryRegistry,
    InvalidClock,
    UntrustedNotaryKey,
    ClaimedNotaryKeyMismatch,
    NotaryExpiredAtConnectionTime,
    ServerNotAllowedByNotary,
    UnsupportedNotaryAlgorithm,
    NotarySignatureInvalid,
    MalformedHttpRequest,
    HostHeaderMismatch,
    RequestPathMismatch,
    MalformedHttpResponse,
    UnauthedBodyBytes { range_start: usize, range_end: usize },
    ControlPlaneInjection,
    BodyTooLarge { actual: usize, max: usize },
    JsonPathTooDeep { depth: usize, max: usize },
    JsonMalformed,
    JsonDuplicateKey(String),
    JsonFieldNotFound(String),
    JsonTypeMismatch(String),
}

fn find_header_body_split(bytes: &[u8]) -> Option<usize> {
    bytes.windows(4).position(|w| w == b"\r\n\r\n")
}

fn validate_http_request(
    sent: &[u8],
    expected_host: &str,
    expected_path: &str,
) -> Result<(), OracleError> {
    if sent.len() > MAX_HTTP_WIRE_BYTES {
        return Err(OracleError::BodyTooLarge {
            actual: sent.len(),
            max: MAX_HTTP_WIRE_BYTES,
        });
    }
    if sent.contains(&0) {
        return Err(OracleError::ControlPlaneInjection);
    }
    let header_end = find_header_body_split(sent).ok_or(OracleError::MalformedHttpRequest)?;
    let head = std::str::from_utf8(&sent[..header_end]).map_err(|_| OracleError::MalformedHttpRequest)?;
    let mut lines = head.split("\r\n");
    let req_line = lines.next().ok_or(OracleError::MalformedHttpRequest)?;
    let mut parts = req_line.split(' ');
    let method = parts.next().ok_or(OracleError::MalformedHttpRequest)?;
    let path = parts.next().ok_or(OracleError::MalformedHttpRequest)?;
    let version = parts.next().ok_or(OracleError::MalformedHttpRequest)?;
    if parts.next().is_some()
        || method.is_empty()
        || !method.bytes().all(|b| b.is_ascii_uppercase())
        || !(version == "HTTP/1.1" || version == "HTTP/1.0")
    {
        return Err(OracleError::MalformedHttpRequest);
    }
    if path != expected_path {
        return Err(OracleError::RequestPathMismatch);
    }
    let mut found_host = None;
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let Some((k, v)) = line.split_once(':') else {
            return Err(OracleError::MalformedHttpRequest);
        };
        if k.eq_ignore_ascii_case("host") {
            if found_host.is_some() {
                return Err(OracleError::ControlPlaneInjection);
            }
            found_host = Some(v.trim());
        }
        if k.eq_ignore_ascii_case("transfer-encoding") {
            return Err(OracleError::ControlPlaneInjection);
        }
    }
    let host = found_host.ok_or(OracleError::HostHeaderMismatch)?;
    let normalized_host = host.strip_suffix(":443").unwrap_or(host);
    if !normalized_host.eq_ignore_ascii_case(expected_host) {
        return Err(OracleError::HostHeaderMismatch);
    }
    Ok(())
}

fn parse_http_response(recv: &[u8]) -> Result<(u16, usize, usize, &[u8]), OracleError> {
    if recv.len() > MAX_HTTP_WIRE_BYTES {
        return Err(OracleError::BodyTooLarge {
            actual: recv.len(),
            max: MAX_HTTP_WIRE_BYTES,
        });
    }
    if recv.contains(&0) {
        return Err(OracleError::ControlPlaneInjection);
    }
    let split = find_header_body_split(recv).ok_or(OracleError::MalformedHttpResponse)?;
    let head = std::str::from_utf8(&recv[..split]).map_err(|_| OracleError::MalformedHttpResponse)?;
    let mut lines = head.split("\r\n");
    let status_line = lines.next().ok_or(OracleError::MalformedHttpResponse)?;
    let status_line_end = status_line.len();
    let mut parts = status_line.split(' ');
    let ver = parts.next().ok_or(OracleError::MalformedHttpResponse)?;
    let code_str = parts.next().ok_or(OracleError::MalformedHttpResponse)?;
    if !(ver == "HTTP/1.1" || ver == "HTTP/1.0") || code_str.len() != 3 {
        return Err(OracleError::MalformedHttpResponse);
    }
    let status_code = code_str
        .parse::<u16>()
        .map_err(|_| OracleError::MalformedHttpResponse)?;
    let body_start = split + 4;
    let body = &recv[body_start..];
    let mut expected_cl: Option<usize> = None;
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let Some((k, v)) = line.split_once(':') else {
            return Err(OracleError::MalformedHttpResponse);
        };
        if k.eq_ignore_ascii_case("transfer-encoding") {
            // Chunked/compressed transfer codings are rejected unless decoded prior to attestation.
            return Err(OracleError::MalformedHttpResponse);
        }
        if k.eq_ignore_ascii_case("content-length") {
            let cl = v
                .trim()
                .parse::<usize>()
                .map_err(|_| OracleError::MalformedHttpResponse)?;
            if expected_cl.is_some_and(|prev| prev != cl) {
                return Err(OracleError::ControlPlaneInjection);
            }
            expected_cl = Some(cl);
        }
    }
    if let Some(cl) = expected_cl {
        if body.len() != cl {
            return Err(OracleError::MalformedHttpResponse);
        }
    }
    Ok((status_code, status_line_end, body_start, body))
}

/// Registry pin for a notary key: `SHA-256(SubjectPublicKeyInfo DER)`.
pub fn notary_key_fingerprint(key: &SubjectPublicKey) -> [u8; 32] {
    sha256(&key.to_spki_der())
}

/// Canonical length-framed bytes the notary signs: domain tag, server name, connection time,
/// sent and received transcripts, every unauthenticated range, and the notary key fingerprint
/// (so a signature cannot be replayed under a different pinned key).
pub fn tlsn_attestation_preimage(env: &TlsnTranscriptEnvelope) -> Vec<u8> {
    let mut out = b"OBEND.TLSN.NOTARY_ATTESTATION/v1".to_vec();
    let frame = |out: &mut Vec<u8>, b: &[u8]| {
        out.extend_from_slice(&(b.len() as u64).to_be_bytes());
        out.extend_from_slice(b);
    };
    frame(&mut out, env.server_name.as_bytes());
    out.extend_from_slice(&env.connection_time.to_be_bytes());
    frame(&mut out, &env.sent_bytes);
    frame(&mut out, &env.recv_bytes);
    out.extend_from_slice(&(env.unauthed_recv_ranges.len() as u64).to_be_bytes());
    for &(a, b) in &env.unauthed_recv_ranges {
        out.extend_from_slice(&(a as u64).to_be_bytes());
        out.extend_from_slice(&(b as u64).to_be_bytes());
    }
    out.extend_from_slice(&notary_key_fingerprint(&env.notary_public_key));
    out
}

/// Fixture helper: install `signer`'s key and a genuine notary signature over the envelope's
/// current contents. Test/fixture use only (see [`FixtureSigner`]).
pub fn fixture_notarize(
    env: &mut TlsnTranscriptEnvelope,
    signer: &FixtureSigner,
    alg: SignatureAlgorithm,
) {
    env.notary_public_key = signer.public_key();
    env.notary_signature_alg = alg;
    env.notary_signature = signer.sign(alg, &tlsn_attestation_preimage(env));
}

/// Verify an untrusted TLSNotary transcript envelope strictly against a caller-supplied
/// [`PinnedNotaryRegistry`], closing **`V3`** & **`V4`**.
pub fn verify_tlsn_transcript(
    registry: &PinnedNotaryRegistry,
    env: &TlsnTranscriptEnvelope,
    extract_field_path: Option<&str>,
    now_secs: u64,
) -> Result<VerifiedHttpsTranscript, OracleError> {
    if registry.is_empty() {
        return Err(OracleError::EmptyNotaryRegistry);
    }
    if now_secs == 0 || env.connection_time == 0 {
        return Err(OracleError::InvalidClock);
    }

    // V3: Strictly require the presentation's authenticated notary key to be in the caller's
    // PinnedNotaryRegistry — NEVER promote env.claimed_notary_key_hex to a trust anchor!
    let fingerprint = notary_key_fingerprint(&env.notary_public_key);
    let pinned = registry
        .find_pinned(&fingerprint)
        .ok_or(OracleError::UntrustedNotaryKey)?;

    if let Some(claimed_hex) = &env.claimed_notary_key_hex {
        let claimed_bytes =
            hex_decode_strict(claimed_hex).ok_or(OracleError::ClaimedNotaryKeyMismatch)?;
        if claimed_bytes.len() != 32 || !ct_eq(&claimed_bytes, &pinned.notary_key_sha256) {
            return Err(OracleError::ClaimedNotaryKeyMismatch);
        }
    }

    if env.connection_time < pinned.valid_from || env.connection_time > pinned.valid_until {
        return Err(OracleError::NotaryExpiredAtConnectionTime);
    }
    if !pinned
        .allowed_servers
        .iter()
        .any(|s| s.eq_ignore_ascii_case(&env.server_name))
    {
        return Err(OracleError::ServerNotAllowedByNotary);
    }
    if env.sent_bytes.len() > MAX_HTTP_WIRE_BYTES {
        return Err(OracleError::BodyTooLarge {
            actual: env.sent_bytes.len(),
            max: MAX_HTTP_WIRE_BYTES,
        });
    }
    if env.recv_bytes.len() > MAX_HTTP_WIRE_BYTES {
        return Err(OracleError::BodyTooLarge {
            actual: env.recv_bytes.len(),
            max: MAX_HTTP_WIRE_BYTES,
        });
    }
    if env.unauthed_recv_ranges.len() > MAX_UNAUTHED_RANGES {
        return Err(OracleError::ControlPlaneInjection);
    }
    match (&env.notary_public_key, env.notary_signature_alg) {
        (SubjectPublicKey::P256(_), SignatureAlgorithm::EcdsaP256Sha256)
        | (SubjectPublicKey::Ed25519(_), SignatureAlgorithm::Ed25519) => {}
        _ => return Err(OracleError::UnsupportedNotaryAlgorithm),
    }
    verify_signature(
        &env.notary_public_key,
        env.notary_signature_alg,
        &tlsn_attestation_preimage(env),
        &env.notary_signature,
    )
    .map_err(|_| OracleError::NotarySignatureInvalid)?;

    // V3: Pin both HTTP Host header and exact request path.
    validate_http_request(&env.sent_bytes, &env.server_name, &env.expected_path)?;

    // V4: Parse HTTP response and refuse ANY unauthenticated/redacted byte range intersecting
    // the status line, header names, colons, CRLF line delimiters, framing headers (`Content-Length`
    // / `Transfer-Encoding`), header-body delimiter, or response body (only values of non-framing
    // headers such as `Set-Cookie` may be redacted).
    let (status_code, status_line_end, body_start, body) = parse_http_response(&env.recv_bytes)?;
    let header_delim_start = body_start.saturating_sub(4);
    let mut allowed_value_spans: Vec<(usize, usize)> = Vec::new();
    let mut cursor = status_line_end + 2;
    while cursor < header_delim_start {
        let rel_end = env.recv_bytes[cursor..header_delim_start + 2]
            .windows(2)
            .position(|w| w == b"\r\n")
            .ok_or(OracleError::MalformedHttpResponse)?;
        let line_end = cursor + rel_end;
        let line = &env.recv_bytes[cursor..line_end];
        if let Some(colon_off) = line.iter().position(|&b| b == b':') {
            let name = std::str::from_utf8(&line[..colon_off])
                .map_err(|_| OracleError::MalformedHttpResponse)?;
            if !name.eq_ignore_ascii_case("content-length")
                && !name.eq_ignore_ascii_case("transfer-encoding")
            {
                let val_start = cursor + colon_off + 1;
                if val_start < line_end {
                    allowed_value_spans.push((val_start, line_end));
                }
            }
        }
        cursor = line_end + 2;
    }
    for &(start, end) in &env.unauthed_recv_ranges {
        let in_allowed_header_value = allowed_value_spans
            .iter()
            .any(|&(vs, ve)| start >= vs && end <= ve);
        if start >= end || end > env.recv_bytes.len() || !in_allowed_header_value {
            return Err(OracleError::UnauthedBodyBytes {
                range_start: start,
                range_end: end,
            });
        }
    }

    let mut legs = vec![
        VerificationLeg {
            name: "authentic-pinned-notary",
            detail: format!(
                "{:?} notary signature over the transcript verified under caller-pinned notary '{}'",
                env.notary_signature_alg, pinned.operator_id
            ),
        },
        VerificationLeg {
            name: "http-host-and-path-pinned",
            detail: format!("authenticated request pinned to {}{}", env.server_name, env.expected_path),
        },
        VerificationLeg {
            name: "complete-body-disclosure",
            detail: "zero unauthenticated/redacted byte ranges in HTTP delimiter or response body"
                .to_string(),
        },
    ];

    let extracted_field = match extract_field_path {
        Some(path) => {
            let body_str = std::str::from_utf8(body).map_err(|_| OracleError::JsonMalformed)?;
            let val = extract_json_field_strict(body_str, path)?;
            legs.push(VerificationLeg {
                name: "strict-rfc8259-json-field",
                detail: format!("duplicate-key-free RFC 8259 JSON extraction for '{path}'"),
            });
            Some(val)
        }
        None => None,
    };

    let mut h = Sha256::new();
    h.update(b"OBEND.ORACLE.TLSN_TRANSCRIPT/v1");
    h.update(&(env.server_name.len() as u64).to_be_bytes());
    h.update(env.server_name.as_bytes());
    h.update(&(env.expected_path.len() as u64).to_be_bytes());
    h.update(env.expected_path.as_bytes());
    h.update(&pinned.notary_key_sha256);
    h.update(&env.connection_time.to_be_bytes());
    h.update(&(env.sent_bytes.len() as u64).to_be_bytes());
    h.update(&env.sent_bytes);
    h.update(&(env.recv_bytes.len() as u64).to_be_bytes());
    h.update(&env.recv_bytes);
    h.update(&(env.unauthed_recv_ranges.len() as u64).to_be_bytes());
    for &(start, end) in &env.unauthed_recv_ranges {
        h.update(&(start as u64).to_be_bytes());
        h.update(&(end as u64).to_be_bytes());
    }
    match (extract_field_path, &extracted_field) {
        (Some(p), Some(v)) => {
            h.update(&[1u8]);
            h.update(&(p.len() as u64).to_be_bytes());
            h.update(p.as_bytes());
            h.update(&(v.len() as u64).to_be_bytes());
            h.update(v.as_bytes());
        }
        _ => h.update(&[0u8]),
    }
    let transcript_digest = h.finalize();

    Ok(VerifiedHttpsTranscript {
        server_name: env.server_name.clone(),
        request_path: env.expected_path.clone(),
        notary_operator: pinned.operator_id.clone(),
        notary_key_sha256: pinned.notary_key_sha256,
        connection_time: env.connection_time,
        status_code,
        body_bytes: body.to_vec(),
        extracted_field,
        transcript_digest,
        legs,
    })
}

// ---------------------------------------------------------------------------
// Strict RFC 8259 Duplicate-Key-Rejecting JSON Extractor (Zero External Crates)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum JsonVal {
    Null,
    Bool(bool),
    Number(String),
    Str(String),
    Array(Vec<JsonVal>),
    Object(Vec<(String, JsonVal)>),
}

struct JsonParser<'a> {
    s: &'a str,
    b: &'a [u8],
    pos: usize,
    depth: usize,
}

impl<'a> JsonParser<'a> {
    fn new(s: &'a str) -> Self {
        Self {
            s,
            b: s.as_bytes(),
            pos: 0,
            depth: 0,
        }
    }

    fn skip_ws(&mut self) {
        while let Some(&c) = self.b.get(self.pos) {
            if matches!(c, b' ' | b'\t' | b'\r' | b'\n') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn parse_value(&mut self) -> Result<JsonVal, OracleError> {
        self.skip_ws();
        let &ch = self.b.get(self.pos).ok_or(OracleError::JsonMalformed)?;
        match ch {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonVal::Str),
            b't' => self.expect_lit(b"true", JsonVal::Bool(true)),
            b'f' => self.expect_lit(b"false", JsonVal::Bool(false)),
            b'n' => self.expect_lit(b"null", JsonVal::Null),
            b'-' | b'0'..=b'9' => self.parse_number(),
            _ => Err(OracleError::JsonMalformed),
        }
    }

    fn expect_lit(&mut self, lit: &[u8], val: JsonVal) -> Result<JsonVal, OracleError> {
        if self.b.get(self.pos..self.pos + lit.len()) == Some(lit) {
            self.pos += lit.len();
            Ok(val)
        } else {
            Err(OracleError::JsonMalformed)
        }
    }

    fn parse_object(&mut self) -> Result<JsonVal, OracleError> {
        self.depth += 1;
        if self.depth > MAX_JSON_PATH_DEPTH {
            return Err(OracleError::JsonPathTooDeep {
                depth: self.depth,
                max: MAX_JSON_PATH_DEPTH,
            });
        }
        self.pos += 1; // '{'
        self.skip_ws();
        let mut entries = Vec::new();
        let mut seen = BTreeSet::new();
        if self.b.get(self.pos) == Some(&b'}') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(JsonVal::Object(entries));
        }
        loop {
            self.skip_ws();
            if self.b.get(self.pos) != Some(&b'"') {
                return Err(OracleError::JsonMalformed);
            }
            let key = self.parse_string()?;
            if !seen.insert(key.clone()) {
                return Err(OracleError::JsonDuplicateKey(key));
            }
            self.skip_ws();
            if self.b.get(self.pos) != Some(&b':') {
                return Err(OracleError::JsonMalformed);
            }
            self.pos += 1;
            let val = self.parse_value()?;
            entries.push((key, val));
            self.skip_ws();
            match self.b.get(self.pos) {
                Some(&b',') => {
                    self.pos += 1;
                }
                Some(&b'}') => {
                    self.pos += 1;
                    self.depth -= 1;
                    return Ok(JsonVal::Object(entries));
                }
                _ => return Err(OracleError::JsonMalformed),
            }
        }
    }

    fn parse_array(&mut self) -> Result<JsonVal, OracleError> {
        self.depth += 1;
        if self.depth > MAX_JSON_PATH_DEPTH {
            return Err(OracleError::JsonPathTooDeep {
                depth: self.depth,
                max: MAX_JSON_PATH_DEPTH,
            });
        }
        self.pos += 1; // '['
        self.skip_ws();
        let mut items = Vec::new();
        if self.b.get(self.pos) == Some(&b']') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(JsonVal::Array(items));
        }
        loop {
            items.push(self.parse_value()?);
            self.skip_ws();
            match self.b.get(self.pos) {
                Some(&b',') => self.pos += 1,
                Some(&b']') => {
                    self.pos += 1;
                    self.depth -= 1;
                    return Ok(JsonVal::Array(items));
                }
                _ => return Err(OracleError::JsonMalformed),
            }
        }
    }

    fn parse_string(&mut self) -> Result<String, OracleError> {
        self.pos += 1; // '"'
        let mut out = String::new();
        while let Some(&c) = self.b.get(self.pos) {
            if c == b'"' {
                self.pos += 1;
                return Ok(out);
            }
            if c < 0x20 {
                return Err(OracleError::JsonMalformed);
            }
            if c == b'\\' {
                self.pos += 1;
                let &esc = self.b.get(self.pos).ok_or(OracleError::JsonMalformed)?;
                self.pos += 1;
                match esc {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'b' => out.push('\u{0008}'),
                    b'f' => out.push('\u{000c}'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let hex_slice = self
                            .b
                            .get(self.pos..self.pos + 4)
                            .ok_or(OracleError::JsonMalformed)?;
                        let hex_str = std::str::from_utf8(hex_slice)
                            .map_err(|_| OracleError::JsonMalformed)?;
                        let code = u16::from_str_radix(hex_str, 16)
                            .map_err(|_| OracleError::JsonMalformed)?;
                        self.pos += 4;
                        let ch = if (0xD800..=0xDBFF).contains(&code) {
                            // High surrogate must be followed immediately by `\uDC00..\uDFFF`.
                            if self.b.get(self.pos..self.pos + 2) != Some(b"\\u") {
                                return Err(OracleError::JsonMalformed);
                            }
                            self.pos += 2;
                            let lo_slice = self
                                .b
                                .get(self.pos..self.pos + 4)
                                .ok_or(OracleError::JsonMalformed)?;
                            let lo_str = std::str::from_utf8(lo_slice)
                                .map_err(|_| OracleError::JsonMalformed)?;
                            let lo = u16::from_str_radix(lo_str, 16)
                                .map_err(|_| OracleError::JsonMalformed)?;
                            if !(0xDC00..=0xDFFF).contains(&lo) {
                                return Err(OracleError::JsonMalformed);
                            }
                            self.pos += 4;
                            let cp = 0x10000
                                + ((u32::from(code) - 0xD800) << 10)
                                + (u32::from(lo) - 0xDC00);
                            char::from_u32(cp).ok_or(OracleError::JsonMalformed)?
                        } else {
                            char::from_u32(u32::from(code)).ok_or(OracleError::JsonMalformed)?
                        };
                        out.push(ch);
                    }
                    _ => return Err(OracleError::JsonMalformed),
                }
            } else {
                // O(1) UTF-8 character advance (input `self.s` is already validated `&str`).
                let ch = self.s[self.pos..]
                    .chars()
                    .next()
                    .ok_or(OracleError::JsonMalformed)?;
                out.push(ch);
                self.pos += ch.len_utf8();
            }
        }
        Err(OracleError::JsonMalformed)
    }

    fn parse_number(&mut self) -> Result<JsonVal, OracleError> {
        let start = self.pos;
        if self.b.get(self.pos) == Some(&b'-') {
            self.pos += 1;
        }
        match self.b.get(self.pos) {
            Some(&b'0') => self.pos += 1,
            Some(b'1'..=b'9') => {
                self.pos += 1;
                while matches!(self.b.get(self.pos), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
            }
            _ => return Err(OracleError::JsonMalformed),
        }
        if self.b.get(self.pos) == Some(&b'.') {
            self.pos += 1;
            if !matches!(self.b.get(self.pos), Some(b'0'..=b'9')) {
                return Err(OracleError::JsonMalformed);
            }
            while matches!(self.b.get(self.pos), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
        }
        if matches!(self.b.get(self.pos), Some(b'e' | b'E')) {
            self.pos += 1;
            if matches!(self.b.get(self.pos), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            if !matches!(self.b.get(self.pos), Some(b'0'..=b'9')) {
                return Err(OracleError::JsonMalformed);
            }
            while matches!(self.b.get(self.pos), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
        }
        let s = std::str::from_utf8(&self.b[start..self.pos])
            .map_err(|_| OracleError::JsonMalformed)?;
        Ok(JsonVal::Number(s.to_string()))
    }
}

fn render_json_val(v: &JsonVal) -> String {
    match v {
        JsonVal::Null => "null".to_string(),
        JsonVal::Bool(true) => "true".to_string(),
        JsonVal::Bool(false) => "false".to_string(),
        JsonVal::Number(s) | JsonVal::Str(s) => s.clone(),
        JsonVal::Array(items) => {
            let inner: Vec<String> = items.iter().map(render_json_val).collect();
            format!("[{}]", inner.join(","))
        }
        JsonVal::Object(entries) => {
            let inner: Vec<String> = entries
                .iter()
                .map(|(k, val)| format!("\"{k}\":{}", render_json_val(val)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
    }
}

/// Strictly parse RFC 8259 JSON (rejecting duplicate object keys at EVERY nesting level) and
/// walk a dotted path (`"data.amount"` or `"items.0.price"`).
pub fn extract_json_field_strict(body: &str, field_path: &str) -> Result<String, OracleError> {
    if body.len() > MAX_JSON_BODY_BYTES {
        return Err(OracleError::BodyTooLarge {
            actual: body.len(),
            max: MAX_JSON_BODY_BYTES,
        });
    }
    let mut parser = JsonParser::new(body);
    let root = parser.parse_value()?;
    parser.skip_ws();
    if parser.pos != parser.b.len() {
        return Err(OracleError::JsonMalformed);
    }

    if field_path.is_empty() {
        return Ok(render_json_val(&root));
    }
    let segs: Vec<&str> = field_path.split('.').collect();
    if segs.len() > MAX_JSON_PATH_DEPTH {
        return Err(OracleError::JsonPathTooDeep {
            depth: segs.len(),
            max: MAX_JSON_PATH_DEPTH,
        });
    }

    let mut cur = &root;
    for seg in segs {
        match cur {
            JsonVal::Object(entries) => {
                let (_, next) = entries
                    .iter()
                    .find(|(k, _)| k == seg)
                    .ok_or_else(|| OracleError::JsonFieldNotFound(seg.to_string()))?;
                cur = next;
            }
            JsonVal::Array(items) => {
                let idx = seg
                    .parse::<usize>()
                    .map_err(|_| OracleError::JsonTypeMismatch(seg.to_string()))?;
                cur = items
                    .get(idx)
                    .ok_or_else(|| OracleError::JsonFieldNotFound(seg.to_string()))?;
            }
            _ => return Err(OracleError::JsonTypeMismatch(seg.to_string())),
        }
    }
    Ok(render_json_val(cur))
}

// ---------------------------------------------------------------------------
// Multi-Hop CallTree Verifier (`breadstuffs/calltree/verify`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallTreeHop {
    pub hop_id: String,
    pub envelope: TlsnTranscriptEnvelope,
    pub extract_field: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallTreeEdge {
    pub parent_index: usize,
    pub child_index: usize,
    /// Required substring or digest token from parent that must appear in child's authenticated request.
    pub binding_token: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallTreeRecording {
    pub policy_digest: [u8; 32],
    pub hops: Vec<CallTreeHop>,
    pub edges: Vec<CallTreeEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallTreeError {
    EmptyRecording,
    HopFailed { index: usize, error: OracleError },
    EdgeOutOfBounds { edge_index: usize },
    EdgeNotCausalOrder { edge_index: usize },
    EdgeBindingMissing { edge_index: usize },
    RootDigestMismatch { expected: [u8; 32], computed: [u8; 32] },
}

/// Sealed verified multi-hop `calltree` execution DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedCallTree {
    root_digest: [u8; 32],
    policy_digest: [u8; 32],
    hops: Vec<VerifiedHttpsTranscript>,
}

impl VerifiedCallTree {
    pub fn root_digest(&self) -> [u8; 32] {
        self.root_digest
    }
    pub fn policy_digest(&self) -> [u8; 32] {
        self.policy_digest
    }
    pub fn hops(&self) -> &[VerifiedHttpsTranscript] {
        &self.hops
    }
}

/// Compute the deterministic root digest of verified calltree hops + edges + policy.
pub fn compute_calltree_root(
    policy_digest: &[u8; 32],
    hop_digests: &[[u8; 32]],
    edges: &[CallTreeEdge],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"OBEND.CALLTREE.ROOT/v1");
    h.update(policy_digest);
    h.update(&(hop_digests.len() as u64).to_be_bytes());
    for d in hop_digests {
        h.update(d);
    }
    h.update(&(edges.len() as u64).to_be_bytes());
    for e in edges {
        h.update(&(e.parent_index as u64).to_be_bytes());
        h.update(&(e.child_index as u64).to_be_bytes());
        h.update(&(e.binding_token.len() as u32).to_be_bytes());
        h.update(e.binding_token.as_bytes());
    }
    h.finalize()
}

/// Verify a recorded multi-hop call tree against a caller-pinned [`PinnedNotaryRegistry`]
/// and expected root digest (mirroring `calltree/verify/src/main.rs`).
pub fn verify_calltree_recording(
    registry: &PinnedNotaryRegistry,
    recording: &CallTreeRecording,
    expected_root: &[u8; 32],
    now_secs: u64,
) -> Result<VerifiedCallTree, CallTreeError> {
    if recording.hops.is_empty() {
        return Err(CallTreeError::EmptyRecording);
    }
    let mut verified_hops = Vec::with_capacity(recording.hops.len());
    let mut hop_digests = Vec::with_capacity(recording.hops.len());
    for (i, hop) in recording.hops.iter().enumerate() {
        let vh = verify_tlsn_transcript(
            registry,
            &hop.envelope,
            hop.extract_field.as_deref(),
            now_secs,
        )
        .map_err(|error| CallTreeError::HopFailed { index: i, error })?;
        hop_digests.push(vh.transcript_digest());
        verified_hops.push(vh);
    }

    for (edge_index, edge) in recording.edges.iter().enumerate() {
        if edge.parent_index >= recording.hops.len() || edge.child_index >= recording.hops.len() {
            return Err(CallTreeError::EdgeOutOfBounds { edge_index });
        }
        // Require strictly topological causal edge order and monotone connection timestamps.
        if edge.parent_index >= edge.child_index
            || verified_hops[edge.parent_index].connection_time()
                > verified_hops[edge.child_index].connection_time()
        {
            return Err(CallTreeError::EdgeNotCausalOrder { edge_index });
        }
        if edge.binding_token.is_empty() {
            return Err(CallTreeError::EdgeBindingMissing { edge_index });
        }
        let parent_body = verified_hops[edge.parent_index].body_bytes();
        let child_sent = &recording.hops[edge.child_index].envelope.sent_bytes;
        let tok = edge.binding_token.as_bytes();
        let in_parent = parent_body.windows(tok.len()).any(|w| w == tok);
        let in_child = child_sent.windows(tok.len()).any(|w| w == tok);
        if !in_parent || !in_child {
            return Err(CallTreeError::EdgeBindingMissing { edge_index });
        }
    }

    let computed = compute_calltree_root(&recording.policy_digest, &hop_digests, &recording.edges);
    if !ct_eq(&computed, expected_root) {
        return Err(CallTreeError::RootDigestMismatch {
            expected: *expected_root,
            computed,
        });
    }

    Ok(VerifiedCallTree {
        root_digest: computed,
        policy_digest: recording.policy_digest,
        hops: verified_hops,
    })
}

// ---------------------------------------------------------------------------
// Hardened E2EE Prompt/Response Session Channel Binding (`dregg-chutes-e2ee`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelDirection {
    Request,
    Response,
    Stream,
}

impl ChannelDirection {
    pub const fn hkdf_info(self) -> &'static [u8] {
        match self {
            Self::Request => E2EE_INFO_REQ,
            Self::Response => E2EE_INFO_RESP,
            Self::Stream => E2EE_INFO_STREAM,
        }
    }

    pub const fn aad_tag(self) -> &'static [u8] {
        match self {
            Self::Request => b"REQ",
            Self::Response => b"RESP",
            Self::Stream => b"STREAM",
        }
    }
}

/// Policy governing CPU + GPU attestation requirements for an E2EE inference channel.
/// Defaults to mandatory CPU + GPU attestation (closing `narrator_backend.rs:391`'s opt-in gap).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct E2eeChannelPolicy {
    pub min_gpus: usize,
    pub ttl_secs: u64,
}

impl Default for E2eeChannelPolicy {
    fn default() -> Self {
        Self {
            min_gpus: 1,
            ttl_secs: 1800,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct E2eeChannelInput {
    pub chute_id: String,
    pub instance_id: String,
    /// Fresh 64-char ASCII hex attestation nonce (32 bytes).
    pub attestation_nonce_hex: String,
    /// Standard Base64 encoding of the enclave's 1184-byte ML-KEM-768 public key.
    pub e2e_pubkey_b64: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum E2eeChannelError {
    EmptyIdentity,
    InvalidClock,
    InvalidAttestationNonce,
    MalformedMlKemPubkey,
    CpuTeeVendorRequired,
    ReportDataBindingMismatch,
    InsufficientAttestedGpus { required: usize, actual: usize },
    DuplicateGpuDevice,
    GpuEvidenceVendorMismatch,
    GpuNonceMismatch,
    GpuMissingFwid,
    InvalidKemCiphertextLen,
    SessionExpired,
    InvocationNonceReplayed,
    EmptyInvocationNonce,
}

/// Sealed verified E2EE session channel bound to attested CPU TEE + GPU evidence.
/// Private fields prevent constructing a channel from unattested or MITM-swapped keys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedE2eeChannel {
    chute_id: String,
    instance_id: String,
    mlkem768_pubkey: Vec<u8>,
    attestation_nonce: [u8; 32],
    cpu_evidence_digest: [u8; 32],
    gpu_fwids: Vec<[u8; 48]>,
    channel_binding_id: [u8; 32],
    established_at: u64,
    ttl_secs: u64,
}

impl VerifiedE2eeChannel {
    pub fn chute_id(&self) -> &str {
        &self.chute_id
    }
    pub fn instance_id(&self) -> &str {
        &self.instance_id
    }
    pub fn mlkem768_pubkey(&self) -> &[u8] {
        &self.mlkem768_pubkey
    }
    pub fn attestation_nonce(&self) -> [u8; 32] {
        self.attestation_nonce
    }
    pub fn cpu_evidence_digest(&self) -> [u8; 32] {
        self.cpu_evidence_digest
    }
    pub fn gpu_fwids(&self) -> &[[u8; 48]] {
        &self.gpu_fwids
    }
    pub fn channel_binding_id(&self) -> [u8; 32] {
        self.channel_binding_id
    }
    pub fn established_at(&self) -> u64 {
        self.established_at
    }
    pub fn ttl_secs(&self) -> u64 {
        self.ttl_secs
    }

    /// Derive the directional HKDF-SHA256 key (`salt = mlkem_ct[..16]`) bound to this channel.
    pub fn derive_bound_session_key(
        &self,
        shared_secret: &[u8; 32],
        mlkem_ct: &[u8],
        direction: ChannelDirection,
    ) -> Result<[u8; 32], E2eeChannelError> {
        if mlkem_ct.len() != ML_KEM_768_CT_LEN {
            return Err(E2eeChannelError::InvalidKemCiphertextLen);
        }
        let base_key = derive_chutes_session_key(shared_secret, mlkem_ct, direction)?;
        let mut info = Vec::with_capacity(64);
        info.extend_from_slice(b"OBEND.E2EE.BOUND_KEY/v1");
        info.extend_from_slice(direction.hkdf_info());
        info.extend_from_slice(&self.channel_binding_id);
        Ok(hkdf_sha256_expand(&base_key, &info))
    }

    /// Derive mandatory ChaCha20-Poly1305 AEAD AAD binding `(channel_binding_id, instance_id,
    /// invocation_nonce, direction)` — closing `dregg-chutes-e2ee`'s missing AEAD AAD gap.
    pub fn derive_aad(&self, invocation_nonce: &str, direction: ChannelDirection) -> [u8; 32] {
        derive_channel_aad(
            &self.channel_binding_id,
            &self.instance_id,
            invocation_nonce,
            direction,
        )
    }
}

/// Wire-compatible Chutes HKDF-SHA256 key derivation (`salt = mlkem_ct[..16]`, `info = e2e-*-v1`).
pub fn derive_chutes_session_key(
    shared_secret: &[u8; 32],
    mlkem_ct: &[u8],
    direction: ChannelDirection,
) -> Result<[u8; 32], E2eeChannelError> {
    if mlkem_ct.len() < 16 {
        return Err(E2eeChannelError::InvalidKemCiphertextLen);
    }
    let prk = hkdf_sha256_extract(&mlkem_ct[..16], shared_secret);
    Ok(hkdf_sha256_expand(&prk, direction.hkdf_info()))
}

/// Compute mandatory channel-bound AEAD AAD digest.
pub fn derive_channel_aad(
    channel_binding_id: &[u8; 32],
    instance_id: &str,
    invocation_nonce: &str,
    direction: ChannelDirection,
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"OBEND.E2EE.AEAD_AAD/v1");
    h.update(channel_binding_id);
    h.update(&(instance_id.len() as u32).to_be_bytes());
    h.update(instance_id.as_bytes());
    h.update(&(invocation_nonce.len() as u32).to_be_bytes());
    h.update(invocation_nonce.as_bytes());
    h.update(direction.aad_tag());
    h.finalize()
}

/// Bind an E2EE ML-KEM-768 prompt/response session channel strictly to a sealed CPU
/// [`VerifiedTeeEvidence`] token (and mandatory GPU [`VerifiedTeeEvidence`] tokens under
/// `policy.min_gpus`). Rejects unpinned or MITM-substituted session keys fail-closed.
pub fn verify_e2ee_channel(
    policy: &E2eeChannelPolicy,
    input: &E2eeChannelInput,
    cpu_tee: &VerifiedTeeEvidence,
    gpu_tees: &[VerifiedTeeEvidence],
    now_secs: u64,
) -> Result<VerifiedE2eeChannel, E2eeChannelError> {
    if input.chute_id.is_empty() || input.instance_id.is_empty() {
        return Err(E2eeChannelError::EmptyIdentity);
    }
    if now_secs == 0 {
        return Err(E2eeChannelError::InvalidClock);
    }
    if matches!(cpu_tee.vendor(), TeeVendor::NvidiaGpu(_)) {
        return Err(E2eeChannelError::CpuTeeVendorRequired);
    }
    // Enforce evidence freshness so stale TEE tokens cannot mint renewed session TTLs.
    if cpu_tee.verified_at() > now_secs
        || now_secs.saturating_sub(cpu_tee.verified_at()) > policy.ttl_secs
    {
        return Err(E2eeChannelError::SessionExpired);
    }
    for gpu in gpu_tees {
        if gpu.verified_at() > now_secs
            || now_secs.saturating_sub(gpu.verified_at()) > policy.ttl_secs
        {
            return Err(E2eeChannelError::SessionExpired);
        }
    }

    // Validate 64-hex-char (32-byte) attestation nonce.
    if input.attestation_nonce_hex.len() != CHUTES_NONCE_HEX_LEN {
        return Err(E2eeChannelError::InvalidAttestationNonce);
    }
    let nonce_vec = hex_decode_strict(&input.attestation_nonce_hex)
        .ok_or(E2eeChannelError::InvalidAttestationNonce)?;
    if nonce_vec.len() != 32 || nonce_vec.iter().all(|&b| b == 0) {
        return Err(E2eeChannelError::InvalidAttestationNonce);
    }
    let mut attestation_nonce = [0u8; 32];
    attestation_nonce.copy_from_slice(&nonce_vec);

    // Validate ML-KEM-768 public key base64 strictly decodes to 1184 bytes.
    let mlkem768_pubkey = base64_decode_strict(&input.e2e_pubkey_b64)
        .ok_or(E2eeChannelError::MalformedMlKemPubkey)?;
    if mlkem768_pubkey.len() != ML_KEM_768_PUBKEY_LEN {
        return Err(E2eeChannelError::MalformedMlKemPubkey);
    }

    // Core channel binding: CPU TEE report_data[0..32] == SHA-256(ascii(nonce_hex) || ascii(pubkey_b64)).
    let expected_rd =
        chutes_report_data_binding(&input.attestation_nonce_hex, &input.e2e_pubkey_b64);
    if !ct_eq(&cpu_tee.report_data_32(), &expected_rd) {
        return Err(E2eeChannelError::ReportDataBindingMismatch);
    }

    // Enforce GPU attestation count + same-nonce binding + FWID presence.
    if gpu_tees.len() < policy.min_gpus {
        return Err(E2eeChannelError::InsufficientAttestedGpus {
            required: policy.min_gpus,
            actual: gpu_tees.len(),
        });
    }
    let mut gpu_fwids = Vec::with_capacity(gpu_tees.len());
    let mut seen_gpu_keys = BTreeSet::new();
    let mut bind_hasher = Sha256::new();
    bind_hasher.update(b"OBEND.E2EE.CHANNEL_BIND/v1");
    bind_hasher.update(&(input.chute_id.len() as u64).to_be_bytes());
    bind_hasher.update(input.chute_id.as_bytes());
    bind_hasher.update(&(input.instance_id.len() as u64).to_be_bytes());
    bind_hasher.update(input.instance_id.as_bytes());
    bind_hasher.update(&cpu_tee.evidence_digest());
    bind_hasher.update(&attestation_nonce);
    bind_hasher.update(&sha256(&mlkem768_pubkey));
    bind_hasher.update(&(gpu_tees.len() as u64).to_be_bytes());

    for gpu in gpu_tees {
        if !matches!(gpu.vendor(), TeeVendor::NvidiaGpu(_)) {
            return Err(E2eeChannelError::GpuEvidenceVendorMismatch);
        }
        if !seen_gpu_keys.insert(gpu.leaf_spki_sha256()) {
            return Err(E2eeChannelError::DuplicateGpuDevice);
        }
        if !ct_eq(&gpu.report_data_32(), &attestation_nonce) {
            return Err(E2eeChannelError::GpuNonceMismatch);
        }
        let fwid = gpu.gpu_fwid().ok_or(E2eeChannelError::GpuMissingFwid)?;
        bind_hasher.update(&gpu.evidence_digest());
        bind_hasher.update(&fwid);
        gpu_fwids.push(fwid);
    }

    let channel_binding_id = bind_hasher.finalize();
    Ok(VerifiedE2eeChannel {
        chute_id: input.chute_id.clone(),
        instance_id: input.instance_id.clone(),
        mlkem768_pubkey,
        attestation_nonce,
        cpu_evidence_digest: cpu_tee.evidence_digest(),
        gpu_fwids,
        channel_binding_id,
        established_at: now_secs,
        ttl_secs: policy.ttl_secs,
    })
}

/// Stateful per-session guard enforcing TTL expiry and single-use invocation nonces.
#[derive(Debug, Clone)]
pub struct E2eeSessionGuard {
    channel: VerifiedE2eeChannel,
    consumed_invocation_nonces: BTreeSet<String>,
}

impl E2eeSessionGuard {
    pub fn new(channel: VerifiedE2eeChannel) -> Self {
        Self {
            channel,
            consumed_invocation_nonces: BTreeSet::new(),
        }
    }

    pub fn channel(&self) -> &VerifiedE2eeChannel {
        &self.channel
    }

    /// Consume a single-use invocation nonce within the channel TTL and return the bound AEAD AAD.
    pub fn authorize_invocation(
        &mut self,
        invocation_nonce: &str,
        direction: ChannelDirection,
        now_secs: u64,
    ) -> Result<[u8; 32], E2eeChannelError> {
        if invocation_nonce.is_empty() {
            return Err(E2eeChannelError::EmptyInvocationNonce);
        }
        if now_secs < self.channel.established_at
            || now_secs.saturating_sub(self.channel.established_at) >= self.channel.ttl_secs
        {
            return Err(E2eeChannelError::SessionExpired);
        }
        if !self
            .consumed_invocation_nonces
            .insert(invocation_nonce.to_string())
        {
            return Err(E2eeChannelError::InvocationNonceReplayed);
        }
        Ok(self.channel.derive_aad(invocation_nonce, direction))
    }
}

#[cfg(test)]
mod notary_signature_tests {
    use super::*;

    const NOW: u64 = 1_780_000_000;

    fn envelope() -> TlsnTranscriptEnvelope {
        TlsnTranscriptEnvelope {
            server_name: "api.coinbase.com".to_string(),
            expected_path: "/v2/prices/BTC-USD/spot".to_string(),
            connection_time: NOW - 10,
            sent_bytes: b"GET /v2/prices/BTC-USD/spot HTTP/1.1\r\nHost: api.coinbase.com\r\n\r\n".to_vec(),
            recv_bytes: b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"data\":{\"amount\":\"98450.25\"}}".to_vec(),
            unauthed_recv_ranges: vec![],
            notary_public_key: SubjectPublicKey::Ed25519([0u8; 32]),
            notary_signature_alg: SignatureAlgorithm::Ed25519,
            notary_signature: vec![],
            claimed_notary_key_hex: None,
        }
    }

    fn registry(keys: &[&FixtureSigner]) -> PinnedNotaryRegistry {
        PinnedNotaryRegistry::new(
            keys.iter()
                .enumerate()
                .map(|(i, k)| PinnedNotaryEntry {
                    operator_id: format!("notary-{i}"),
                    notary_key_sha256: notary_key_fingerprint(&k.public_key()),
                    allowed_servers: vec!["api.coinbase.com".to_string()],
                    valid_from: NOW - 86_400,
                    valid_until: NOW + 86_400,
                })
                .collect(),
        )
    }

    #[test]
    fn genuine_p256_and_ed25519_notary_signatures_verify() {
        for (signer, alg) in [
            (FixtureSigner::p256(b"notary-p256"), SignatureAlgorithm::EcdsaP256Sha256),
            (FixtureSigner::ed25519(b"notary-ed"), SignatureAlgorithm::Ed25519),
        ] {
            let reg = registry(&[&signer]);
            let mut env = envelope();
            fixture_notarize(&mut env, &signer, alg);
            let v = verify_tlsn_transcript(&reg, &env, Some("data.amount"), NOW).unwrap();
            assert_eq!(v.extracted_field(), Some("98450.25"));
            // Any transcript byte flipped after signing is refused.
            let mut tampered = env.clone();
            *tampered.recv_bytes.last_mut().unwrap() ^= 1;
            assert_eq!(
                verify_tlsn_transcript(&reg, &tampered, None, NOW).unwrap_err(),
                OracleError::NotarySignatureInvalid
            );
            let mut redacted = env.clone();
            redacted.unauthed_recv_ranges = vec![(0, 1)];
            assert_eq!(
                verify_tlsn_transcript(&reg, &redacted, None, NOW).unwrap_err(),
                OracleError::NotarySignatureInvalid
            );
        }
    }

    #[test]
    fn rogue_replayed_and_unsupported_notaries_refused() {
        let trusted = FixtureSigner::p256(b"trusted");
        let other_pinned = FixtureSigner::p256(b"other-pinned");
        let rogue = FixtureSigner::p256(b"rogue");
        let reg = registry(&[&trusted, &other_pinned]);
        // Rogue self-signed envelope: key not pinned.
        let mut env = envelope();
        fixture_notarize(&mut env, &rogue, SignatureAlgorithm::EcdsaP256Sha256);
        assert_eq!(
            verify_tlsn_transcript(&reg, &env, None, NOW).unwrap_err(),
            OracleError::UntrustedNotaryKey
        );
        // A genuine signature by `trusted` presented under another pinned key is refused.
        let mut env = envelope();
        fixture_notarize(&mut env, &trusted, SignatureAlgorithm::EcdsaP256Sha256);
        env.notary_public_key = other_pinned.public_key();
        assert_eq!(
            verify_tlsn_transcript(&reg, &env, None, NOW).unwrap_err(),
            OracleError::NotarySignatureInvalid
        );
        // RSA notary keys are outside the accepted notary algorithms.
        let rsa = FixtureSigner::rsa(2048);
        let reg = registry(&[&rsa]);
        let mut env = envelope();
        fixture_notarize(&mut env, &rsa, SignatureAlgorithm::RsaPkcs1Sha256);
        assert_eq!(
            verify_tlsn_transcript(&reg, &env, None, NOW).unwrap_err(),
            OracleError::UnsupportedNotaryAlgorithm
        );
    }
}
