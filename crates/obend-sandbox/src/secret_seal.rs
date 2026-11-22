#![forbid(unsafe_code)]
//! Slot-Path-Bound AEAD Secret Sealing & `0600` Encrypted File Store.
//!
//! Quarried and hardened from `breadstuffs/secrets/src/{encrypted.rs,store.rs}`:
//! - Fixes `secrets/src/encrypted.rs:62-88` (which omitted `(namespace, key)` from AEAD associated
//!   data, allowing ciphertext file swapping across secret slots!) by injectively length-framing
//!   `(namespace, key, context_aad)` into the RFC 8439 `ChaCha20-Poly1305` AEAD AAD.
//! - Derives per-envelope 256-bit AEAD subkeys via NIST SP 800-185 `cSHAKE256` over `(master_key,
//!   16B salt)` paired with a 96-bit OS CSPRNG nonce (`224`-bit effective random nonce+salt space).
//! - Fails closed if `/dev/urandom` cannot supply full entropy (`CAP-29` anti-zero-RNG invariant).
//! - Scrubs secret material from RAM on `Drop`.

use std::collections::BTreeMap;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use obend_crypto_exec::transcript::cshake256_32;
use serde::{Deserialize, Serialize};

static SECRET_TMP_SEQ: AtomicU64 = AtomicU64::new(1);

/// Envelope wire header (`"OBS1"` = Obend Slot-Bound Secret v1):
/// `[magic : 4B "OBS1"][salt : 16B][nonce : 12B][ciphertext : N][poly1305_tag : 16B]`
pub const SECRET_ENVELOPE_MAGIC: &[u8; 4] = b"OBS1";
const SALT_LEN: usize = 16;
const NONCE_LEN: usize = 12;
const TAG_LEN: usize = 16;
const HEADER_LEN: usize = 4 + SALT_LEN + NONCE_LEN;

/// Canonical `(namespace, key)` secret slot identifier.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SecretSlotId {
    pub namespace: String,
    pub key: String,
}

impl SecretSlotId {
    pub fn new(namespace: impl Into<String>, key: impl Into<String>) -> Self {
        Self {
            namespace: namespace.into(),
            key: key.into(),
        }
    }

    pub fn validate(&self) -> Result<(), SecretSealError> {
        if self.namespace.is_empty() || self.key.is_empty() {
            return Err(SecretSealError::InvalidSlotId(
                "secret namespace and key must both be non-empty".into(),
            ));
        }
        if self.namespace.contains('\0') || self.key.contains('\0') {
            return Err(SecretSealError::InvalidSlotId(
                "secret namespace and key must not contain NUL bytes".into(),
            ));
        }
        Ok(())
    }

    /// Construct the injective, length-framed AEAD Associated Data (AAD) binding both
    /// `namespace` and `key` plus optional caller `context_aad`.
    ///
    /// Because both `namespace` and `key` carry explicit 64-bit big-endian byte lengths,
    /// `("ab", "c")` and `("a", "bc")` have strictly disjoint AAD byte strings.
    pub fn canonical_aad(&self, context_aad: &[u8]) -> Vec<u8> {
        let mut aad =
            Vec::with_capacity(32 + self.namespace.len() + self.key.len() + context_aad.len());
        aad.extend_from_slice(b"OBEND-SECRET-SLOT-AAD-V1:");
        aad.extend_from_slice(&(self.namespace.len() as u64).to_be_bytes());
        aad.extend_from_slice(self.namespace.as_bytes());
        aad.extend_from_slice(&(self.key.len() as u64).to_be_bytes());
        aad.extend_from_slice(self.key.as_bytes());
        aad.extend_from_slice(&(context_aad.len() as u64).to_be_bytes());
        aad.extend_from_slice(context_aad);
        aad
    }
}

impl fmt::Display for SecretSlotId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.namespace, self.key)
    }
}

/// Zeroize-on-drop secret byte buffer (`Debug` redacts contents).
#[derive(Clone)]
pub struct SecretValue {
    inner: Vec<u8>,
}

impl SecretValue {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self { inner: bytes }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.inner
    }

    pub fn as_str(&self) -> Option<&str> {
        std::str::from_utf8(&self.inner).ok()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl Drop for SecretValue {
    fn drop(&mut self) {
        self.inner.fill(0);
        std::hint::black_box(&self.inner);
    }
}

impl fmt::Debug for SecretValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SecretValue([REDACTED, {} bytes])", self.inner.len())
    }
}

/// Stored metadata accompanying an encrypted secret slot.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SecretMetadata {
    pub id: SecretSlotId,
    pub created_at: u64,
    pub updated_at: u64,
    pub labels: BTreeMap<String, String>,
}

/// Errors returned by slot-path-bound secret sealing and storage operations.
#[derive(Debug)]
pub enum SecretSealError {
    InvalidSlotId(String),
    EntropyUnavailable(String),
    MalformedEnvelope(&'static str),
    AuthenticationFailed,
    Io(std::io::Error),
    Serialization(String),
}

impl fmt::Display for SecretSealError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSlotId(m) => write!(f, "invalid secret slot id: {m}"),
            Self::EntropyUnavailable(m) => write!(f, "OS CSPRNG unavailable: {m}"),
            Self::MalformedEnvelope(m) => write!(f, "malformed secret envelope: {m}"),
            Self::AuthenticationFailed => {
                write!(f, "AEAD authentication failed (tampered ciphertext, wrong key, or wrong slot AAD)")
            }
            Self::Io(e) => write!(f, "secret store I/O error: {e}"),
            Self::Serialization(m) => write!(f, "secret metadata serialization error: {m}"),
        }
    }
}

impl std::error::Error for SecretSealError {}

impl From<std::io::Error> for SecretSealError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

// =========================================================================
// Pure-Rust RFC 8439 `ChaCha20-Poly1305` IETF AEAD
// =========================================================================

#[inline]
fn quarter_round(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    state[a] = state[a].wrapping_add(state[b]);
    state[d] ^= state[a];
    state[d] = state[d].rotate_left(16);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] ^= state[c];
    state[b] = state[b].rotate_left(12);

    state[a] = state[a].wrapping_add(state[b]);
    state[d] ^= state[a];
    state[d] = state[d].rotate_left(8);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] ^= state[c];
    state[b] = state[b].rotate_left(7);
}

fn chacha20_block(key: &[u8; 32], counter: u32, nonce: &[u8; 12]) -> [u8; 64] {
    let mut initial = [0u32; 16];
    initial[0] = 0x6170_7865;
    initial[1] = 0x3320_646e;
    initial[2] = 0x7962_2d32;
    initial[3] = 0x6b20_6574;
    for i in 0..8 {
        initial[4 + i] = u32::from_le_bytes([
            key[4 * i],
            key[4 * i + 1],
            key[4 * i + 2],
            key[4 * i + 3],
        ]);
    }
    initial[12] = counter;
    initial[13] = u32::from_le_bytes([nonce[0], nonce[1], nonce[2], nonce[3]]);
    initial[14] = u32::from_le_bytes([nonce[4], nonce[5], nonce[6], nonce[7]]);
    initial[15] = u32::from_le_bytes([nonce[8], nonce[9], nonce[10], nonce[11]]);

    let mut working = initial;
    for _ in 0..10 {
        quarter_round(&mut working, 0, 4, 8, 12);
        quarter_round(&mut working, 1, 5, 9, 13);
        quarter_round(&mut working, 2, 6, 10, 14);
        quarter_round(&mut working, 3, 7, 11, 15);

        quarter_round(&mut working, 0, 5, 10, 15);
        quarter_round(&mut working, 1, 6, 11, 12);
        quarter_round(&mut working, 2, 7, 8, 13);
        quarter_round(&mut working, 3, 4, 9, 14);
    }

    let mut out = [0u8; 64];
    for i in 0..16 {
        let word = working[i].wrapping_add(initial[i]);
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_le_bytes());
    }
    out
}

fn chacha20_xor(key: &[u8; 32], initial_counter: u32, nonce: &[u8; 12], data: &mut [u8]) {
    for (blk_idx, chunk) in data.chunks_mut(64).enumerate() {
        let ctr = initial_counter.wrapping_add(blk_idx as u32);
        let mut ks = chacha20_block(key, ctr, nonce);
        for (b, k) in chunk.iter_mut().zip(ks.iter()) {
            *b ^= *k;
        }
        ks.fill(0);
        std::hint::black_box(&ks);
    }
}

/// Constant-time 5-limb radix-$2^{26}$ Poly1305 authenticator (`mod 2^130 - 5`, RFC 8439 §2.5).
fn poly1305_mac(otk: &[u8; 32], msg: &[u8]) -> [u8; 16] {
    const MASK26: u64 = (1 << 26) - 1;
    let mut r_bytes = [0u8; 16];
    r_bytes.copy_from_slice(&otk[0..16]);
    // Clamp r per RFC 8439 §2.5
    r_bytes[3] &= 15;
    r_bytes[7] &= 15;
    r_bytes[11] &= 15;
    r_bytes[15] &= 15;
    r_bytes[4] &= 252;
    r_bytes[8] &= 252;
    r_bytes[12] &= 252;

    let r_u128 = u128::from_le_bytes(r_bytes);
    let r0 = (r_u128 as u64) & MASK26;
    let r1 = ((r_u128 >> 26) as u64) & MASK26;
    let r2 = ((r_u128 >> 52) as u64) & MASK26;
    let r3 = ((r_u128 >> 78) as u64) & MASK26;
    let r4 = ((r_u128 >> 104) as u64) & MASK26;

    let s1 = r1 * 5;
    let s2 = r2 * 5;
    let s3 = r3 * 5;
    let s4 = r4 * 5;

    let mut h0 = 0u64;
    let mut h1 = 0u64;
    let mut h2 = 0u64;
    let mut h3 = 0u64;
    let mut h4 = 0u64;

    for chunk in msg.chunks(16) {
        let mut blk = [0u8; 17];
        blk[..chunk.len()].copy_from_slice(chunk);
        blk[chunk.len()] = 1; // high bit `2^(8 * chunk.len())`

        let lo = u128::from_le_bytes([
            blk[0], blk[1], blk[2], blk[3], blk[4], blk[5], blk[6], blk[7], blk[8], blk[9],
            blk[10], blk[11], blk[12], blk[13], blk[14], blk[15],
        ]);
        let hi_bit = u64::from(blk[16]);

        h0 += (lo as u64) & MASK26;
        h1 += ((lo >> 26) as u64) & MASK26;
        h2 += ((lo >> 52) as u64) & MASK26;
        h3 += ((lo >> 78) as u64) & MASK26;
        h4 += (((lo >> 104) as u64) & ((1 << 24) - 1)) | (hi_bit << 24);

        let d0 = (h0 as u128) * (r0 as u128)
            + (h1 as u128) * (s4 as u128)
            + (h2 as u128) * (s3 as u128)
            + (h3 as u128) * (s2 as u128)
            + (h4 as u128) * (s1 as u128);
        let d1 = (h0 as u128) * (r1 as u128)
            + (h1 as u128) * (r0 as u128)
            + (h2 as u128) * (s4 as u128)
            + (h3 as u128) * (s3 as u128)
            + (h4 as u128) * (s2 as u128);
        let d2 = (h0 as u128) * (r2 as u128)
            + (h1 as u128) * (r1 as u128)
            + (h2 as u128) * (r0 as u128)
            + (h3 as u128) * (s4 as u128)
            + (h4 as u128) * (s3 as u128);
        let d3 = (h0 as u128) * (r3 as u128)
            + (h1 as u128) * (r2 as u128)
            + (h2 as u128) * (r1 as u128)
            + (h3 as u128) * (r0 as u128)
            + (h4 as u128) * (s4 as u128);
        let d4 = (h0 as u128) * (r4 as u128)
            + (h1 as u128) * (r3 as u128)
            + (h2 as u128) * (r2 as u128)
            + (h3 as u128) * (r1 as u128)
            + (h4 as u128) * (r0 as u128);

        let mut c: u64;
        c = (d0 >> 26) as u64;
        h0 = (d0 as u64) & MASK26;
        let d1 = d1 + u128::from(c);
        c = (d1 >> 26) as u64;
        h1 = (d1 as u64) & MASK26;
        let d2 = d2 + u128::from(c);
        c = (d2 >> 26) as u64;
        h2 = (d2 as u64) & MASK26;
        let d3 = d3 + u128::from(c);
        c = (d3 >> 26) as u64;
        h3 = (d3 as u64) & MASK26;
        let d4 = d4 + u128::from(c);
        c = (d4 >> 26) as u64;
        h4 = (d4 as u64) & MASK26;
        h0 += c * 5;
        c = h0 >> 26;
        h0 &= MASK26;
        h1 += c;
    }

    // Final constant-time reduction mod `2^130 - 5`
    let mut c = h1 >> 26;
    h1 &= MASK26;
    h2 += c;
    c = h2 >> 26;
    h2 &= MASK26;
    h3 += c;
    c = h3 >> 26;
    h3 &= MASK26;
    h4 += c;
    c = h4 >> 26;
    h4 &= MASK26;
    h0 += c * 5;
    c = h0 >> 26;
    h0 &= MASK26;
    h1 += c;

    // Compute g = h + 5; if g4 >= 2^26, select g, else h
    let mut g0 = h0 + 5;
    c = g0 >> 26;
    g0 &= MASK26;
    let mut g1 = h1 + c;
    c = g1 >> 26;
    g1 &= MASK26;
    let mut g2 = h2 + c;
    c = g2 >> 26;
    g2 &= MASK26;
    let mut g3 = h3 + c;
    c = g3 >> 26;
    g3 &= MASK26;
    let g4 = h4.wrapping_add(c).wrapping_sub(1 << 26);

    // `g4 >> 63 == 0` iff `h + 5 >= 2^130` (`mask = u64::MAX`), else `0`
    let mask_keep_h = (g4 >> 63).wrapping_neg();
    let mask_take_g = !mask_keep_h;
    h0 = (h0 & mask_keep_h) | (g0 & mask_take_g);
    h1 = (h1 & mask_keep_h) | (g1 & mask_take_g);
    h2 = (h2 & mask_keep_h) | (g2 & mask_take_g);
    h3 = (h3 & mask_keep_h) | (g3 & mask_take_g);
    h4 = (h4 & mask_keep_h) | ((g4 & MASK26) & mask_take_g);

    let acc_u128 = u128::from(h0)
        | (u128::from(h1) << 26)
        | (u128::from(h2) << 52)
        | (u128::from(h3) << 78)
        | (u128::from(h4) << 104);

    let mut s_bytes = [0u8; 16];
    s_bytes.copy_from_slice(&otk[16..32]);
    let pad_s = u128::from_le_bytes(s_bytes);
    acc_u128.wrapping_add(pad_s).to_le_bytes()
}

fn poly1305_aead_input(aad: &[u8], ct: &[u8]) -> Vec<u8> {
    let aad_pad = (16 - (aad.len() % 16)) % 16;
    let ct_pad = (16 - (ct.len() % 16)) % 16;
    let mut mac_data = Vec::with_capacity(aad.len() + aad_pad + ct.len() + ct_pad + 16);
    mac_data.extend_from_slice(aad);
    mac_data.resize(mac_data.len() + aad_pad, 0);
    mac_data.extend_from_slice(ct);
    mac_data.resize(mac_data.len() + ct_pad, 0);
    mac_data.extend_from_slice(&(aad.len() as u64).to_le_bytes());
    mac_data.extend_from_slice(&(ct.len() as u64).to_le_bytes());
    mac_data
}

/// Pure-Rust RFC 8439 §2.8 IETF `ChaCha20-Poly1305` seal returning `ciphertext || 16B tag`.
pub fn chacha20_poly1305_seal(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    plaintext: &[u8],
) -> Vec<u8> {
    let mut block0 = chacha20_block(key, 0, nonce);
    let mut otk = [0u8; 32];
    otk.copy_from_slice(&block0[0..32]);
    block0.fill(0);
    std::hint::black_box(&block0);

    let mut ct = plaintext.to_vec();
    chacha20_xor(key, 1, nonce, &mut ct);

    let mac_input = poly1305_aead_input(aad, &ct);
    let tag = poly1305_mac(&otk, &mac_input);
    otk.fill(0);
    std::hint::black_box(&otk);

    let mut out = Vec::with_capacity(ct.len() + TAG_LEN);
    out.extend_from_slice(&ct);
    out.extend_from_slice(&tag);
    out
}

/// Pure-Rust RFC 8439 §2.8 IETF `ChaCha20-Poly1305` open verifying the 16-byte tag in constant time
/// BEFORE decrypting.
pub fn chacha20_poly1305_open(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ciphertext_and_tag: &[u8],
) -> Result<Vec<u8>, SecretSealError> {
    if ciphertext_and_tag.len() < TAG_LEN {
        return Err(SecretSealError::MalformedEnvelope("ciphertext shorter than Poly1305 tag"));
    }
    let (ct, claimed_tag) = ciphertext_and_tag.split_at(ciphertext_and_tag.len() - TAG_LEN);

    let mut block0 = chacha20_block(key, 0, nonce);
    let mut otk = [0u8; 32];
    otk.copy_from_slice(&block0[0..32]);
    block0.fill(0);
    std::hint::black_box(&block0);

    let mac_input = poly1305_aead_input(aad, ct);
    let expected_tag = poly1305_mac(&otk, &mac_input);
    otk.fill(0);
    std::hint::black_box(&otk);

    let mut diff = 0u8;
    for (&a, &b) in claimed_tag.iter().zip(expected_tag.iter()) {
        diff |= a ^ b;
    }
    if std::hint::black_box(diff) != 0 {
        return Err(SecretSealError::AuthenticationFailed);
    }

    let mut pt = ct.to_vec();
    chacha20_xor(key, 1, nonce, &mut pt);
    Ok(pt)
}

fn derive_envelope_subkey(master_key: &[u8; 32], salt: &[u8; SALT_LEN]) -> [u8; 32] {
    let mut preimage = [0u8; 32 + SALT_LEN];
    preimage[..32].copy_from_slice(master_key);
    preimage[32..].copy_from_slice(salt);
    let subkey = cshake256_32(b"obend.v0.secret_seal.subkey.v1", &preimage);
    preimage.fill(0);
    std::hint::black_box(&preimage);
    subkey
}

fn fill_os_random(dst: &mut [u8]) -> Result<(), SecretSealError> {
    let mut f = File::open("/dev/urandom")
        .map_err(|e| SecretSealError::EntropyUnavailable(format!("/dev/urandom open: {e}")))?;
    f.read_exact(dst)
        .map_err(|e| SecretSealError::EntropyUnavailable(format!("/dev/urandom read: {e}")))
}

/// Seal `plaintext` for `slot` (`(namespace, key)` + `context_aad` injectively bound into AEAD AAD).
pub fn seal_secret_for_slot(
    master_key: &[u8; 32],
    slot: &SecretSlotId,
    context_aad: &[u8],
    plaintext: &[u8],
) -> Result<Vec<u8>, SecretSealError> {
    slot.validate()?;
    let mut entropy = [0u8; SALT_LEN + NONCE_LEN];
    fill_os_random(&mut entropy)?;
    let mut salt = [0u8; SALT_LEN];
    let mut nonce = [0u8; NONCE_LEN];
    salt.copy_from_slice(&entropy[..SALT_LEN]);
    nonce.copy_from_slice(&entropy[SALT_LEN..]);

    let mut subkey = derive_envelope_subkey(master_key, &salt);
    let aad = slot.canonical_aad(context_aad);
    let ct_and_tag = chacha20_poly1305_seal(&subkey, &nonce, &aad, plaintext);
    subkey.fill(0);
    std::hint::black_box(&subkey);

    let mut out = Vec::with_capacity(HEADER_LEN + ct_and_tag.len());
    out.extend_from_slice(SECRET_ENVELOPE_MAGIC);
    out.extend_from_slice(&salt);
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&ct_and_tag);
    Ok(out)
}

/// Unseal an `"OBS1"` envelope strictly under `slot` (`(namespace, key)`) and `context_aad`.
/// Attempting to unseal under ANY other `(namespace, key)` or `context_aad` fails closed with
/// [`SecretSealError::AuthenticationFailed`].
pub fn unseal_secret_for_slot(
    master_key: &[u8; 32],
    slot: &SecretSlotId,
    context_aad: &[u8],
    envelope: &[u8],
) -> Result<SecretValue, SecretSealError> {
    slot.validate()?;
    if envelope.len() < HEADER_LEN + TAG_LEN {
        return Err(SecretSealError::MalformedEnvelope("envelope truncated"));
    }
    if &envelope[..4] != SECRET_ENVELOPE_MAGIC {
        return Err(SecretSealError::MalformedEnvelope("bad OBS1 magic"));
    }
    let mut salt = [0u8; SALT_LEN];
    let mut nonce = [0u8; NONCE_LEN];
    salt.copy_from_slice(&envelope[4..4 + SALT_LEN]);
    nonce.copy_from_slice(&envelope[4 + SALT_LEN..HEADER_LEN]);

    let mut subkey = derive_envelope_subkey(master_key, &salt);
    let aad = slot.canonical_aad(context_aad);
    let pt_res = chacha20_poly1305_open(&subkey, &nonce, &aad, &envelope[HEADER_LEN..]);
    subkey.fill(0);
    std::hint::black_box(&subkey);
    pt_res.map(SecretValue::new)
}

// =========================================================================
// `0600` Atomic Filesystem Secret Store (`SlotBoundSecretStore`)
// =========================================================================

fn sanitize_segment(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(name.len());
    let mut enc = [0u8; 4];
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
            out.push(c);
        } else {
            for &b in c.encode_utf8(&mut enc).as_bytes() {
                out.push('%');
                out.push(HEX[(b >> 4) as usize] as char);
                out.push(HEX[(b & 0x0f) as usize] as char);
            }
        }
    }
    out
}

fn now_unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// Encrypted file-backed secret store binding `(namespace, key)` into every slot's AEAD AAD.
pub struct SlotBoundSecretStore {
    base_dir: PathBuf,
    master_key: [u8; 32],
    store_context_aad: Vec<u8>,
}

impl Drop for SlotBoundSecretStore {
    fn drop(&mut self) {
        self.master_key.fill(0);
        std::hint::black_box(&self.master_key);
    }
}

impl SlotBoundSecretStore {
    pub fn new(base_dir: impl Into<PathBuf>, master_key: [u8; 32]) -> Self {
        Self {
            base_dir: base_dir.into(),
            master_key,
            store_context_aad: Vec::new(),
        }
    }

    pub fn with_context_aad(mut self, context_aad: impl Into<Vec<u8>>) -> Self {
        self.store_context_aad = context_aad.into();
        self
    }

    pub fn base_dir(&self) -> &Path {
        &self.base_dir
    }

    pub fn secret_file_path(&self, id: &SecretSlotId) -> PathBuf {
        self.base_dir
            .join(sanitize_segment(&id.namespace))
            .join(format!("{}.enc", sanitize_segment(&id.key)))
    }

    fn meta_file_path(&self, id: &SecretSlotId) -> PathBuf {
        self.base_dir
            .join(sanitize_segment(&id.namespace))
            .join(format!("{}.meta", sanitize_segment(&id.key)))
    }

    fn atomic_write_0600(&self, target: &Path, payload: &[u8]) -> Result<(), SecretSealError> {
        let dir = target.parent().unwrap_or(&self.base_dir);
        fs::create_dir_all(dir)?;
        fs::set_permissions(dir, fs::Permissions::from_mode(0o700))?;

        let seq = SECRET_TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let file_name = target
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("secret");
        let tmp_path = dir.join(format!(".{file_name}.tmp.{pid}.{seq}"));

        let mut tmp = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&tmp_path)?;

        if let Err(e) = tmp.write_all(payload).and_then(|()| tmp.sync_all()) {
            let _ = fs::remove_file(&tmp_path);
            return Err(SecretSealError::Io(e));
        }
        drop(tmp);
        if let Err(e) = fs::rename(&tmp_path, target) {
            let _ = fs::remove_file(&tmp_path);
            return Err(SecretSealError::Io(e));
        }
        File::open(dir)?.sync_all()?;
        Ok(())
    }

    pub fn put(&self, id: &SecretSlotId, plaintext: &[u8]) -> Result<(), SecretSealError> {
        id.validate()?;
        let envelope =
            seal_secret_for_slot(&self.master_key, id, &self.store_context_aad, plaintext)?;
        self.atomic_write_0600(&self.secret_file_path(id), &envelope)?;

        let now = now_unix_secs();
        let meta_path = self.meta_file_path(id);
        let meta = if meta_path.exists() {
            let raw = fs::read_to_string(&meta_path)?;
            let mut m: SecretMetadata = serde_json::from_str(&raw)
                .map_err(|e| SecretSealError::Serialization(e.to_string()))?;
            m.updated_at = now;
            m
        } else {
            SecretMetadata {
                id: id.clone(),
                created_at: now,
                updated_at: now,
                labels: BTreeMap::new(),
            }
        };
        let meta_bytes = serde_json::to_vec(&meta)
            .map_err(|e| SecretSealError::Serialization(e.to_string()))?;
        self.atomic_write_0600(&meta_path, &meta_bytes)
    }

    pub fn get(&self, id: &SecretSlotId) -> Result<Option<SecretValue>, SecretSealError> {
        id.validate()?;
        let path = self.secret_file_path(id);
        let mut f = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&path)
        {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(SecretSealError::Io(e)),
        };
        let mut envelope = Vec::new();
        f.read_to_end(&mut envelope)?;
        let secret =
            unseal_secret_for_slot(&self.master_key, id, &self.store_context_aad, &envelope)?;
        Ok(Some(secret))
    }

    pub fn delete(&self, id: &SecretSlotId) -> Result<bool, SecretSealError> {
        id.validate()?;
        let enc = self.secret_file_path(id);
        let meta = self.meta_file_path(id);
        let existed = enc.exists();
        if enc.exists() {
            fs::remove_file(&enc)?;
        }
        if meta.exists() {
            fs::remove_file(&meta)?;
        }
        Ok(existed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc8439_section_2_8_2_official_aead_vector() {
        let key: [u8; 32] = [
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ];
        let nonce: [u8; 12] = [
            0x07, 0x00, 0x00, 0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        ];
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";

        let expected_ct: [u8; 114] = [
            0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb, 0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef,
            0x7e, 0xc2, 0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe, 0xa9, 0xe2, 0xb5, 0xa7,
            0x36, 0xee, 0x62, 0xd6, 0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12, 0x82, 0xfa,
            0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b, 0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29,
            0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36, 0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77,
            0x8b, 0x8c, 0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58, 0xfa, 0xb3, 0x24, 0xe4,
            0xfa, 0xd6, 0x75, 0x94, 0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc, 0x3f, 0xf4,
            0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d, 0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
            0x61, 0x16,
        ];
        let expected_tag: [u8; 16] = [
            0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a, 0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60,
            0x06, 0x91,
        ];

        let sealed = chacha20_poly1305_seal(&key, &nonce, &aad, plaintext);
        assert_eq!(&sealed[..114], &expected_ct[..]);
        assert_eq!(&sealed[114..], &expected_tag[..]);

        let opened = chacha20_poly1305_open(&key, &nonce, &aad, &sealed).unwrap();
        assert_eq!(opened.as_slice(), &plaintext[..]);

        // Any 1-bit flip in AAD fails closed!
        let mut bad_aad = aad;
        bad_aad[0] ^= 1;
        assert!(matches!(
            chacha20_poly1305_open(&key, &nonce, &bad_aad, &sealed),
            Err(SecretSealError::AuthenticationFailed)
        ));
    }

    #[test]
    fn wrong_slot_or_spliced_file_unseal_is_refused() {
        let dir = std::env::temp_dir().join(format!(
            "obend_secret_seal_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let store = SlotBoundSecretStore::new(&dir, [0x42u8; 32]);

        let slot_a = SecretSlotId::new("grain-auth", "stripe_secret");
        let slot_b = SecretSlotId::new("grain-auth", "webhook_hmac");
        store.put(&slot_a, b"sk_live_top_secret").unwrap();
        store.put(&slot_b, b"whsec_low_priv").unwrap();

        assert_eq!(
            store.get(&slot_a).unwrap().unwrap().as_bytes(),
            b"sk_live_top_secret"
        );
        assert_eq!(
            fs::metadata(store.secret_file_path(&slot_a))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );

        // Attack 1: Copy `slot_a.enc` onto `slot_b.enc` under the SAME master key!
        fs::copy(
            store.secret_file_path(&slot_a),
            store.secret_file_path(&slot_b),
        )
        .unwrap();
        assert!(
            matches!(store.get(&slot_b), Err(SecretSealError::AuthenticationFailed)),
            "swapping ciphertext across slots MUST fail AEAD slot-path AAD authentication!"
        );

        // Attack 2: Boundary-shift `("ab", "c")` vs `("a", "bc")`
        let env = seal_secret_for_slot(&[0x42u8; 32], &SecretSlotId::new("ab", "c"), b"ctx", b"v")
            .unwrap();
        assert!(matches!(
            unseal_secret_for_slot(&[0x42u8; 32], &SecretSlotId::new("a", "bc"), b"ctx", &env),
            Err(SecretSealError::AuthenticationFailed)
        ));

        let _ = fs::remove_dir_all(&dir);
    }
}
