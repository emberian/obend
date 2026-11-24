#![forbid(unsafe_code)]
//! Pure-Rust RFC 8439 `ChaCha20-Poly1305` IETF AEAD (`0` external crates, `#![forbid(unsafe_code)]`).
//!
//! Implements:
//! - RFC 8439 §2.1–2.4 20-round `ChaCha20` stream cipher (`256`-bit key, `32`-bit block counter,
//!   `96`-bit IETF nonce),
//! - RFC 8439 §2.5 `Poly1305` one-time authenticator over $\mathbb{F}_{2^{130}-5}$ using
//!   constant-time 5×26-bit limb arithmetic (`0` branches on secret key/message bits),
//! - RFC 8439 §2.8 `ChaCha20-Poly1305` AEAD seal & constant-time tag-first open (fail-closed:
//!   never releases unauthenticated plaintext on MAC mismatch).

use obend_primitives::ct::ct_eq;

/// Length in bytes of a ChaCha20-Poly1305 key (256 bits).
pub const CHACHA20_KEY_LEN: usize = 32;
/// Length in bytes of an IETF ChaCha20-Poly1305 nonce (96 bits).
pub const CHACHA20_NONCE_LEN: usize = 12;
/// Length in bytes of a Poly1305 authentication tag (128 bits).
pub const POLY1305_TAG_LEN: usize = 16;

const CHACHA20_CONSTANTS: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];
const MASK_26: u64 = 0x03ff_ffff;

/// Errors returned by RFC 8439 `ChaCha20-Poly1305` operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AeadError {
    /// Input exceeds the 32-bit IETF ChaCha20 block counter limit (`(2^32 - 1) * 64` bytes).
    CounterOverflow,
    /// Combined `ciphertext || tag` buffer is shorter than [`POLY1305_TAG_LEN`].
    CiphertextTooShort,
    /// Poly1305 authentication tag verification failed.
    AuthenticationFailed,
}

#[inline]
fn quarter_round(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(16);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(12);

    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(8);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(7);
}

/// RFC 8439 §2.3 20-round IETF ChaCha20 block function producing 64 keystream bytes.
pub fn chacha20_block(
    key: &[u8; CHACHA20_KEY_LEN],
    counter: u32,
    nonce: &[u8; CHACHA20_NONCE_LEN],
) -> [u8; 64] {
    let mut initial = [0u32; 16];
    initial[0] = CHACHA20_CONSTANTS[0];
    initial[1] = CHACHA20_CONSTANTS[1];
    initial[2] = CHACHA20_CONSTANTS[2];
    initial[3] = CHACHA20_CONSTANTS[3];
    for i in 0..8 {
        let off = 4 * i;
        initial[4 + i] = u32::from_le_bytes([key[off], key[off + 1], key[off + 2], key[off + 3]]);
    }
    initial[12] = counter;
    for i in 0..3 {
        let off = 4 * i;
        initial[13 + i] =
            u32::from_le_bytes([nonce[off], nonce[off + 1], nonce[off + 2], nonce[off + 3]]);
    }

    let mut working = initial;
    for _ in 0..10 {
        // Column rounds.
        quarter_round(&mut working, 0, 4, 8, 12);
        quarter_round(&mut working, 1, 5, 9, 13);
        quarter_round(&mut working, 2, 6, 10, 14);
        quarter_round(&mut working, 3, 7, 11, 15);
        // Diagonal rounds.
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

/// RFC 8439 §2.4 IETF ChaCha20 XOR stream encryption/decryption starting at `initial_counter`.
pub fn chacha20_xor(
    key: &[u8; CHACHA20_KEY_LEN],
    initial_counter: u32,
    nonce: &[u8; CHACHA20_NONCE_LEN],
    input: &[u8],
) -> Result<Vec<u8>, AeadError> {
    let mut out = Vec::with_capacity(input.len());
    for (block_idx, chunk) in input.chunks(64).enumerate() {
        let idx_u32 = u32::try_from(block_idx).map_err(|_| AeadError::CounterOverflow)?;
        let counter = initial_counter
            .checked_add(idx_u32)
            .ok_or(AeadError::CounterOverflow)?;
        let ks = chacha20_block(key, counter, nonce);
        for (b, k) in chunk.iter().zip(ks.iter()) {
            out.push(b ^ k);
        }
    }
    Ok(out)
}

/// Streaming constant-time RFC 8439 §2.5 `Poly1305` authenticator over $\mathbb{F}_{2^{130}-5}$.
pub struct Poly1305 {
    r: [u64; 5],
    s_pre: [u64; 4],
    pad_s: u128,
    h: [u64; 5],
    buf: [u8; 16],
    buf_len: usize,
}

impl Poly1305 {
    /// Initialize a one-time Poly1305 state from a 32-byte key (`r || s`), clamping `r` per RFC 8439 §2.5.
    pub fn new(otk: &[u8; 32]) -> Self {
        let mut r_bytes = [0u8; 16];
        r_bytes.copy_from_slice(&otk[0..16]);
        r_bytes[3] &= 15;
        r_bytes[7] &= 15;
        r_bytes[11] &= 15;
        r_bytes[15] &= 15;
        r_bytes[4] &= 252;
        r_bytes[8] &= 252;
        r_bytes[12] &= 252;

        let r_u128 = u128::from_le_bytes(r_bytes);
        let r0 = (r_u128 & u128::from(MASK_26)) as u64;
        let r1 = ((r_u128 >> 26) & u128::from(MASK_26)) as u64;
        let r2 = ((r_u128 >> 52) & u128::from(MASK_26)) as u64;
        let r3 = ((r_u128 >> 78) & u128::from(MASK_26)) as u64;
        let r4 = ((r_u128 >> 104) & u128::from(MASK_26)) as u64;

        let mut s_bytes = [0u8; 16];
        s_bytes.copy_from_slice(&otk[16..32]);
        let pad_s = u128::from_le_bytes(s_bytes);

        Self {
            r: [r0, r1, r2, r3, r4],
            s_pre: [r1 * 5, r2 * 5, r3 * 5, r4 * 5],
            pad_s,
            h: [0u64; 5],
            buf: [0u8; 16],
            buf_len: 0,
        }
    }

    fn process_block(&mut self, block: &[u8]) {
        debug_assert!(!block.is_empty() && block.len() <= 16);
        let mut padded = [0u8; 17];
        padded[..block.len()].copy_from_slice(block);
        padded[block.len()] = 1;

        let mut lo_bytes = [0u8; 16];
        lo_bytes.copy_from_slice(&padded[0..16]);
        let lo = u128::from_le_bytes(lo_bytes);
        let hi = u64::from(padded[16]);

        let m0 = (lo & u128::from(MASK_26)) as u64;
        let m1 = ((lo >> 26) & u128::from(MASK_26)) as u64;
        let m2 = ((lo >> 52) & u128::from(MASK_26)) as u64;
        let m3 = ((lo >> 78) & u128::from(MASK_26)) as u64;
        let m4 = ((lo >> 104) as u64) | (hi << 24);

        let h0 = u128::from(self.h[0] + m0);
        let h1 = u128::from(self.h[1] + m1);
        let h2 = u128::from(self.h[2] + m2);
        let h3 = u128::from(self.h[3] + m3);
        let h4 = u128::from(self.h[4] + m4);

        let r0 = u128::from(self.r[0]);
        let r1 = u128::from(self.r[1]);
        let r2 = u128::from(self.r[2]);
        let r3 = u128::from(self.r[3]);
        let r4 = u128::from(self.r[4]);

        let s1 = u128::from(self.s_pre[0]);
        let s2 = u128::from(self.s_pre[1]);
        let s3 = u128::from(self.s_pre[2]);
        let s4 = u128::from(self.s_pre[3]);

        let d0 = h0 * r0 + h1 * s4 + h2 * s3 + h3 * s2 + h4 * s1;
        let mut d1 = h0 * r1 + h1 * r0 + h2 * s4 + h3 * s3 + h4 * s2;
        let mut d2 = h0 * r2 + h1 * r1 + h2 * r0 + h3 * s4 + h4 * s3;
        let mut d3 = h0 * r3 + h1 * r2 + h2 * r1 + h3 * r0 + h4 * s4;
        let mut d4 = h0 * r4 + h1 * r3 + h2 * r2 + h3 * r1 + h4 * r0;

        let mut c = (d0 >> 26) as u64;
        let mut nh0 = (d0 as u64) & MASK_26;
        d1 += u128::from(c);

        c = (d1 >> 26) as u64;
        let mut nh1 = (d1 as u64) & MASK_26;
        d2 += u128::from(c);

        c = (d2 >> 26) as u64;
        let nh2 = (d2 as u64) & MASK_26;
        d3 += u128::from(c);

        c = (d3 >> 26) as u64;
        let nh3 = (d3 as u64) & MASK_26;
        d4 += u128::from(c);

        c = (d4 >> 26) as u64;
        let nh4 = (d4 as u64) & MASK_26;
        nh0 += c * 5;

        c = nh0 >> 26;
        nh0 &= MASK_26;
        nh1 += c;

        self.h = [nh0, nh1, nh2, nh3, nh4];
    }

    /// Absorb arbitrary bytes into the Poly1305 state.
    pub fn update(&mut self, mut data: &[u8]) {
        if self.buf_len > 0 {
            let take = (16 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 16 {
                let block = self.buf;
                self.buf_len = 0;
                self.process_block(&block);
            }
        }
        while data.len() >= 16 {
            self.process_block(&data[..16]);
            data = &data[16..];
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.buf_len = data.len();
        }
    }

    fn pad16(&mut self, len: usize) {
        let rem = len % 16;
        if rem != 0 {
            let zeros = [0u8; 16];
            self.update(&zeros[..16 - rem]);
        }
    }

    /// Finalize the Poly1305 state and return the 16-byte tag in constant time.
    pub fn finalize(mut self) -> [u8; POLY1305_TAG_LEN] {
        if self.buf_len > 0 {
            let tail_len = self.buf_len;
            let tail = self.buf;
            self.buf_len = 0;
            self.process_block(&tail[..tail_len]);
        }

        // Complete carry chain so 0 <= h < 2 * (2^130 - 5).
        let mut h0 = self.h[0];
        let mut h1 = self.h[1];
        let mut h2 = self.h[2];
        let mut h3 = self.h[3];
        let mut h4 = self.h[4];

        let mut c = h1 >> 26;
        h1 &= MASK_26;
        h2 += c;
        c = h2 >> 26;
        h2 &= MASK_26;
        h3 += c;
        c = h3 >> 26;
        h3 &= MASK_26;
        h4 += c;
        c = h4 >> 26;
        h4 &= MASK_26;
        h0 += c * 5;
        c = h0 >> 26;
        h0 &= MASK_26;
        h1 += c;

        // Constant-time subtraction of p = 2^130 - 5 via g = h + 5 - 2^130.
        let mut g0 = h0 + 5;
        c = g0 >> 26;
        g0 &= MASK_26;
        let mut g1 = h1 + c;
        c = g1 >> 26;
        g1 &= MASK_26;
        let mut g2 = h2 + c;
        c = g2 >> 26;
        g2 &= MASK_26;
        let mut g3 = h3 + c;
        c = g3 >> 26;
        g3 &= MASK_26;
        let g4 = h4.wrapping_add(c).wrapping_sub(1 << 26);

        // If g4 underflowed, bit 63 is 1 -> keep h; otherwise h >= 2^130 - 5 -> select g.
        let keep_h = (g4 >> 63).wrapping_neg();
        let keep_g = !keep_h;

        h0 = (h0 & keep_h) | (g0 & keep_g);
        h1 = (h1 & keep_h) | (g1 & keep_g);
        h2 = (h2 & keep_h) | (g2 & keep_g);
        h3 = (h3 & keep_h) | (g3 & keep_g);
        h4 = (h4 & keep_h) | (g4 & keep_g);

        let h_mod_2_128 = u128::from(h0)
            | (u128::from(h1) << 26)
            | (u128::from(h2) << 52)
            | (u128::from(h3) << 78)
            | (u128::from(h4 & 0x00ff_ffff) << 104);

        h_mod_2_128.wrapping_add(self.pad_s).to_le_bytes()
    }
}

/// Evaluate one-shot RFC 8439 §2.5 `Poly1305` MAC over `msg` under one-time key `otk`.
pub fn poly1305_mac(otk: &[u8; 32], msg: &[u8]) -> [u8; POLY1305_TAG_LEN] {
    let mut mac = Poly1305::new(otk);
    mac.update(msg);
    mac.finalize()
}

fn compute_aead_tag(
    key: &[u8; CHACHA20_KEY_LEN],
    nonce: &[u8; CHACHA20_NONCE_LEN],
    aad: &[u8],
    ciphertext: &[u8],
) -> [u8; POLY1305_TAG_LEN] {
    let block0 = chacha20_block(key, 0, nonce);
    let mut otk = [0u8; 32];
    otk.copy_from_slice(&block0[0..32]);

    let mut mac = Poly1305::new(&otk);
    mac.update(aad);
    mac.pad16(aad.len());
    mac.update(ciphertext);
    mac.pad16(ciphertext.len());
    mac.update(&(aad.len() as u64).to_le_bytes());
    mac.update(&(ciphertext.len() as u64).to_le_bytes());
    mac.finalize()
}

/// RFC 8439 §2.8 `ChaCha20-Poly1305` detached AEAD encryption returning `(ciphertext, tag)`.
pub fn chacha20poly1305_seal(
    key: &[u8; CHACHA20_KEY_LEN],
    nonce: &[u8; CHACHA20_NONCE_LEN],
    aad: &[u8],
    plaintext: &[u8],
) -> Result<(Vec<u8>, [u8; POLY1305_TAG_LEN]), AeadError> {
    let ciphertext = chacha20_xor(key, 1, nonce, plaintext)?;
    let tag = compute_aead_tag(key, nonce, aad, &ciphertext);
    Ok((ciphertext, tag))
}

/// RFC 8439 §2.8 `ChaCha20-Poly1305` detached AEAD decryption.
/// Verifies `tag` in constant time (`ct_eq`) before decrypting any ciphertext bytes.
pub fn chacha20poly1305_open(
    key: &[u8; CHACHA20_KEY_LEN],
    nonce: &[u8; CHACHA20_NONCE_LEN],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; POLY1305_TAG_LEN],
) -> Result<Vec<u8>, AeadError> {
    // Check counter bound upfront so oversized ciphertexts fail cleanly.
    let block_count = ciphertext.len().div_ceil(64);
    let last_offset = block_count.saturating_sub(1);
    let idx_u32 = u32::try_from(last_offset).map_err(|_| AeadError::CounterOverflow)?;
    if !ciphertext.is_empty() && 1u32.checked_add(idx_u32).is_none() {
        return Err(AeadError::CounterOverflow);
    }

    let expected_tag = compute_aead_tag(key, nonce, aad, ciphertext);
    if !ct_eq(&expected_tag, tag) {
        return Err(AeadError::AuthenticationFailed);
    }
    chacha20_xor(key, 1, nonce, ciphertext)
}

/// Combined `ChaCha20-Poly1305` seal returning `ciphertext || tag` (`plaintext.len() + 16` bytes).
pub fn chacha20poly1305_seal_combined(
    key: &[u8; CHACHA20_KEY_LEN],
    nonce: &[u8; CHACHA20_NONCE_LEN],
    aad: &[u8],
    plaintext: &[u8],
) -> Result<Vec<u8>, AeadError> {
    let (mut ct, tag) = chacha20poly1305_seal(key, nonce, aad, plaintext)?;
    ct.reserve_exact(POLY1305_TAG_LEN);
    ct.extend_from_slice(&tag);
    Ok(ct)
}

/// Combined `ChaCha20-Poly1305` open over `ciphertext || tag`.
pub fn chacha20poly1305_open_combined(
    key: &[u8; CHACHA20_KEY_LEN],
    nonce: &[u8; CHACHA20_NONCE_LEN],
    aad: &[u8],
    sealed: &[u8],
) -> Result<Vec<u8>, AeadError> {
    if sealed.len() < POLY1305_TAG_LEN {
        return Err(AeadError::CiphertextTooShort);
    }
    let ct_len = sealed.len() - POLY1305_TAG_LEN;
    let mut tag = [0u8; POLY1305_TAG_LEN];
    tag.copy_from_slice(&sealed[ct_len..]);
    chacha20poly1305_open(key, nonce, aad, &sealed[..ct_len], &tag)
}
