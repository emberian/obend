//! Keccak-f[1600], NIST SP 800-185 `cSHAKE256` / `SHAKE256` (matching `Obend.Digest.Cshake256`),
//! and the compile-time typestate `FenziTranscript<Phase>` (`Unbound -> RelationBound -> InstanceBound`).
//!
//! Closing **Fenzi `ePrint 2026/1838`** (delayed circuit-relation binding) and **`F3`/`F5`**
//! (premature challenge squeezing prior to absorbing `(vk_digest, circuit_desc, comm, claimed_sum, point)`):
//! challenge-squeezing methods exist **only** on `FenziTranscript<InstanceBound>`.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::goldilocks::{Goldilocks, GoldilocksExt2};

/// Sponge rate of SHAKE256 / cSHAKE256 in bytes ($1088 / 8 = 136$).
pub const SHAKE256_RATE_BYTES: usize = 136;

/// Number of 64-bit lanes in the SHAKE256 / cSHAKE256 rate ($136 / 8 = 17$).
pub const SHAKE256_RATE_LANES: usize = 17;

/// Standard 24 FIPS 202 Keccak-f[1600] round constants.
pub const KECCAK_ROUND_CONSTANTS: [u64; 24] = [
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

/// FIPS 202 rho rotation offsets indexed by `x + 5 * y`.
const ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Domain customization strings matching `Obend.Crypto.Transcript`.
pub const FS_SEED_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.SEED/v1";
pub const FS_BIND_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.BIND/v1";
pub const FS_INSTANCE_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.INSTANCE/v1";
pub const FS_ABSORB_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.ABSORB/v1";
pub const FS_SQUEEZE_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.SQUEEZE/v1";
pub const FS_RATCHET_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.FS.RATCHET/v1";

pub const DUAL_TRACK1_LABEL: &[u8] = b"DUAL.TRACK1";
pub const DUAL_TRACK2_LABEL: &[u8] = b"DUAL.TRACK2";
pub const DUAL_JOIN_LABEL: &[u8] = b"DUAL.JOIN";

/// Exact 24-round Keccak-f[1600] permutation over 25 little-endian 64-bit lanes.
pub fn keccak_f1600(state: &mut [u64; 25]) {
    // Fixed lane indices avoid debug-mode Range iterator calls and let the
    // compiler resolve lane arithmetic and bounds checks even at opt-level=0.
    macro_rules! lanes5 {
        ($f:ident) => {
            $f!(0);
            $f!(1);
            $f!(2);
            $f!(3);
            $f!(4);
        };
    }
    let mut round = 0;
    while round < 24 {
        // Theta
        let mut c = [0u64; 5];
        macro_rules! parity {
            ($x:expr) => {
                c[$x] = state[$x] ^ state[$x + 5] ^ state[$x + 10]
                    ^ state[$x + 15] ^ state[$x + 20];
            };
        }
        lanes5!(parity);
        macro_rules! theta {
            ($x:expr) => {
                let d = c[($x + 4) % 5] ^ c[($x + 1) % 5].rotate_left(1);
                state[$x] ^= d;
                state[$x + 5] ^= d;
                state[$x + 10] ^= d;
                state[$x + 15] ^= d;
                state[$x + 20] ^= d;
            };
        }
        lanes5!(theta);

        // Rho + Pi
        let mut b = [0u64; 25];
        macro_rules! rho_pi {
            ($x:expr, $y:expr) => {
                b[$y + 5 * ((2 * $x + 3 * $y) % 5)] =
                    state[$x + 5 * $y].rotate_left(ROTATION_OFFSETS[$x + 5 * $y]);
            };
        }
        macro_rules! rho_row {
            ($y:expr) => {
                rho_pi!(0, $y);
                rho_pi!(1, $y);
                rho_pi!(2, $y);
                rho_pi!(3, $y);
                rho_pi!(4, $y);
            };
        }
        lanes5!(rho_row);

        // Chi
        macro_rules! chi {
            ($x:expr, $y:expr) => {
                state[5 * $y + $x] = b[5 * $y + $x]
                    ^ ((!b[5 * $y + (($x + 1) % 5)]) & b[5 * $y + (($x + 2) % 5)]);
            };
        }
        macro_rules! chi_row {
            ($y:expr) => {
                chi!(0, $y);
                chi!(1, $y);
                chi!(2, $y);
                chi!(3, $y);
                chi!(4, $y);
            };
        }
        lanes5!(chi_row);

        // Iota
        state[0] ^= KECCAK_ROUND_CONSTANTS[round];
        round += 1;
    }
}

/// SP 800-185 minimal non-empty big-endian byte representation (`[0]` for `0`).
pub fn nat_bytes_be(mut value: usize) -> Vec<u8> {
    if value == 0 {
        return vec![0u8];
    }
    let mut le = Vec::with_capacity(8);
    while value > 0 {
        le.push((value & 0xFF) as u8);
        value >>= 8;
    }
    le.reverse();
    le
}

/// SP 800-185 `left_encode`, matching `Obend.Digest.Cshake256.leftEncode`.
pub fn sp800_185_left_encode(value: usize) -> Vec<u8> {
    let bytes = nat_bytes_be(value);
    let mut out = Vec::with_capacity(1 + bytes.len());
    out.push(bytes.len() as u8);
    out.extend_from_slice(&bytes);
    out
}

/// SP 800-185 `encode_string`, matching `Obend.Digest.Cshake256.encodeString`.
pub fn sp800_185_encode_string(bytes: &[u8]) -> Vec<u8> {
    let mut out = sp800_185_left_encode(bytes.len().saturating_mul(8));
    out.extend_from_slice(bytes);
    out
}

/// SP 800-185 `bytepad`, matching `Obend.Digest.Cshake256.bytepad`.
pub fn sp800_185_bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
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

/// SP 800-185 cSHAKE256 customization prefix for empty function-name `N = ""` and caller `S`.
pub fn cshake256_customization_prefix(customization: &[u8]) -> Vec<u8> {
    let mut inner = sp800_185_encode_string(&[]);
    inner.extend_from_slice(&sp800_185_encode_string(customization));
    sp800_185_bytepad(&inner, SHAKE256_RATE_BYTES)
}

#[inline]
fn xor_rate_block(state: &mut [u64; 25], block: &[u8; SHAKE256_RATE_BYTES]) {
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

/// Streaming SP 800-185 `cSHAKE256` / `SHAKE256` XOF sponge matching `Obend.Digest.Cshake256`.
#[derive(Clone)]
pub struct Cshake256Xof {
    state: [u64; 25],
    buf: [u8; SHAKE256_RATE_BYTES],
    buf_len: usize,
    suffix: u8,
    squeezing: bool,
    squeeze_offset: usize,
}

impl Drop for Cshake256Xof {
    fn drop(&mut self) {
        self.scrub();
    }
}

impl Cshake256Xof {
    fn scrub(&mut self) {
        self.state.fill(0);
        self.buf.fill(0);
        self.buf_len = 0;
        self.squeeze_offset = 0;
        self.suffix = 0;
        self.squeezing = false;
        core::hint::black_box((&self.state, &self.buf));
    }
}

impl Cshake256Xof {
    /// Initialize `cSHAKE256` with empty function-name `N = ""` and customization `S`.
    /// Per NIST SP 800-185 §3.3, empty `S` falls back identically to `SHAKE256` (`suffix = 0x1f`).
    pub fn new(customization: &[u8]) -> Self {
        let mut xof = Self {
            state: [0u64; 25],
            buf: [0u8; SHAKE256_RATE_BYTES],
            buf_len: 0,
            suffix: if customization.is_empty() { 0x1f } else { 0x04 },
            squeezing: false,
            squeeze_offset: 0,
        };
        if !customization.is_empty() {
            let prefix = cshake256_customization_prefix(customization);
            xof.absorb(&prefix);
        }
        xof
    }

    /// Absorb arbitrary bytes into the sponge prior to squeezing.
    pub fn absorb(&mut self, mut data: &[u8]) {
        assert!(
            !self.squeezing,
            "cannot absorb into Cshake256Xof after squeezing began"
        );
        while !data.is_empty() {
            let space = SHAKE256_RATE_BYTES - self.buf_len;
            let take = space.min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == SHAKE256_RATE_BYTES {
                xor_rate_block(&mut self.state, &self.buf);
                keccak_f1600(&mut self.state);
                self.buf_len = 0;
            }
        }
    }

    fn finalize_to_squeeze(&mut self) {
        if self.squeezing {
            return;
        }
        // Multi-rate padding matching `padForRate` in `Obend/Digest/Cshake256/Spec.lean`
        for b in &mut self.buf[self.buf_len..] {
            *b = 0;
        }
        self.buf[self.buf_len] ^= self.suffix;
        self.buf[SHAKE256_RATE_BYTES - 1] ^= 0x80;
        xor_rate_block(&mut self.state, &self.buf);
        keccak_f1600(&mut self.state);
        self.squeezing = true;
        self.squeeze_offset = 0;
    }

    /// Squeeze arbitrary output bytes from the finalized sponge.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        self.finalize_to_squeeze();
        let mut written = 0usize;
        while written < out.len() {
            if self.squeeze_offset == SHAKE256_RATE_BYTES {
                keccak_f1600(&mut self.state);
                self.squeeze_offset = 0;
            }
            let lane_idx = self.squeeze_offset / 8;
            let byte_in_lane = self.squeeze_offset % 8;
            let b = ((self.state[lane_idx] >> (8 * byte_in_lane)) & 0xFF) as u8;
            out[written] = b;
            written += 1;
            self.squeeze_offset += 1;
        }
    }
}

/// Exact 32-byte `cSHAKE256` evaluation matching `Obend.Digest.Cshake256.cshake256Bytes`
/// and `Obend.Crypto.Transcript.cshake32ByteArray` bit-for-bit.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(customization);
    xof.absorb(input);
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Standard uncustomized 32-byte `SHAKE256` helper.
#[inline]
pub fn shake256_32(input: &[u8]) -> [u8; 32] {
    cshake256_32(&[], input)
}

// ============================================================================
// Self-Delimiting LEB128 Framing (Matching `Obend.Crypto.Transcript`)
// ============================================================================

/// Canonical self-delimiting unsigned LEB128 encoding matching `Obend.Crypto.Transcript.leb128`.
pub fn leb128(mut n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(4);
    loop {
        if n < 128 {
            out.push(n as u8);
            break;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out
}

/// `leb128` for `u64` step counters.
pub fn leb128_u64(mut n: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(5);
    loop {
        if n < 128 {
            out.push(n as u8);
            break;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out
}

/// Length-prefixed byte field `leb128(xs.len()) || xs`.
pub fn encode_list_field(xs: &[u8]) -> Vec<u8> {
    let mut out = leb128(xs.len());
    out.extend_from_slice(xs);
    out
}

/// Injectively framed 3-field payload matching `Obend.Crypto.Transcript.encodeFrame`.
pub fn encode_frame(a: &[u8], b: &[u8], c: &[u8]) -> Vec<u8> {
    let mut out = encode_list_field(a);
    out.extend_from_slice(&encode_list_field(b));
    out.extend_from_slice(&encode_list_field(c));
    out
}

/// Encode a UTF-8 string via LEB128 Unicode scalar values matching `encodeStringCodepoints`.
pub fn encode_string_codepoints(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    for ch in s.chars() {
        out.extend_from_slice(&leb128(ch as usize));
    }
    out
}

// ============================================================================
// Compile-Time Typestate `FenziTranscript<Phase>`
// ============================================================================

mod sealed {
    pub trait Sealed {}
}

/// Sealed marker trait for compile-time Fiat–Shamir transcript phases.
pub trait TranscriptPhase: sealed::Sealed + Clone + Copy {}

/// Initial phase: context seed absorbed, neither circuit relation nor statement instance bound yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unbound;
impl sealed::Sealed for Unbound {}
impl TranscriptPhase for Unbound {}

/// Second phase: `(protocol_id, vk_digest, circuit_desc)` cryptographically bound (`Fenzi 2026/1838`),
/// awaiting `(comm, claimed_sum, point)` instance binding (`F3`/`F5`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationBound;
impl sealed::Sealed for RelationBound {}
impl TranscriptPhase for RelationBound {}

/// Terminal active phase: both materialized circuit relation AND `(comm, claimed_sum, point)`
/// instance are bound; prover messages can be absorbed and 128/256-bit challenges squeezed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstanceBound;
impl sealed::Sealed for InstanceBound {}
impl TranscriptPhase for InstanceBound {}

/// Compile-time typestate Fiat–Shamir sponge transcript backed by 256-bit `cSHAKE256`.
///
/// Attempting to squeeze any Fiat–Shamir challenge from `FenziTranscript<Unbound>` or
/// `FenziTranscript<RelationBound>` is a **hard Rust compile-time error**:
///
/// ```compile_fail
/// use obend_crypto_exec::transcript::FenziTranscript;
/// let mut tr = FenziTranscript::new(b"seed");
/// let _ = tr.squeeze_ext2(); // ERROR: `Unbound` has no `squeeze_ext2`!
/// ```
///
/// ```compile_fail
/// use obend_crypto_exec::transcript::FenziTranscript;
/// let vk = [0u8; 32];
/// let mut tr = FenziTranscript::new(b"seed")
///     .bind_relation("OBEND.TEST/v1", &vk, b"r1cs-desc");
/// let _ = tr.squeeze_ext2(); // ERROR: `RelationBound` has no `squeeze_ext2` before `bind_instance`!
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FenziTranscript<Phase: TranscriptPhase> {
    state: [u8; 32],
    step_count: u64,
    relation_digest: [u8; 32],
    instance_digest: [u8; 32],
    _phase: PhantomData<Phase>,
}

impl<Phase: TranscriptPhase> FenziTranscript<Phase> {
    /// Inspect the current 32-byte (256-bit) sponge state.
    #[inline]
    pub const fn state(&self) -> &[u8; 32] {
        &self.state
    }

    /// Monotonic transcript transition counter.
    #[inline]
    pub const fn step_count(&self) -> u64 {
        self.step_count
    }

    /// Digest recorded during `bind_relation` (all-zeros on `Unbound`).
    #[inline]
    pub const fn relation_digest(&self) -> &[u8; 32] {
        &self.relation_digest
    }

    /// Digest recorded during `bind_instance` (all-zeros prior to `InstanceBound`).
    #[inline]
    pub const fn instance_digest(&self) -> &[u8; 32] {
        &self.instance_digest
    }
}

impl FenziTranscript<Unbound> {
    /// Construct a fresh `Unbound` transcript from a context nonce/seed under `OBEND.CRYPTO.FS.SEED/v1`.
    pub fn new(context_seed: &[u8]) -> Self {
        let state = cshake256_32(FS_SEED_CUSTOMIZATION, context_seed);
        Self {
            state,
            step_count: 0,
            relation_digest: [0u8; 32],
            instance_digest: [0u8; 32],
            _phase: PhantomData,
        }
    }

    /// **Sole constructor of `FenziTranscript<RelationBound>`** (`Fenzi ePrint 2026/1838` defense):
    /// injectively binds `(protocol_id, vk_digest, circuit_desc)` via 256-bit `cSHAKE256`.
    pub fn bind_relation(
        self,
        protocol_id: &str,
        vk_digest: &[u8; 32],
        circuit_desc: &[u8],
    ) -> FenziTranscript<RelationBound> {
        let proto_bytes = encode_string_codepoints(protocol_id);
        let rel_frame = encode_frame(&proto_bytes, vk_digest, circuit_desc);
        let mut preimage = encode_list_field(&self.state);
        preimage.extend_from_slice(&rel_frame);
        let next_state = cshake256_32(FS_BIND_CUSTOMIZATION, &preimage);
        FenziTranscript {
            state: next_state,
            step_count: 1,
            relation_digest: next_state,
            instance_digest: [0u8; 32],
            _phase: PhantomData,
        }
    }
}

impl FenziTranscript<RelationBound> {
    /// **Sole constructor of `FenziTranscript<InstanceBound>`** (closing `F3` & `F5`!):
    /// injectively absorbs `(comm_bytes, claimed_sum, point)` so no Fiat–Shamir challenge can ever
    /// be squeezed before the commitment, claimed sum, and evaluation point are fixed!
    pub fn bind_instance(
        self,
        comm_bytes: &[u8],
        claimed_sum: GoldilocksExt2,
        point: &[GoldilocksExt2],
    ) -> FenziTranscript<InstanceBound> {
        let sum_bytes = claimed_sum.to_be_bytes();
        let mut pt_bytes = leb128(point.len());
        for coord in point {
            pt_bytes.extend_from_slice(&coord.to_be_bytes());
        }
        let inst_frame = encode_frame(comm_bytes, &sum_bytes, &pt_bytes);
        let step_bytes = leb128_u64(self.step_count);
        let preimage = encode_frame(&self.state, &step_bytes, &inst_frame);
        let next_state = cshake256_32(FS_INSTANCE_CUSTOMIZATION, &preimage);
        FenziTranscript {
            state: next_state,
            step_count: self.step_count + 1,
            relation_digest: self.relation_digest,
            instance_digest: next_state,
            _phase: PhantomData,
        }
    }
}

impl FenziTranscript<InstanceBound> {
    /// Absorb a labeled prover message into an `InstanceBound` transcript, matching `absorbMsg`.
    pub fn absorb(&mut self, label: &[u8], msg_bytes: &[u8]) {
        let mut step_and_msg = leb128_u64(self.step_count);
        step_and_msg.extend_from_slice(msg_bytes);
        let frame = encode_frame(&self.state, label, &step_and_msg);
        self.state = cshake256_32(FS_ABSORB_CUSTOMIZATION, &frame);
        self.step_count += 1;
    }

    /// Absorb a single canonical `Goldilocks` element under `label`.
    #[inline]
    pub fn absorb_field(&mut self, label: &[u8], val: Goldilocks) {
        self.absorb(label, &val.to_be_bytes());
    }

    /// Absorb a canonical `GoldilocksExt2` element under `label`.
    #[inline]
    pub fn absorb_ext2(&mut self, label: &[u8], val: GoldilocksExt2) {
        self.absorb(label, &val.to_be_bytes());
    }

    /// Squeeze a full 32-byte (256-bit) challenge and ratchet the sponge state forward,
    /// matching `Obend.Crypto.Transcript.squeezeChallenge256`.
    pub fn squeeze_challenge_256(&mut self) -> [u8; 32] {
        let mut payload = encode_list_field(&self.state);
        payload.extend_from_slice(&leb128_u64(self.step_count));
        let out_bytes = cshake256_32(FS_SQUEEZE_CUSTOMIZATION, &payload);

        let mut ratchet_in = encode_list_field(&self.state);
        ratchet_in.extend_from_slice(&encode_list_field(&out_bytes));
        self.state = cshake256_32(FS_RATCHET_CUSTOMIZATION, &ratchet_in);
        self.step_count += 1;
        out_bytes
    }

    /// Squeeze a 128-bit challenge in `GoldilocksExt2` ($\mathbb{F}_{p^2}$) from two independent
    /// 128-bit halves of `squeeze_challenge_256` (matching `squeezeGoldilocksExt2` in Lean!).
    pub fn squeeze_ext2(&mut self) -> GoldilocksExt2 {
        let bytes = self.squeeze_challenge_256();
        let mut lo_arr = [0u8; 16];
        let mut hi_arr = [0u8; 16];
        lo_arr.copy_from_slice(&bytes[0..16]);
        hi_arr.copy_from_slice(&bytes[16..32]);
        let lo128 = u128::from_be_bytes(lo_arr);
        let hi128 = u128::from_be_bytes(hi_arr);
        GoldilocksExt2::new(
            Goldilocks::from_u128_reduced(lo128),
            Goldilocks::from_u128_reduced(hi128),
        )
    }

    /// Sample `count` unbiased ternary trits in `{-1, 0, +1}` via rejection sampling over base-3
    /// digits ($3^5 = 243 < 256$, extracting up to 5 independent unbiased trits per byte!).
    pub fn squeeze_ternary_trits(&mut self, count: usize) -> Vec<i8> {
        let raw_seed = self.squeeze_challenge_256();
        let mut xof = Cshake256Xof::new(b"OBEND.CRYPTO.FS.TERNARY/v1");
        xof.absorb(&raw_seed);

        let mut out = Vec::with_capacity(count);
        let mut byte = [0u8; 1];
        while out.len() < count {
            xof.squeeze(&mut byte);
            let b = byte[0];
            if b < 243 {
                let mut v = b;
                for _ in 0..5 {
                    if out.len() == count {
                        break;
                    }
                    let trit = (v % 3) as i8 - 1; // {-1, 0, +1}
                    out.push(trit);
                    v /= 3;
                }
            }
        }
        out
    }

    /// Squeeze a signed monomial challenge `(sign, exponent)` for $\pm X^{\text{exp}} \in R_{q_{\text{lat}}}$
    /// (`sign` in `{-1, +1}`, `exponent` in `0..ring_degree` where `ring_degree` is a power of two).
    pub fn squeeze_signed_monomial(&mut self, ring_degree: usize) -> (i64, usize) {
        assert!(
            ring_degree.is_power_of_two(),
            "ring_degree must be a power of two"
        );
        let bytes = self.squeeze_challenge_256();
        let word = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let sign = if (word & 1) == 0 { 1i64 } else { -1i64 };
        let exp = ((word >> 1) as usize) & (ring_degree - 1);
        (sign, exp)
    }

    /// Squeeze `count` distinct sorted query indices in `0..domain_size` (or all indices if
    /// `count >= domain_size`), used by `Canopy` proximity & evaluation column openings.
    pub fn squeeze_distinct_query_indices(
        &mut self,
        count: usize,
        domain_size: usize,
    ) -> Vec<usize> {
        assert!(
            domain_size.is_power_of_two(),
            "domain_size must be a power of two"
        );
        let target = count.min(domain_size);
        let seed = self.squeeze_challenge_256();
        let mut xof = Cshake256Xof::new(b"OBEND.CRYPTO.FS.QUERIES/v1");
        xof.absorb(&seed);

        let mask = domain_size - 1;
        let mut indices = Vec::with_capacity(target);
        let mut buf = [0u8; 8];
        while indices.len() < target {
            xof.squeeze(&mut buf);
            let idx = (u64::from_le_bytes(buf) as usize) & mask;
            if !indices.contains(&idx) {
                indices.push(idx);
            }
        }
        indices.sort_unstable();
        indices
    }

    /// Fork an `InstanceBound` transcript along a track label (`DUAL.TRACK1` / `DUAL.TRACK2`),
    /// matching `Obend.Crypto.DualSpine`.
    pub fn fork(&self, track_label: &[u8]) -> Self {
        let mut forked = self.clone();
        forked.absorb(track_label, &[]);
        forked
    }

    /// Join two forked `InstanceBound` transcripts back into `self` (`DUAL.JOIN`),
    /// matching `Obend.Crypto.DualSpine`.
    pub fn join(&mut self, track1: &Self, track2: &Self) {
        let join_frame = encode_frame(&track1.state, &track2.state, &[]);
        self.absorb(DUAL_JOIN_LABEL, &join_frame);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_to_32(hex: &str) -> [u8; 32] {
        assert_eq!(hex.len(), 64);
        let mut out = [0u8; 32];
        for i in 0..32 {
            out[i] = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    #[test]
    fn test_nist_fips202_shake256_and_sp800_185_cshake256_vectors() {
        // NIST FIPS 202 official test vector: SHAKE256("", 256)
        let expected_empty =
            hex_to_32("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f");
        assert_eq!(shake256_32(b""), expected_empty);

        // NIST FIPS 202 official test vector: SHAKE256("abc", 256)
        let expected_abc =
            hex_to_32("483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739");
        assert_eq!(shake256_32(b"abc"), expected_abc);

        // NIST SP 800-185 official Sample #3: cSHAKE256(X=00010203, L=256, N="", S="Email Signature")
        // Note: first 32 bytes of SP 800-185 cSHAKE256 Sample #3 (L=512 prefix = L=256 output because XOF!)
        let expected_cshake_sample3 =
            hex_to_32("d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1");
        assert_eq!(
            cshake256_32(b"Email Signature", &[0x00, 0x01, 0x02, 0x03]),
            expected_cshake_sample3
        );
    }

    #[test]
    fn test_fenzi_transcript_domain_and_instance_separation() {
        let vk = [0x42u8; 32];
        let pt = [GoldilocksExt2::from_canonical_u64_pair(7, 11).unwrap()];
        let sum1 = GoldilocksExt2::from_canonical_u64_pair(100, 0).unwrap();
        let sum2 = GoldilocksExt2::from_canonical_u64_pair(101, 0).unwrap();

        let mut tr_a = FenziTranscript::new(b"seed")
            .bind_relation("PROTO.A", &vk, b"circuit-1")
            .bind_instance(b"comm-1", sum1, &pt);
        let mut tr_b = FenziTranscript::new(b"seed")
            .bind_relation("PROTO.A", &vk, b"circuit-1")
            .bind_instance(b"comm-1", sum2, &pt);
        let mut tr_c = FenziTranscript::new(b"seed")
            .bind_relation("PROTO.A", &vk, b"circuit-2")
            .bind_instance(b"comm-1", sum1, &pt);
        let mut tr_d = FenziTranscript::new(b"seed")
            .bind_relation("PROTO.A", &vk, b"circuit-1")
            .bind_instance(b"comm-1", sum1, &[]);

        let ca = tr_a.squeeze_ext2();
        let cb = tr_b.squeeze_ext2();
        let cc = tr_c.squeeze_ext2();
        let cd = tr_d.squeeze_ext2();

        assert_ne!(ca, cb, "changing claimed_sum must change challenge (F3)");
        assert_ne!(
            ca, cc,
            "changing circuit_desc must change challenge (Fenzi 2026/1838)"
        );
        assert_ne!(
            ca, cd,
            "omitting evaluation point must change challenge (F5)"
        );
    }

    #[test]
    fn test_bind_instance_matches_lean_instance_preimage_list_framing() {
        let vk = [0x77u8; 32];
        let pt = [GoldilocksExt2::from_canonical_u64_pair(13, 19).unwrap()];
        let sum = GoldilocksExt2::from_canonical_u64_pair(42, 0).unwrap();
        let rel = FenziTranscript::new(b"lean-align").bind_relation("PROTO.LEAN", &vk, b"circ");
        let rel_state = *rel.state();

        let sum_bytes = sum.to_be_bytes();
        let mut pt_bytes = leb128(pt.len());
        pt_bytes.extend_from_slice(&pt[0].to_be_bytes());
        let inst_frame = encode_frame(b"comm-bytes", &sum_bytes, &pt_bytes);
        let step_bytes = leb128_u64(1);
        // Lean `Transcript.instancePreimageList`: `encodeFrameList relState (leb128 stepCount) instBytes`
        let expected_lean_preimage = encode_frame(&rel_state, &step_bytes, &inst_frame);
        let expected_state = cshake256_32(FS_INSTANCE_CUSTOMIZATION, &expected_lean_preimage);

        let bound = rel.bind_instance(b"comm-bytes", sum, &pt);
        assert_eq!(bound.state(), &expected_state);
        assert_eq!(bound.instance_digest(), &expected_state);
    }
}

#[cfg(test)]
mod xof_drop_tests {
    use super::*;
    #[test]
    fn drop_scrubs_sponge_and_buffer() {
        for squeeze in [false, true] {
            let mut xof = Cshake256Xof::new(b"scrub-test");
            xof.absorb(&[0x5a; 200]);
            if squeeze {
                xof.squeeze(&mut [0; 17]);
            }
            // Invoke the same cleanup body through a helper; Rust forbids explicit Drop calls.
            xof.scrub();
            assert_eq!(xof.state, [0; 25]);
            assert_eq!(xof.buf, [0; SHAKE256_RATE_BYTES]);
            assert_eq!((xof.buf_len, xof.squeeze_offset), (0, 0));
            assert!(!xof.squeezing);
        }
    }
}
