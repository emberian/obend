//! Keccak-f[1600] and its sponge functions: FIPS 202 SHA-3 and SHAKE, and NIST SP 800-185
//! `cSHAKE256` and `KMAC256`. Word-wise, `no_std`, and allocation-free.
//!
//! The permutation and framing match `Obend.Digest.Cshake256.Spec` and `Obend.Digest.Kmac256`,
//! and the entire crate extracts cleanly through Charon + Aeneas to pure Lean 4.35 (`aeneas/`).
//! A partial block lives in the 25-lane state, so a sponge is the lanes plus a byte position.
//!
//! Sponges and midstates clear their lanes on drop. Without volatile writes this is best
//! effort: copies the compiler made earlier are out of reach.

#![no_std]
#![forbid(unsafe_code)]

/// Sponge rate of `SHAKE128` in bytes.
pub const SHAKE128_RATE_BYTES: usize = 168;
/// Sponge rate of `SHA3-256`, `SHAKE256`, `cSHAKE256`, and `KMAC256` in bytes.
pub const SHAKE256_RATE_BYTES: usize = 136;
const SHA3_512_RATE_BYTES: usize = 72;

const SHA3_SUFFIX: u8 = 0x06;
const SHAKE_SUFFIX: u8 = 0x1f;
const CSHAKE_SUFFIX: u8 = 0x04;

/// The 24 FIPS 202 Keccak-f[1600] round constants.
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
pub const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// The 24-round Keccak-f[1600] permutation over 25 little-endian lanes indexed `x + 5 * y`.
pub fn keccak_f1600(state: &mut [u64; 25]) {
    // Lanes are locals named `a<x><y>`, so a round has no indexing and no bounds checks.
    #[rustfmt::skip]
    let [
        mut a00, mut a10, mut a20, mut a30, mut a40,
        mut a01, mut a11, mut a21, mut a31, mut a41,
        mut a02, mut a12, mut a22, mut a32, mut a42,
        mut a03, mut a13, mut a23, mut a33, mut a43,
        mut a04, mut a14, mut a24, mut a34, mut a44,
    ] = *state;

    macro_rules! rho {
        ($lane:expr, $index:literal) => {
            $lane.rotate_left(const { KECCAK_ROTATION_OFFSETS[$index] })
        };
    }
    macro_rules! chi {
        ($o0:ident $o1:ident $o2:ident $o3:ident $o4:ident,
         $b0:ident $b1:ident $b2:ident $b3:ident $b4:ident) => {
            $o0 = $b0 ^ (!$b1 & $b2);
            $o1 = $b1 ^ (!$b2 & $b3);
            $o2 = $b2 ^ (!$b3 & $b4);
            $o3 = $b3 ^ (!$b4 & $b0);
            $o4 = $b4 ^ (!$b0 & $b1);
        };
    }

    let mut round = 0;
    while round < 24 {
        // Theta.
        let c0 = a00 ^ a01 ^ a02 ^ a03 ^ a04;
        let c1 = a10 ^ a11 ^ a12 ^ a13 ^ a14;
        let c2 = a20 ^ a21 ^ a22 ^ a23 ^ a24;
        let c3 = a30 ^ a31 ^ a32 ^ a33 ^ a34;
        let c4 = a40 ^ a41 ^ a42 ^ a43 ^ a44;
        let d0 = c4 ^ c1.rotate_left(1);
        let d1 = c0 ^ c2.rotate_left(1);
        let d2 = c1 ^ c3.rotate_left(1);
        let d3 = c2 ^ c4.rotate_left(1);
        let d4 = c3 ^ c0.rotate_left(1);

        // Rho and pi: lane `(x, y)` moves to `b<y><2x + 3y mod 5>`.
        let b00 = rho!(a00 ^ d0, 0);
        let b02 = rho!(a10 ^ d1, 1);
        let b04 = rho!(a20 ^ d2, 2);
        let b01 = rho!(a30 ^ d3, 3);
        let b03 = rho!(a40 ^ d4, 4);
        let b13 = rho!(a01 ^ d0, 5);
        let b10 = rho!(a11 ^ d1, 6);
        let b12 = rho!(a21 ^ d2, 7);
        let b14 = rho!(a31 ^ d3, 8);
        let b11 = rho!(a41 ^ d4, 9);
        let b21 = rho!(a02 ^ d0, 10);
        let b23 = rho!(a12 ^ d1, 11);
        let b20 = rho!(a22 ^ d2, 12);
        let b22 = rho!(a32 ^ d3, 13);
        let b24 = rho!(a42 ^ d4, 14);
        let b34 = rho!(a03 ^ d0, 15);
        let b31 = rho!(a13 ^ d1, 16);
        let b33 = rho!(a23 ^ d2, 17);
        let b30 = rho!(a33 ^ d3, 18);
        let b32 = rho!(a43 ^ d4, 19);
        let b42 = rho!(a04 ^ d0, 20);
        let b44 = rho!(a14 ^ d1, 21);
        let b41 = rho!(a24 ^ d2, 22);
        let b43 = rho!(a34 ^ d3, 23);
        let b40 = rho!(a44 ^ d4, 24);

        chi!(a00 a10 a20 a30 a40, b00 b10 b20 b30 b40);
        chi!(a01 a11 a21 a31 a41, b01 b11 b21 b31 b41);
        chi!(a02 a12 a22 a32 a42, b02 b12 b22 b32 b42);
        chi!(a03 a13 a23 a33 a43, b03 b13 b23 b33 b43);
        chi!(a04 a14 a24 a34 a44, b04 b14 b24 b34 b44);

        // Iota.
        a00 ^= KECCAK_ROUND_CONSTANTS[round];
        round += 1;
    }

    *state = [
        a00, a10, a20, a30, a40, a01, a11, a21, a31, a41, a02, a12, a22, a32, a42, a03, a13, a23,
        a33, a43, a04, a14, a24, a34, a44,
    ];
}

/// The minimal nonzero byte width of `value` (`1..=8`).
pub const fn encoded_width(value: u64) -> usize {
    if value == 0 {
        return 1;
    }
    let mut v = value;
    let mut width = 0usize;
    while v > 0 {
        v >>= 8;
        width += 1;
    }
    width
}

/// SP 800-185 `left_encode`: the byte count, then the minimal big-endian bytes.
/// Writes into `out` and returns the encoded length.
pub fn left_encode(value: u64, out: &mut [u8; 9]) -> usize {
    let width = encoded_width(value);
    out[0] = width as u8;
    let mut i = 0usize;
    while i < width {
        let shift = (8 * (width - 1 - i)) as u32;
        out[1 + i] = ((value >> shift) & 0xff) as u8;
        i += 1;
    }
    width + 1
}

/// SP 800-185 `right_encode`: the minimal big-endian bytes, then the byte count.
/// Writes into `out` and returns the encoded length.
pub fn right_encode(value: u64, out: &mut [u8; 9]) -> usize {
    let width = encoded_width(value);
    let mut i = 0usize;
    while i < width {
        let shift = (8 * (width - 1 - i)) as u32;
        out[i] = ((value >> shift) & 0xff) as u8;
        i += 1;
    }
    out[width] = width as u8;
    width + 1
}

fn bit_length(byte_length: usize) -> u64 {
    let bytes = byte_length as u64;
    assert!(
        bytes as usize == byte_length && bytes <= 0x1fff_ffff_ffff_ffff,
        "bit length fits in u64"
    );
    bytes * 8
}

fn zero_lanes(lanes: &mut [u64; 25]) {
    let mut i = 0usize;
    while i < 25 {
        lanes[i] = 0;
        i += 1;
    }
}

fn xor_padding<const RATE: usize>(lanes: &mut [u64; 25], pos: usize, suffix: u8) {
    let idx0 = pos / 8;
    let shift0 = (8 * (pos % 8)) as u32;
    lanes[idx0] = lanes[idx0] ^ ((suffix as u64) << shift0);
    // A suffix ending in bit 7 can fill the block with the first bit of pad10*1.
    // Its closing bit then belongs in a new block.
    let last = RATE - 1;
    if pos == last && (suffix & 0x80) != 0 {
        keccak_f1600(lanes);
    }
    let idx1 = last / 8;
    let shift1 = (8 * (last % 8)) as u32;
    lanes[idx1] = lanes[idx1] ^ (0x80u64 << shift1);
}

#[inline]
fn load_le_u64_at(data: &[u8], offset: usize) -> u64 {
    (data[offset] as u64)
        | ((data[offset + 1] as u64) << 8)
        | ((data[offset + 2] as u64) << 16)
        | ((data[offset + 3] as u64) << 24)
        | ((data[offset + 4] as u64) << 32)
        | ((data[offset + 5] as u64) << 40)
        | ((data[offset + 6] as u64) << 48)
        | ((data[offset + 7] as u64) << 56)
}

/// An absorbed sponge state on a rate boundary: 25 lanes and the pending domain suffix.
///
/// For a keyed sponge this is key-equivalent material, so it is cleared on drop.
#[derive(Clone)]
pub struct Midstate<const RATE: usize> {
    lanes: [u64; 25],
    suffix: u8,
}

impl<const RATE: usize> Midstate<RATE> {
    /// Rebuilds a midstate from its 25 lanes and nonzero delimited suffix.
    pub const fn new(lanes: [u64; 25], suffix: u8) -> Self {
        assert!(suffix != 0, "delimited suffix must be nonzero");
        Self { lanes, suffix }
    }

    /// The 25 lanes.
    pub const fn lanes(&self) -> &[u64; 25] {
        &self.lanes
    }

    /// The domain suffix the resumed sponge will pad with.
    pub const fn suffix(&self) -> u8 {
        self.suffix
    }
}

impl<const RATE: usize> Drop for Midstate<RATE> {
    fn drop(&mut self) {
        zero_lanes(&mut self.lanes);
        self.suffix = 0;
    }
}

/// An incremental Keccak sponge with a byte rate `RATE` and a delimited domain suffix.
#[derive(Clone)]
pub struct KeccakSponge<const RATE: usize> {
    lanes: [u64; 25],
    pos: usize,
    suffix: u8,
    squeezing: bool,
}

impl<const RATE: usize> Drop for KeccakSponge<RATE> {
    fn drop(&mut self) {
        self.scrub();
    }
}

impl<const RATE: usize> KeccakSponge<RATE> {
    const VALID_RATE: () = assert!(RATE > 0 && RATE <= 200 && RATE % 8 == 0);

    /// An empty sponge with a nonzero delimited suffix and a rate of 1 to 25 whole lanes.
    pub const fn new(suffix: u8) -> Self {
        let () = Self::VALID_RATE;
        assert!(suffix != 0, "delimited suffix must be nonzero");
        Self {
            lanes: [0; 25],
            pos: 0,
            suffix,
            squeezing: false,
        }
    }

    /// Resumes absorbing from a rate-aligned midstate.
    pub fn from_midstate(midstate: &Midstate<RATE>) -> Self {
        let () = Self::VALID_RATE;
        Self {
            lanes: midstate.lanes,
            pos: 0,
            suffix: midstate.suffix,
            squeezing: false,
        }
    }

    fn scrub(&mut self) {
        zero_lanes(&mut self.lanes);
        self.pos = 0;
        self.suffix = 0;
        self.squeezing = false;
    }

    #[inline]
    fn absorb_byte(&mut self, byte: u8) {
        let idx = self.pos / 8;
        let shift = (8 * (self.pos % 8)) as u32;
        self.lanes[idx] = self.lanes[idx] ^ ((byte as u64) << shift);
        self.pos += 1;
        if self.pos == RATE {
            keccak_f1600(&mut self.lanes);
            self.pos = 0;
        }
    }

    /// Absorbs bytes up to a lane boundary, then whole little-endian lanes, then the tail.
    ///
    /// # Panics
    /// If squeezing has begun.
    pub fn absorb(&mut self, data: &[u8]) {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot absorb after squeezing began");
        let len = data.len();
        let mut idx = 0usize;
        while idx < len && self.pos % 8 != 0 {
            self.absorb_byte(data[idx]);
            idx += 1;
        }
        while len - idx >= 8 {
            let word = load_le_u64_at(data, idx);
            let lane_idx = self.pos / 8;
            self.lanes[lane_idx] = self.lanes[lane_idx] ^ word;
            self.pos += 8;
            idx += 8;
            if self.pos == RATE {
                keccak_f1600(&mut self.lanes);
                self.pos = 0;
            }
        }
        while idx < len {
            self.absorb_byte(data[idx]);
            idx += 1;
        }
    }

    fn absorb_left_encode_count(&mut self, value: u64) -> usize {
        let mut encoded = [0u8; 9];
        let len = left_encode(value, &mut encoded);
        let mut i = 0usize;
        while i < len {
            self.absorb_byte(encoded[i]);
            i += 1;
        }
        len
    }

    /// Absorbs SP 800-185 `left_encode(value)`.
    pub fn absorb_left_encode(&mut self, value: u64) {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot absorb after squeezing began");
        let _ = self.absorb_left_encode_count(value);
    }

    /// Absorbs SP 800-185 `right_encode(value)`.
    pub fn absorb_right_encode(&mut self, value: u64) {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot absorb after squeezing began");
        let mut encoded = [0u8; 9];
        let len = right_encode(value, &mut encoded);
        let mut i = 0usize;
        while i < len {
            self.absorb_byte(encoded[i]);
            i += 1;
        }
    }

    fn absorb_encoded_string(&mut self, string: &[u8]) -> usize {
        let header_len = self.absorb_left_encode_count(bit_length(string.len()));
        self.absorb(string);
        (header_len % RATE + string.len() % RATE) % RATE
    }

    fn finish_bytepad(&mut self, filled: usize) {
        if filled != 0 {
            let pad = RATE - filled;
            let mut i = 0usize;
            while i < pad {
                self.absorb_byte(0);
                i += 1;
            }
        }
    }

    /// Absorbs SP 800-185 `bytepad(encode_string(first), RATE)`.
    pub fn absorb_bytepad_1(&mut self, first: &[u8]) {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot absorb after squeezing began");
        let width_len = self.absorb_left_encode_count(RATE as u64);
        let first_mod = self.absorb_encoded_string(first);
        let filled = (width_len % RATE + first_mod) % RATE;
        self.finish_bytepad(filled);
    }

    /// Absorbs SP 800-185 `bytepad(encode_string(first) ‖ encode_string(second), RATE)`.
    pub fn absorb_bytepad_2(&mut self, first: &[u8], second: &[u8]) {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot absorb after squeezing began");
        let width_len = self.absorb_left_encode_count(RATE as u64);
        let first_mod = self.absorb_encoded_string(first);
        let filled0 = (width_len % RATE + first_mod) % RATE;
        let second_mod = self.absorb_encoded_string(second);
        let filled = (filled0 + second_mod) % RATE;
        self.finish_bytepad(filled);
    }

    /// The byte position within the current rate block.
    pub const fn position(&self) -> usize {
        self.pos
    }

    /// The 25 lanes, with any partial block already xored in.
    pub const fn lanes(&self) -> &[u64; 25] {
        &self.lanes
    }

    /// The lanes as the final absorb would permute them, with the padding xored in.
    pub fn padded_lanes(&self) -> [u64; 25] {
        let () = Self::VALID_RATE;
        assert!(!self.squeezing, "cannot pad after squeezing began");
        let mut lanes = self.lanes;
        xor_padding::<RATE>(&mut lanes, self.pos, self.suffix);
        lanes
    }

    /// The 25-lane state, when absorbing on a rate boundary.
    pub fn midstate(&self) -> Option<Midstate<RATE>> {
        if !self.squeezing && self.pos == 0 {
            Some(Midstate::new(self.lanes, self.suffix))
        } else {
            None
        }
    }

    /// Pads on the first call, then writes the next `out.len()` bytes of the output stream.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        let () = Self::VALID_RATE;
        if !self.squeezing {
            xor_padding::<RATE>(&mut self.lanes, self.pos, self.suffix);
            keccak_f1600(&mut self.lanes);
            self.pos = 0;
            self.squeezing = true;
        }
        let out_len = out.len();
        let mut written = 0usize;
        while written < out_len {
            if self.pos == RATE {
                keccak_f1600(&mut self.lanes);
                self.pos = 0;
            }
            let lane = self.lanes[self.pos / 8];
            let shift = (8 * (self.pos % 8)) as u32;
            out[written] = ((lane >> shift) & 0xff) as u8;
            written += take_one();
            self.pos += 1;
        }
    }

    /// Squeezes the first 32 output bytes and consumes the sponge.
    pub fn finalize_32(mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.squeeze(&mut out);
        out
    }
}

#[inline]
const fn take_one() -> usize {
    1
}

macro_rules! xof_methods {
    ($name:ident, $rate:expr) => {
        impl $name {
            /// Absorbs message bytes.
            ///
            /// # Panics
            /// If squeezing has begun.
            pub fn absorb(&mut self, data: &[u8]) {
                self.0.absorb(data);
            }

            /// Pads on the first call, then writes the next `out.len()` output bytes.
            pub fn squeeze(&mut self, out: &mut [u8]) {
                self.0.squeeze(out);
            }

            /// The 25-lane state, when absorbing on a rate boundary.
            pub fn midstate(&self) -> Option<Midstate<{ $rate }>> {
                self.0.midstate()
            }

            /// Resumes a rate-aligned midstate from the same XOF and domain.
            pub fn from_midstate(midstate: &Midstate<{ $rate }>) -> Self {
                Self(KeccakSponge::from_midstate(midstate))
            }

            /// Squeezes the first 32 output bytes and consumes the sponge.
            pub fn finalize_32(self) -> [u8; 32] {
                self.0.finalize_32()
            }
        }
    };
}

/// Incremental FIPS 202 `SHAKE128`.
#[derive(Clone)]
pub struct Shake128(KeccakSponge<SHAKE128_RATE_BYTES>);

impl Shake128 {
    /// An empty `SHAKE128` sponge.
    pub const fn new() -> Self {
        Self(KeccakSponge::new(SHAKE_SUFFIX))
    }
}

impl Default for Shake128 {
    fn default() -> Self {
        Self::new()
    }
}

xof_methods!(Shake128, SHAKE128_RATE_BYTES);

/// Incremental FIPS 202 `SHAKE256`.
#[derive(Clone)]
pub struct Shake256(KeccakSponge<SHAKE256_RATE_BYTES>);

impl Shake256 {
    /// An empty `SHAKE256` sponge.
    pub const fn new() -> Self {
        Self(KeccakSponge::new(SHAKE_SUFFIX))
    }
}

impl Default for Shake256 {
    fn default() -> Self {
        Self::new()
    }
}

xof_methods!(Shake256, SHAKE256_RATE_BYTES);

/// Incremental SP 800-185 `cSHAKE256`.
#[derive(Clone)]
pub struct Cshake256(KeccakSponge<SHAKE256_RATE_BYTES>);

impl Cshake256 {
    /// `cSHAKE256` with function name `N` and customization `S`.
    /// When both are empty this is `SHAKE256`, as SP 800-185 §3.3 requires.
    pub fn new(name: &[u8], customization: &[u8]) -> Self {
        if name.is_empty() && customization.is_empty() {
            return Self(KeccakSponge::new(SHAKE_SUFFIX));
        }
        let mut sponge = KeccakSponge::new(CSHAKE_SUFFIX);
        sponge.absorb_bytepad_2(name, customization);
        Self(sponge)
    }

    /// `cSHAKE256` with an empty function name and customization `S`.
    pub fn customized(customization: &[u8]) -> Self {
        let empty: [u8; 0] = [];
        Self::new(&empty, customization)
    }

    /// Absorbs SP 800-185 `left_encode(value)`.
    pub fn absorb_left_encode(&mut self, value: u64) {
        self.0.absorb_left_encode(value);
    }

    /// The byte position within the current rate block.
    pub const fn position(&self) -> usize {
        self.0.position()
    }

    /// The 25 lanes, with any partial block already xored in.
    pub const fn lanes(&self) -> &[u64; 25] {
        self.0.lanes()
    }

    /// The lanes as the final absorb would permute them, with the padding xored in.
    pub fn padded_lanes(&self) -> [u64; 25] {
        self.0.padded_lanes()
    }
}

xof_methods!(Cshake256, SHAKE256_RATE_BYTES);

/// Incremental SP 800-185 `KMAC256`. The output length `L` is bound when finalizing.
#[derive(Clone)]
pub struct Kmac256(KeccakSponge<SHAKE256_RATE_BYTES>);

impl Kmac256 {
    /// `KMAC256` under `key` with customization `S`.
    pub fn new(key: &[u8], customization: &[u8]) -> Self {
        let Cshake256(mut sponge) = Cshake256::new(b"KMAC", customization);
        sponge.absorb_bytepad_1(key);
        Self(sponge)
    }

    /// Absorbs message bytes.
    pub fn absorb(&mut self, data: &[u8]) {
        self.0.absorb(data);
    }

    /// The 25-lane state, when absorbing on a rate boundary. Right after [`Kmac256::new`] this
    /// is the keyed state shared by every message under this key and customization.
    pub fn midstate(&self) -> Option<Midstate<SHAKE256_RATE_BYTES>> {
        self.0.midstate()
    }

    /// Resumes a rate-aligned state captured under the same KMAC key and customization.
    pub fn from_midstate(midstate: &Midstate<SHAKE256_RATE_BYTES>) -> Self {
        Self(KeccakSponge::from_midstate(midstate))
    }

    /// Binds `L = 8 * out.len()` with `right_encode` and writes the tag.
    pub fn finalize(self, out: &mut [u8]) {
        let bits = bit_length(out.len());
        self.finalize_bits(out, bits);
    }

    /// Binds `L = bits` with `right_encode` and writes the first `bits` output bits. FIPS 202
    /// orders a byte's bits from least significant, so the last byte keeps its low bits.
    ///
    /// # Panics
    /// If `out` is not exactly `bits.div_ceil(8)` bytes long.
    pub fn finalize_bits(mut self, out: &mut [u8], bits: u64) {
        let out_bytes = out.len() as u64;
        let needed = if bits == 0 { 0 } else { ((bits - 1) / 8) + 1 };
        assert!(
            out_bytes as usize == out.len() && out_bytes == needed,
            "output buffer must hold exactly the requested bits"
        );
        self.0.absorb_right_encode(bits);
        self.0.squeeze(out);
        let spare = bits % 8;
        if spare != 0 {
            let last_idx = out.len() - 1;
            let mask = ((1u16 << (spare as u32)) - 1) as u8;
            out[last_idx] = out[last_idx] & mask;
        }
    }
}

/// One-shot `cSHAKE256` with an empty function name, customization `S`, and any output length.
pub fn cshake256(customization: &[u8], input: &[u8], out: &mut [u8]) {
    let mut xof = Cshake256::customized(customization);
    xof.absorb(input);
    xof.squeeze(out);
}

/// One-shot 32-byte `cSHAKE256` with an empty function name, matching
/// `Obend.Digest.Cshake256.cshake256Bytes`.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut xof = Cshake256::customized(customization);
    xof.absorb(input);
    xof.finalize_32()
}

/// One-shot `SHAKE256` into `out`.
pub fn shake256_into(input: &[u8], out: &mut [u8]) {
    let mut xof = Shake256::new();
    xof.absorb(input);
    xof.squeeze(out);
}

/// One-shot 32-byte `SHAKE256`.
pub fn shake256_32(input: &[u8]) -> [u8; 32] {
    let mut xof = Shake256::new();
    xof.absorb(input);
    xof.finalize_32()
}

/// One-shot FIPS 202 `SHA3-256`.
pub fn sha3_256(input: &[u8]) -> [u8; 32] {
    let mut sponge = KeccakSponge::<SHAKE256_RATE_BYTES>::new(SHA3_SUFFIX);
    sponge.absorb(input);
    sponge.finalize_32()
}

/// One-shot FIPS 202 `SHA3-512`.
pub fn sha3_512(input: &[u8]) -> [u8; 64] {
    let mut sponge = KeccakSponge::<SHA3_512_RATE_BYTES>::new(SHA3_SUFFIX);
    sponge.absorb(input);
    let mut out = [0u8; 64];
    sponge.squeeze(&mut out);
    out
}

/// One-shot `KMAC256` with `L = 256`, matching `Obend.Digest.Kmac256.kmac256Bytes`.
pub fn kmac256_32(key: &[u8], customization: &[u8], message: &[u8]) -> [u8; 32] {
    let mut mac = Kmac256::new(key, customization);
    mac.absorb(message);
    let mut tag = [0u8; 32];
    mac.finalize(&mut tag);
    tag
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scrub_clears_lanes_position_and_phase() {
        for squeeze in [false, true] {
            let mut sponge = KeccakSponge::<SHAKE256_RATE_BYTES>::new(CSHAKE_SUFFIX);
            sponge.absorb(&[0x5a; 200]);
            if squeeze {
                sponge.squeeze(&mut [0; 17]);
            }
            assert_ne!(sponge.lanes, [0; 25]);
            sponge.scrub();
            assert_eq!(sponge.lanes, [0; 25]);
            assert_eq!((sponge.pos, sponge.suffix, sponge.squeezing), (0, 0, false));
        }
    }

    #[test]
    #[should_panic(expected = "cannot absorb after squeezing began")]
    fn absorb_after_squeeze_panics() {
        let mut xof = Shake256::new();
        xof.squeeze(&mut []);
        xof.absorb(b"late");
    }
}
