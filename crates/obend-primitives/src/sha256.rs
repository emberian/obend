//! FIPS 180-4 SHA-256, RFC 2104 HMAC-SHA-256 and RFC 5869 HKDF-SHA-256. Streaming, `no_std` and
//! allocation-free.

use core::fmt;

/// Round constants: the first 32 bits of the fractional parts of the cube roots of the first 64
/// primes (FIPS 180-4 §4.2.2).
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Initial hash value: the first 32 bits of the fractional parts of the square roots of the first
/// eight primes (FIPS 180-4 §5.3.3).
const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

const BLOCK_BYTES: usize = 64;

/// Streaming FIPS 180-4 SHA-256. The state can be copied to fork a hash at a shared prefix.
#[derive(Clone, Copy)]
pub struct Sha256 {
    state: [u32; 8],
    block: [u8; BLOCK_BYTES],
    block_len: usize,
    total_bytes: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Sha256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sha256").finish_non_exhaustive()
    }
}

impl Sha256 {
    pub const fn new() -> Self {
        Self {
            state: H0,
            block: [0; BLOCK_BYTES],
            block_len: 0,
            total_bytes: 0,
        }
    }

    /// Absorb the next part of the message.
    pub fn update(&mut self, mut data: &[u8]) {
        self.total_bytes = u64::try_from(data.len())
            .ok()
            .and_then(|n| self.total_bytes.checked_add(n))
            .expect("SHA-256 message length");
        if self.block_len > 0 {
            let take = (BLOCK_BYTES - self.block_len).min(data.len());
            self.block[self.block_len..self.block_len + take].copy_from_slice(&data[..take]);
            self.block_len += take;
            data = &data[take..];
            if self.block_len < BLOCK_BYTES {
                return;
            }
            compress(&mut self.state, &self.block);
            self.block_len = 0;
        }
        let (blocks, rest) = data.as_chunks::<BLOCK_BYTES>();
        for block in blocks {
            compress(&mut self.state, block);
        }
        self.block[..rest.len()].copy_from_slice(rest);
        self.block_len = rest.len();
    }

    pub fn finalize(mut self) -> [u8; 32] {
        self.finish()
    }

    fn finish(&mut self) -> [u8; 32] {
        let bit_len = self
            .total_bytes
            .checked_mul(8)
            .expect("SHA-256 message length");
        self.block[self.block_len] = 0x80;
        self.block[self.block_len + 1..].fill(0);
        if self.block_len >= BLOCK_BYTES - 8 {
            compress(&mut self.state, &self.block);
            self.block.fill(0);
        }
        self.block[BLOCK_BYTES - 8..].copy_from_slice(&bit_len.to_be_bytes());
        compress(&mut self.state, &self.block);
        let mut out = [0u8; 32];
        for (bytes, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(self.state) {
            *bytes = word.to_be_bytes();
        }
        self.state.fill(0);
        self.block.fill(0);
        core::hint::black_box((&self.state, &self.block));
        out
    }
}

fn compress(state: &mut [u32; 8], block: &[u8; BLOCK_BYTES]) {
    let mut w = [0u32; 64];
    for (word, bytes) in w.iter_mut().zip(block.as_chunks::<4>().0) {
        *word = u32::from_be_bytes(*bytes);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for (&k, &wi) in K.iter().zip(&w) {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(k)
            .wrapping_add(wi);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (word, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *word = word.wrapping_add(v);
    }
}

/// One-shot FIPS 180-4 SHA-256.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize()
}

/// `SHA-256(a ‖ b)`, the SSZ Merkle internal node.
pub fn sha256_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(a);
    h.update(b);
    h.finalize()
}

/// RFC 2104 HMAC-SHA-256 over the concatenation of `parts`.
fn hmac_sha256_parts(key: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut pad = [0u8; BLOCK_BYTES];
    if key.len() > BLOCK_BYTES {
        pad[..32].copy_from_slice(&sha256(key));
    } else {
        pad[..key.len()].copy_from_slice(key);
    }
    for b in &mut pad {
        *b ^= 0x36;
    }
    let mut inner = Sha256::new();
    inner.update(&pad);
    for part in parts {
        inner.update(part);
    }
    let inner = inner.finish();
    for b in &mut pad {
        *b ^= 0x36 ^ 0x5c;
    }
    let mut outer = Sha256::new();
    outer.update(&pad);
    outer.update(&inner);
    pad.fill(0);
    core::hint::black_box(&pad);
    outer.finish()
}

/// RFC 2104 HMAC-SHA-256.
pub fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(key, &[data])
}

/// RFC 5869 HKDF-Extract(salt, ikm) with SHA-256; an empty salt is 32 zero bytes.
pub fn hkdf_sha256_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {
    let salt: &[u8] = if salt.is_empty() { &[0; 32] } else { salt };
    hmac_sha256(salt, ikm)
}

/// RFC 5869 HKDF-Expand(prk, info, 32) with SHA-256: the single block `T(1)`.
pub fn hkdf_sha256_expand(prk: &[u8; 32], info: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(prk, &[info, &[0x01]])
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::string::String;
    use std::vec::Vec;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| std::format!("{x:02x}")).collect()
    }

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn fips_180_4_known_answers() {
        assert_eq!(
            hex(&sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(&sha256(
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
            )),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        assert_eq!(
            hex(&sha256(&[b'a'; 1_000_000])),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }

    /// Lengths on both sides of every padding boundary (Python `hashlib`).
    #[test]
    fn padding_boundaries() {
        let kats: [(usize, &str); 12] = [
            (
                0,
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                1,
                "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb",
            ),
            (
                3,
                "9834876dcfb05cb167a5c24953eba58c4ac89b1adf57f28f2f9d09af107ee8f0",
            ),
            (
                55,
                "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318",
            ),
            (
                56,
                "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
            ),
            (
                57,
                "f13b2d724659eb3bf47f2dd6af1accc87b81f09f59f2b75e5c0bed6589dfe8c6",
            ),
            (
                63,
                "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34",
            ),
            (
                64,
                "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb",
            ),
            (
                65,
                "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0",
            ),
            (
                119,
                "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb",
            ),
            (
                120,
                "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c",
            ),
            (
                128,
                "6836cf13bac400e9105071cd6af47084dfacad4e5e302c94bfed24e013afb73e",
            ),
        ];
        for (len, want) in kats {
            assert_eq!(hex(&sha256(&[b'a'; 128][..len])), want, "length {len}");
        }
    }

    #[test]
    fn streaming_matches_one_shot_across_chunkings() {
        let data: Vec<u8> = (0..1000u32).map(|i| (i * 7 + 3) as u8).collect();
        let want = sha256(&data);
        for chunk in [1, 7, 37, 63, 64, 65, 200] {
            let mut h = Sha256::new();
            for piece in data.chunks(chunk) {
                h.update(piece);
            }
            assert_eq!(h.finalize(), want, "chunk {chunk}");
        }
        let mut pair = [0u8; 64];
        pair[..32].copy_from_slice(&sha256(b"left"));
        pair[32..].copy_from_slice(&sha256(b"right"));
        assert_eq!(
            sha256_pair(&sha256(b"left"), &sha256(b"right")),
            sha256(&pair)
        );
    }

    #[test]
    fn rfc_4231_hmac_known_answers() {
        assert_eq!(
            hex(&hmac_sha256(&[0x0b; 20], b"Hi There")),
            "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
        );
        assert_eq!(
            hex(&hmac_sha256(b"Jefe", b"what do ya want for nothing?")),
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
        );
        assert_eq!(
            hex(&hmac_sha256(
                &[0xaa; 131],
                b"Test Using Larger Than Block-Size Key - Hash Key First"
            )),
            "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
        );
        assert_eq!(
            hex(&hmac_sha256(
                &[0xaa; 131],
                b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."
            )),
            "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
        );
    }

    /// RFC 5869 test cases 1 and 3; `T(1)` is the first 32 bytes of the OKM.
    #[test]
    fn rfc_5869_hkdf_known_answers() {
        let salt: Vec<u8> = (0..13).collect();
        let info: Vec<u8> = (0xf0..=0xf9).collect();
        let prk = hkdf_sha256_extract(&salt, &[0x0b; 22]);
        assert_eq!(
            hex(&prk),
            "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
        );
        assert_eq!(
            hkdf_sha256_expand(&prk, &info).to_vec(),
            unhex("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf")
        );
        let prk = hkdf_sha256_extract(&[], &[0x0b; 22]);
        assert_eq!(
            hex(&prk),
            "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"
        );
        assert_eq!(
            hex(&hkdf_sha256_expand(&prk, &[])),
            "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d"
        );
    }
}
