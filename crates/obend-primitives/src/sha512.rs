//! FIPS 180-4 SHA-384 / SHA-512 and RFC 2104 HMAC-SHA-384 / HMAC-SHA-512. Streaming, `no_std`
//! and allocation-free. Round constants are the first 64 bits of the fractional parts of the cube
//! roots of the first 80 primes; IVs from square roots of primes 1..8 (SHA-512) and 9..16
//! (SHA-384), FIPS 180-4 §4.2.3 / §5.3.4-5.3.5.

use core::fmt;

const K512: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

const H512: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

const H384: [u64; 8] = [
    0xcbbb9d5dc1059ed8,
    0x629a292a367cd507,
    0x9159015a3070dd17,
    0x152fecd8f70e5939,
    0x67332667ffc00b31,
    0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7,
    0x47b5481dbefa4fa4,
];

const BLOCK_BYTES: usize = 128;

/// The SHA-512 compression state. SHA-384 is the same with another IV, truncated to 48 bytes.
#[derive(Clone)]
struct Core {
    state: [u64; 8],
    block: [u8; BLOCK_BYTES],
    block_len: usize,
    total_bytes: u128,
}

impl Drop for Core {
    fn drop(&mut self) {
        self.state = [0; 8];
        self.block.fill(0);
        self.block_len = 0;
        self.total_bytes = 0;
        core::hint::black_box((&self.state, &self.block));
    }
}

impl Core {
    const fn new(iv: [u64; 8]) -> Self {
        Self {
            state: iv,
            block: [0; BLOCK_BYTES],
            block_len: 0,
            total_bytes: 0,
        }
    }

    fn update(&mut self, mut data: &[u8]) {
        self.total_bytes = self
            .total_bytes
            .checked_add(data.len() as u128)
            .expect("SHA-512 message length");
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

    /// Pads and returns all eight state words big-endian; the caller truncates for SHA-384.
    fn finalize(&mut self) -> [u8; 64] {
        let bit_len = self
            .total_bytes
            .checked_mul(8)
            .expect("SHA-512 message length");
        self.block[self.block_len] = 0x80;
        self.block[self.block_len + 1..].fill(0);
        if self.block_len >= BLOCK_BYTES - 16 {
            compress(&mut self.state, &self.block);
            self.block.fill(0);
        }
        self.block[BLOCK_BYTES - 16..].copy_from_slice(&bit_len.to_be_bytes());
        compress(&mut self.state, &self.block);
        let mut out = [0u8; 64];
        for (bytes, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(self.state) {
            *bytes = word.to_be_bytes();
        }
        out
    }
}

fn compress(state: &mut [u64; 8], block: &[u8; BLOCK_BYTES]) {
    let mut w = [0u64; 80];
    for (word, bytes) in w.iter_mut().zip(block.as_chunks::<8>().0) {
        *word = u64::from_be_bytes(*bytes);
    }
    for i in 16..80 {
        let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
        let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for (&k, &wi) in K512.iter().zip(&w) {
        let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(k)
            .wrapping_add(wi);
        let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
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

/// Streaming FIPS 180-4 SHA-512. The state is cleared on drop.
#[derive(Clone)]
pub struct Sha512(Core);

impl Default for Sha512 {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Sha512 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sha512").finish_non_exhaustive()
    }
}

impl Sha512 {
    pub const fn new() -> Self {
        Self(Core::new(H512))
    }

    /// Absorbs `data`. Panics past the FIPS 180-4 bound of `2^128 - 1` message bits.
    pub fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }

    pub fn finalize(mut self) -> [u8; 64] {
        self.0.finalize()
    }
}

/// Streaming FIPS 180-4 SHA-384. The state is cleared on drop.
#[derive(Clone)]
pub struct Sha384(Core);

impl Default for Sha384 {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Sha384 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sha384").finish_non_exhaustive()
    }
}

impl Sha384 {
    pub const fn new() -> Self {
        Self(Core::new(H384))
    }

    /// Absorbs `data`. Panics past the FIPS 180-4 bound of `2^128 - 1` message bits.
    pub fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }

    pub fn finalize(mut self) -> [u8; 48] {
        truncate(&self.0.finalize())
    }
}

fn truncate<const OUT: usize>(full: &[u8; 64]) -> [u8; OUT] {
    let mut out = [0u8; OUT];
    out.copy_from_slice(&full[..OUT]);
    out
}

/// One SHA-512-family digest of the concatenation of `parts`, truncated to `OUT` bytes.
fn digest<const OUT: usize>(iv: [u64; 8], parts: &[&[u8]]) -> [u8; OUT] {
    let mut core = Core::new(iv);
    for part in parts {
        core.update(part);
    }
    truncate(&core.finalize())
}

/// FIPS 180-4 SHA-512.
pub fn sha512(data: &[u8]) -> [u8; 64] {
    digest(H512, &[data])
}

/// FIPS 180-4 SHA-384.
pub fn sha384(data: &[u8]) -> [u8; 48] {
    digest(H384, &[data])
}

/// RFC 2104 HMAC over the SHA-512 family member with IV `iv` and `OUT`-byte digests.
fn hmac<const OUT: usize>(iv: [u64; 8], key: &[u8], data: &[u8]) -> [u8; OUT] {
    let mut pad = [0u8; BLOCK_BYTES];
    if key.len() > BLOCK_BYTES {
        pad[..OUT].copy_from_slice(&digest::<OUT>(iv, &[key]));
    } else {
        pad[..key.len()].copy_from_slice(key);
    }
    for b in &mut pad {
        *b ^= 0x36;
    }
    let inner = digest::<OUT>(iv, &[&pad, data]);
    for b in &mut pad {
        *b ^= 0x36 ^ 0x5c;
    }
    let out = digest::<OUT>(iv, &[&pad, &inner]);
    pad.fill(0);
    core::hint::black_box(&pad);
    out
}

/// RFC 2104 HMAC-SHA-384.
pub fn hmac_sha384(key: &[u8], data: &[u8]) -> [u8; 48] {
    hmac(H384, key, data)
}

/// RFC 2104 HMAC-SHA-512.
pub fn hmac_sha512(key: &[u8], data: &[u8]) -> [u8; 64] {
    hmac(H512, key, data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::string::String;
    use std::vec::Vec;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| std::format!("{x:02x}")).collect()
    }

    #[test]
    fn fips_180_4_known_answers() {
        assert_eq!(hex(&sha512(b"abc")), "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
        assert_eq!(hex(&sha384(b"abc")), "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7");
        assert_eq!(hex(&sha512(b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")), "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909");
        assert_eq!(hex(&sha512(&[b'a'; 1000])), "67ba5535a46e3f86dbfbed8cbbaf0125c76ed549ff8b0b9e03e0c88cf90fa634fa7b12b47d77b694de488ace8d9a65967dc96df599727d3292a8d9d447709c97");
    }

    /// Lengths on both sides of every padding boundary (Python `hashlib`).
    #[test]
    fn padding_boundaries() {
        let kats: [(usize, &str, &str); 8] = [
            (111, "fa9121c7b32b9e01733d034cfc78cbf67f926c7ed83e82200ef86818196921760b4beff48404df811b953828274461673c68d04e297b0eb7b2b4d60fc6b566a2", "3c37955051cb5c3026f94d551d5b5e2ac38d572ae4e07172085fed81f8466b8f90dc23a8ffcdea0b8d8e58e8fdacc80a"),
            (112, "c01d080efd492776a1c43bd23dd99d0a2e626d481e16782e75d54c2503b5dc32bd05f0f1ba33e568b88fd2d970929b719ecbb152f58f130a407c8830604b70ca", "187d4e07cb306103c69967bf544d0dfbe9042577599c73c330abc0cb64c61236d5ed565ee19119d8c31779a38f791fcd"),
            (113, "55ddd8ac210a6e18ba1ee055af84c966e0dbff091c43580ae1be703bdb85da31acf6948cf5bd90c55a20e5450f22fb89bd8d0085e39f85a86cc46abbca75e24d", "1d6bed01626682961b50da078a6b1da707c1da0c8a0a3226f159235bd45ed724a0622fa6f39fd70007a6c72a5cda43ae"),
            (127, "828613968b501dc00a97e08c73b118aa8876c26b8aac93df128502ab360f91bab50a51e088769a5c1eff4782ace147dce3642554199876374291f5d921629502", "9bd06b1763c2cf7aef40e795dc65bc96d59c41b537f3ad72ebdefd485476b5717c1aeb37c327fe9c1831b12b9efd08ae"),
            (128, "b73d1929aa615934e61a871596b3f3b33359f42b8175602e89f7e06e5f658a243667807ed300314b95cacdd579f3e33abdfbe351909519a846d465c59582f321", "edb12730a366098b3b2beac75a3bef1b0969b15c48e2163c23d96994f8d1bef760c7e27f3c464d3829f56c0d53808b0b"),
            (129, "4f681e0bd53cda4b5a2041cc8a06f2eabde44fb16c951fbd5b87702f07aeab611565b19c47fde30587177ebb852e3971bbd8d3fd30da18d71037dfbd98420429", "39b6f5a7b0e781dbc419f72e49b30eaac10f2c98c4403bc610da31067fd1b48f324138c8615d2b496d08d73d5e865326"),
            (239, "52c853cb8d907f3d4d6b889beb027985d7c273486d75f8baf26f80d24e90c74c6c3de3e22131582380a7d14d43f2941a31385439cd6ddc469f628015e50bf286", "e247c35f4bc1aa38026f8880c8c97305545d00d3f859e00c57d1c1f0a176b3c6b749c4eb081f08bd0fba500969cd056a"),
            (240, "4c296d90c61052a62ffb1dd196f1b7b09373b1f93e71836baebf89690546b7595684dbe9467a8e484fa0d1094272b4344a7c24f5fee8daedeb0bf549c985ab5f", "4d86957beab348a29180f02d02564ac1d32f5b4c217ece2b038f7c184f0cafc8c8e438eb82aa03796170e0a7ce8c0675"),
        ];
        for (len, want512, want384) in kats {
            let msg = &[b'a'; 240][..len];
            assert_eq!(hex(&sha512(msg)), want512, "SHA-512 length {len}");
            assert_eq!(hex(&sha384(msg)), want384, "SHA-384 length {len}");
        }
    }

    #[test]
    fn streaming_matches_one_shot_across_chunkings() {
        let data: Vec<u8> = (0..1000u32).map(|i| (i * 7 + 3) as u8).collect();
        for chunk in [1, 37, 111, 128, 129, 400] {
            let mut s512 = Sha512::new();
            let mut s384 = Sha384::new();
            for piece in data.chunks(chunk) {
                s512.update(piece);
                s384.update(piece);
            }
            assert_eq!(s512.finalize(), sha512(&data), "chunk {chunk}");
            assert_eq!(s384.finalize(), sha384(&data), "chunk {chunk}");
        }
    }

    #[test]
    fn rfc_4231_hmac_known_answers() {
        assert_eq!(hex(&hmac_sha384(&[0x0b; 20], b"Hi There")), "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6");
        assert_eq!(hex(&hmac_sha512(&[0x0b; 20], b"Hi There")), "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854");
        assert_eq!(hex(&hmac_sha384(b"Jefe", b"what do ya want for nothing?")), "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649");
        assert_eq!(
            hex(&hmac_sha384(&[0xaa; 131], b"Test Using Larger Than Block-Size Key - Hash Key First")),
            "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab4030fe8296248df163f44952"
        );
        assert_eq!(
            hex(&hmac_sha512(&[0xaa; 131], b"Test Using Larger Than Block-Size Key - Hash Key First")),
            "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"
        );
    }
}
