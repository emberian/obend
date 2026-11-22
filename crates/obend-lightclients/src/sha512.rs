//! Pure-Rust FIPS 180-4 SHA-384 / SHA-512 and RFC 2104 HMAC-SHA-384 / HMAC-SHA-512
//! (zero external crates). Round constants are the first 64 bits of the fractional parts of
//! the cube roots of the first 80 primes; IVs from square roots of primes 1..8 (SHA-512) and
//! 9..16 (SHA-384), FIPS 180-4 §4.2.3 / §5.3.4-5.3.5.

const K512: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

const H512: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

const H384: [u64; 8] = [
    0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4,
];

/// Streaming SHA-512 core (SHA-384 is the same compression with a different IV, truncated).
#[derive(Clone)]
pub struct Sha512 {
    h: [u64; 8],
    buf: [u8; 128],
    buf_len: usize,
    total_len: u128,
    out_len: usize,
}

impl Default for Sha512 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha512 {
    pub fn new() -> Self {
        Self { h: H512, buf: [0u8; 128], buf_len: 0, total_len: 0, out_len: 64 }
    }

    /// SHA-384 instance (FIPS 180-4 §5.3.4 IV, 48-byte output).
    pub fn new_384() -> Self {
        Self { h: H384, buf: [0u8; 128], buf_len: 0, total_len: 0, out_len: 48 }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.total_len = self.total_len.wrapping_add(data.len() as u128);
        if self.buf_len > 0 {
            let take = (128 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 128 {
                let block = self.buf;
                compress(&mut self.h, &block);
                self.buf_len = 0;
            }
        }
        while data.len() >= 128 {
            let mut block = [0u8; 128];
            block.copy_from_slice(&data[..128]);
            compress(&mut self.h, &block);
            data = &data[128..];
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.buf_len = data.len();
        }
    }

    /// Finalize, returning `out_len` (64 or 48) bytes.
    pub fn finalize_vec(mut self) -> Vec<u8> {
        let bit_len = self.total_len.wrapping_mul(8);
        let mut pad = vec![0x80u8];
        let rem = (self.buf_len + 1) % 128;
        let zeros = if rem <= 112 { 112 - rem } else { 240 - rem };
        pad.extend(std::iter::repeat(0u8).take(zeros));
        pad.extend_from_slice(&bit_len.to_be_bytes());
        let total = self.total_len;
        self.update(&pad);
        self.total_len = total;
        debug_assert_eq!(self.buf_len, 0);
        let mut out = Vec::with_capacity(64);
        for w in self.h.iter() {
            out.extend_from_slice(&w.to_be_bytes());
        }
        out.truncate(self.out_len);
        out
    }
}

fn compress(h: &mut [u64; 8], block: &[u8; 128]) {
    let mut w = [0u64; 80];
    for (i, chunk) in block.chunks_exact(8).enumerate() {
        let mut b = [0u8; 8];
        b.copy_from_slice(chunk);
        w[i] = u64::from_be_bytes(b);
    }
    for i in 16..80 {
        let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
        let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = *h;
    for i in 0..80 {
        let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K512[i]).wrapping_add(w[i]);
        let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (slot, v) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
        *slot = slot.wrapping_add(v);
    }
}

/// FIPS 180-4 SHA-512.
pub fn sha512(data: &[u8]) -> [u8; 64] {
    let mut s = Sha512::new();
    s.update(data);
    let v = s.finalize_vec();
    let mut out = [0u8; 64];
    out.copy_from_slice(&v);
    out
}

/// FIPS 180-4 SHA-384.
pub fn sha384(data: &[u8]) -> [u8; 48] {
    let mut s = Sha512::new_384();
    s.update(data);
    let v = s.finalize_vec();
    let mut out = [0u8; 48];
    out.copy_from_slice(&v);
    out
}

fn hmac_sha2_512_family(new: fn() -> Sha512, key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut k = [0u8; 128];
    if key.len() > 128 {
        let mut h = new();
        h.update(key);
        let d = h.finalize_vec();
        k[..d.len()].copy_from_slice(&d);
    } else {
        k[..key.len()].copy_from_slice(key);
    }
    let mut ipad = [0x36u8; 128];
    let mut opad = [0x5cu8; 128];
    for i in 0..128 {
        ipad[i] ^= k[i];
        opad[i] ^= k[i];
    }
    let mut inner = new();
    inner.update(&ipad);
    inner.update(data);
    let inner_d = inner.finalize_vec();
    let mut outer = new();
    outer.update(&opad);
    outer.update(&inner_d);
    outer.finalize_vec()
}

/// RFC 2104 HMAC-SHA-384.
pub fn hmac_sha384(key: &[u8], data: &[u8]) -> [u8; 48] {
    let v = hmac_sha2_512_family(Sha512::new_384, key, data);
    let mut out = [0u8; 48];
    out.copy_from_slice(&v);
    out
}

/// RFC 2104 HMAC-SHA-512.
pub fn hmac_sha512(key: &[u8], data: &[u8]) -> [u8; 64] {
    let v = hmac_sha2_512_family(Sha512::new, key, data);
    let mut out = [0u8; 64];
    out.copy_from_slice(&v);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }

    #[test]
    fn fips_180_4_known_answers() {
        assert_eq!(hex(&sha512(b"abc")), "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
        assert_eq!(hex(&sha384(b"abc")), "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7");
        assert_eq!(hex(&sha512(b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")), "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909");
        assert_eq!(hex(&sha512(&[b'a'; 1000])), "67ba5535a46e3f86dbfbed8cbbaf0125c76ed549ff8b0b9e03e0c88cf90fa634fa7b12b47d77b694de488ace8d9a65967dc96df599727d3292a8d9d447709c97");
        // Streaming across odd chunk boundaries equals one-shot.
        let data: Vec<u8> = (0..1000u32).map(|i| (i * 7 + 3) as u8).collect();
        let mut s = Sha512::new();
        for chunk in data.chunks(37) {
            s.update(chunk);
        }
        assert_eq!(s.finalize_vec(), sha512(&data).to_vec());
    }

    #[test]
    fn rfc_4231_hmac_known_answers() {
        assert_eq!(hex(&hmac_sha384(&[0x0b; 20], b"Hi There")), "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6");
        assert_eq!(
            hex(&hmac_sha512(&[0xaa; 131], b"Test Using Larger Than Block-Size Key - Hash Key First")),
            "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"
        );
    }
}
