//! Checks `obend-keccak` against a reference written from the FIPS 202 and SP 800-185 algorithms,
//! published NIST answers, an independent corpus (hashlib and PyCryptodome), and the 95 tags the
//! Lean `KMAC256` specification is tested against.

use obend_keccak::{
    cshake256, cshake256_32, keccak_f1600, kmac256_32, left_encode, right_encode, sha3_256,
    sha3_512, shake256_32, shake256_into, Cshake256, KeccakSponge, Kmac256, Midstate, Shake128,
    Shake256, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS, SHAKE128_RATE_BYTES,
    SHAKE256_RATE_BYTES,
};

const VECTORS: &str = include_str!("vectors/sp800_185.txt");

const MESSAGE_SEED: u8 = 1;
const NAME_SEED: u8 = 2;
const CUSTOM_SEED: u8 = 3;
const KEY_SEED: u8 = 4;

struct SplitMix(u64);

impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }

    fn state(&mut self) -> [u64; 25] {
        std::array::from_fn(|_| self.next())
    }
}

/// FIPS 202 Algorithm 5, `rc(t)`.
fn fips_rc(t: usize) -> u64 {
    let mut r: u16 = 1;
    for _ in 0..t % 255 {
        r <<= 1;
        if r & 0x100 != 0 {
            r ^= 0x171;
        }
    }
    u64::from(r & 1)
}

/// The round constant FIPS 202 Algorithm 6 xors into lane `(0, 0)`.
fn fips_round_constant(round: usize) -> u64 {
    (0..7).fold(0, |acc, j| {
        acc | (fips_rc(j + 7 * round) << ((1usize << j) - 1))
    })
}

/// The rotation offsets FIPS 202 Algorithm 2 walks out, indexed by `x + 5 * y`.
fn fips_rotation_offsets() -> [u32; 25] {
    let mut offsets = [0u32; 25];
    let (mut x, mut y) = (1usize, 0usize);
    for t in 0..24u32 {
        offsets[x + 5 * y] = ((t + 1) * (t + 2) / 2) % 64;
        (x, y) = (y, (2 * x + 3 * y) % 5);
    }
    offsets
}

/// Keccak-f[1600] as the step mappings theta, rho, pi, chi, and iota of FIPS 202 §3.2.
fn reference_f1600(state: &mut [u64; 25]) {
    let rotations = fips_rotation_offsets();
    let at = |x: usize, y: usize| x % 5 + 5 * (y % 5);
    for round in 0..24 {
        let parity: [u64; 5] =
            std::array::from_fn(|x| (0..5).fold(0, |acc, y| acc ^ state[at(x, y)]));
        let theta: [u64; 25] = std::array::from_fn(|i| {
            state[i] ^ parity[(i + 4) % 5] ^ parity[(i + 1) % 5].rotate_left(1)
        });
        let mut moved = [0u64; 25];
        for (source, (&lane, &rotation)) in theta.iter().zip(&rotations).enumerate() {
            let (x, y) = (source % 5, source / 5);
            moved[at(y, 2 * x + 3 * y)] = lane.rotate_left(rotation);
        }
        *state = std::array::from_fn(|i| {
            let (x, y) = (i % 5, i / 5);
            moved[i] ^ (!moved[at(x + 1, y)] & moved[at(x + 2, y)])
        });
        state[0] ^= fips_round_constant(round);
    }
}

fn reference_sponge(rate: usize, suffix: u8, message: &[u8], out_len: usize) -> Vec<u8> {
    let mut padded = message.to_vec();
    padded.push(suffix);
    if suffix & 0x80 != 0 {
        padded.push(0); // The final padding bit must follow the delimited suffix.
    }
    padded.resize(padded.len().next_multiple_of(rate), 0);
    *padded.last_mut().expect("padding is non-empty") ^= 0x80;
    let mut state = [0u64; 25];
    for block in padded.chunks_exact(rate) {
        for (lane, bytes) in state.iter_mut().zip(block.as_chunks::<8>().0) {
            *lane ^= u64::from_le_bytes(*bytes);
        }
        reference_f1600(&mut state);
    }
    let mut out = Vec::with_capacity(out_len + rate);
    loop {
        for lane in &state[..rate / 8] {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        if out.len() >= out_len {
            out.truncate(out_len);
            return out;
        }
        reference_f1600(&mut state);
    }
}

fn reference_be(value: u64) -> Vec<u8> {
    let bytes = value.to_be_bytes();
    let skip = bytes.iter().take(7).take_while(|&&b| b == 0).count();
    bytes[skip..].to_vec()
}

fn reference_left_encode(value: u64) -> Vec<u8> {
    let bytes = reference_be(value);
    [vec![bytes.len() as u8], bytes].concat()
}

fn reference_right_encode(value: u64) -> Vec<u8> {
    let bytes = reference_be(value);
    let width = bytes.len() as u8;
    [bytes, vec![width]].concat()
}

fn reference_encode_string(string: &[u8]) -> Vec<u8> {
    [
        reference_left_encode(8 * string.len() as u64),
        string.to_vec(),
    ]
    .concat()
}

fn reference_bytepad(x: &[u8], width: usize) -> Vec<u8> {
    let mut z = [reference_left_encode(width as u64), x.to_vec()].concat();
    z.resize(z.len().next_multiple_of(width), 0);
    z
}

fn reference_cshake256(name: &[u8], custom: &[u8], message: &[u8], out_len: usize) -> Vec<u8> {
    if name.is_empty() && custom.is_empty() {
        return reference_sponge(SHAKE256_RATE_BYTES, 0x1f, message, out_len);
    }
    let strings = [
        reference_encode_string(name),
        reference_encode_string(custom),
    ]
    .concat();
    let prefix = reference_bytepad(&strings, SHAKE256_RATE_BYTES);
    reference_sponge(
        SHAKE256_RATE_BYTES,
        0x04,
        &[prefix, message.to_vec()].concat(),
        out_len,
    )
}

fn reference_kmac256(key: &[u8], custom: &[u8], message: &[u8], out_len: usize) -> Vec<u8> {
    reference_kmac256_bits(key, custom, message, 8 * out_len as u64)
}

fn reference_kmac256_bits(key: &[u8], custom: &[u8], message: &[u8], bits: u64) -> Vec<u8> {
    let framed = [
        reference_bytepad(&reference_encode_string(key), SHAKE256_RATE_BYTES),
        message.to_vec(),
        reference_right_encode(bits),
    ]
    .concat();
    let mut out = reference_cshake256(b"KMAC", custom, &framed, bits.div_ceil(8) as usize);
    if !bits.is_multiple_of(8) {
        *out.last_mut().expect("a partial byte") &= (1u8 << (bits % 8)) - 1;
    }
    out
}

fn absorb_in_pieces(rng: &mut SplitMix, data: &[u8], mut absorb: impl FnMut(&[u8])) {
    let mut rest = data;
    while !rest.is_empty() {
        let take = 1 + rng.below(rest.len().min(150));
        let (head, tail) = rest.split_at(take);
        absorb(head);
        rest = tail;
    }
}

fn squeeze_in_pieces(
    rng: &mut SplitMix,
    len: usize,
    mut squeeze: impl FnMut(&mut [u8]),
) -> Vec<u8> {
    let mut out = vec![0u8; len];
    let mut rest = out.as_mut_slice();
    while !rest.is_empty() {
        let take = 1 + rng.below(rest.len().min(150));
        let (head, tail) = std::mem::take(&mut rest).split_at_mut(take);
        squeeze(head);
        rest = tail;
    }
    out
}

fn pattern(seed: u8, len: usize) -> Vec<u8> {
    (0..len)
        .map(|i| (usize::from(seed) + 131 * i + (i >> 3)) as u8)
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> Vec<u8> {
    assert_eq!(text.len() % 2, 0, "odd hex length");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).expect("hex digit"))
        .collect()
}

fn check_tag(line: &str, expected: &str, out: &[u8]) {
    let actual = if expected.starts_with("h:") {
        format!("h:{}", hex(&sha3_256(out)))
    } else {
        hex(out)
    };
    assert_eq!(actual, expected, "{line}");
}

#[test]
fn tables_match_the_fips_202_generators() {
    let round_constants: [u64; 24] = std::array::from_fn(fips_round_constant);
    assert_eq!(KECCAK_ROUND_CONSTANTS, round_constants);
    assert_eq!(KECCAK_ROTATION_OFFSETS, fips_rotation_offsets());
}

#[test]
fn permutation_matches_the_published_zero_state_answer() {
    let expected: [u64; 25] = [
        0xf125_8f79_40e1_dde7,
        0x84d5_ccf9_33c0_478a,
        0xd598_261e_a65a_a9ee,
        0xbd15_4730_6f80_494d,
        0x8b28_4e05_6253_d057,
        0xff97_a42d_7f8e_6fd4,
        0x90fe_e5a0_a446_47c4,
        0x8c5b_da0c_d619_2e76,
        0xad30_a6f7_1b19_059c,
        0x3093_5ab7_d08f_fc64,
        0xeb5a_a93f_2317_d635,
        0xa9a6_e626_0d71_2103,
        0x81a5_7c16_dbcf_555f,
        0x43b8_31cd_0347_c826,
        0x01f2_2f1a_11a5_569f,
        0x05e5_635a_21d9_ae61,
        0x64be_fef2_8cc9_70f2,
        0x6136_7095_7bc4_6611,
        0xb87c_5a55_4fd0_0ecb,
        0x8c3e_e88a_1ccf_32c8,
        0x940c_7922_ae3a_2614,
        0x1841_f924_a2c5_09e4,
        0x16f5_3526_e704_65c2,
        0x75f6_44e9_7f30_a13b,
        0xeaf1_ff7b_5cec_a249,
    ];
    let mut state = [0u64; 25];
    keccak_f1600(&mut state);
    assert_eq!(state, expected);
    let mut reference = [0u64; 25];
    reference_f1600(&mut reference);
    assert_eq!(reference, expected);
}

#[test]
fn permutation_matches_the_reference_on_random_states() {
    let mut rng = SplitMix(0x6b65_6363_616b);
    for _ in 0..2_000 {
        let start = rng.state();
        let (mut fast, mut reference) = (start, start);
        keccak_f1600(&mut fast);
        reference_f1600(&mut reference);
        assert_eq!(fast, reference, "start state {start:x?}");
    }
}

#[test]
fn encoders_match_sp800_185() {
    let cases: [(u64, &[u8]); 8] = [
        (0, &[0]),
        (1, &[1]),
        (136, &[136]),
        (255, &[255]),
        (256, &[1, 0]),
        (65_535, &[255, 255]),
        (65_536, &[1, 0, 0]),
        (u64::MAX, &[255; 8]),
    ];
    for (value, big_endian) in cases {
        let mut encoded = [0u8; 9];
        let len = left_encode(value, &mut encoded);
        assert_eq!(usize::from(encoded[0]), big_endian.len());
        assert_eq!(&encoded[1..len], big_endian);
        assert_eq!(encoded[..len], reference_left_encode(value)[..]);
        let len = right_encode(value, &mut encoded);
        assert_eq!(&encoded[..len - 1], big_endian);
        assert_eq!(usize::from(encoded[len - 1]), big_endian.len());
        assert_eq!(encoded[..len], reference_right_encode(value)[..]);
    }
}

#[test]
fn bytepad_stream_matches_the_reference() {
    for first_len in [0, 1, 31, 32, 128, 129, 130, 131, 132, 136, 265, 266, 300] {
        let first = pattern(NAME_SEED, first_len);
        let mut s1 = KeccakSponge::<SHAKE256_RATE_BYTES>::new(0x04);
        s1.absorb_bytepad_1(&first);
        let mut ref1 = KeccakSponge::<SHAKE256_RATE_BYTES>::new(0x04);
        ref1.absorb(&reference_bytepad(
            &reference_encode_string(&first),
            SHAKE256_RATE_BYTES,
        ));
        assert_eq!(s1.position(), 0, "|first| = {first_len}");
        assert_eq!(s1.lanes(), ref1.lanes(), "|first| = {first_len}");

        for second_len in [0, 1, 129, 136] {
            let second = pattern(CUSTOM_SEED, second_len);
            let mut s2 = KeccakSponge::<SHAKE256_RATE_BYTES>::new(0x04);
            s2.absorb_bytepad_2(&first, &second);
            let strings = [
                reference_encode_string(&first),
                reference_encode_string(&second),
            ]
            .concat();
            let mut ref2 = KeccakSponge::<SHAKE256_RATE_BYTES>::new(0x04);
            ref2.absorb(&reference_bytepad(&strings, SHAKE256_RATE_BYTES));
            assert_eq!(
                s2.position(),
                0,
                "|first| = {first_len}, |second| = {second_len}"
            );
            assert_eq!(
                s2.lanes(),
                ref2.lanes(),
                "|first| = {first_len}, |second| = {second_len}"
            );
        }
    }
}

#[test]
fn xofs_match_the_reference_across_rate_boundaries() {
    let mut rng = SplitMix(0x7370_6f6e_6765);
    let names: [&[u8]; 3] = [b"", b"KMAC", &[0x5a; 140]];
    let customs: [&[u8]; 4] = [b"", b"Email Signature", &[0xa5; 129], &[0x3c; 265]];
    let out_lens = [0, 1, 32, 135, 136, 137, 168, 169, 272, 400];
    for len in (0..=345).chain([407, 408, 409, 543, 544, 545]) {
        let message = rng.bytes(len);
        let out_len = out_lens[len % out_lens.len()];

        let mut shake128 = Shake128::new();
        absorb_in_pieces(&mut rng, &message, |piece| shake128.absorb(piece));
        assert_eq!(
            squeeze_in_pieces(&mut rng, out_len, |piece| shake128.squeeze(piece)),
            reference_sponge(SHAKE128_RATE_BYTES, 0x1f, &message, out_len),
            "SHAKE128 |M| = {len}, out {out_len}"
        );

        let mut shake256 = Shake256::new();
        absorb_in_pieces(&mut rng, &message, |piece| shake256.absorb(piece));
        assert_eq!(
            squeeze_in_pieces(&mut rng, out_len, |piece| shake256.squeeze(piece)),
            reference_sponge(SHAKE256_RATE_BYTES, 0x1f, &message, out_len),
            "SHAKE256 |M| = {len}, out {out_len}"
        );

        let name = names[len % names.len()];
        let custom = customs[len % customs.len()];
        let mut cshake = Cshake256::new(name, custom);
        absorb_in_pieces(&mut rng, &message, |piece| cshake.absorb(piece));
        assert_eq!(
            squeeze_in_pieces(&mut rng, out_len, |piece| cshake.squeeze(piece)),
            reference_cshake256(name, custom, &message, out_len),
            "cSHAKE256 |N| = {}, |S| = {}, |M| = {len}, out {out_len}",
            name.len(),
            custom.len()
        );
    }
}

#[test]
fn every_cshake_customization_shape_matches_the_reference() {
    let message = pattern(MESSAGE_SEED, 137);
    for name_len in [0, 1, 4, 127, 128, 129, 130, 131, 132, 136, 140, 265, 266] {
        for custom_len in [
            0, 1, 15, 125, 126, 127, 128, 129, 130, 136, 137, 262, 265, 266,
        ] {
            let name = pattern(NAME_SEED, name_len);
            let custom = pattern(CUSTOM_SEED, custom_len);
            let mut xof = Cshake256::new(&name, &custom);
            xof.absorb(&message);
            let mut out = [0u8; 64];
            xof.squeeze(&mut out);
            assert_eq!(
                out[..],
                reference_cshake256(&name, &custom, &message, 64)[..],
                "|N| = {name_len}, |S| = {custom_len}"
            );
        }
    }
}

#[test]
fn one_shots_match_the_reference() {
    let mut rng = SplitMix(0x6f6e_6573_686f);
    for len in [0, 1, 71, 72, 73, 135, 136, 137, 271, 272, 273, 409] {
        let message = rng.bytes(len);
        assert_eq!(
            sha3_256(&message)[..],
            reference_sponge(SHAKE256_RATE_BYTES, 0x06, &message, 32)[..]
        );
        assert_eq!(
            sha3_512(&message)[..],
            reference_sponge(72, 0x06, &message, 64)[..]
        );
        assert_eq!(
            shake256_32(&message)[..],
            reference_sponge(SHAKE256_RATE_BYTES, 0x1f, &message, 32)[..]
        );
        let mut out = [0u8; 200];
        shake256_into(&message, &mut out);
        assert_eq!(
            out[..],
            reference_sponge(SHAKE256_RATE_BYTES, 0x1f, &message, 200)[..]
        );
        for custom in [&b""[..], b"OBEND.CRYPTO.FS.ABSORB/v1"] {
            assert_eq!(
                cshake256_32(custom, &message)[..],
                reference_cshake256(b"", custom, &message, 32)[..]
            );
            cshake256(custom, &message, &mut out);
            assert_eq!(out[..], reference_cshake256(b"", custom, &message, 200)[..]);
        }
    }
}

#[test]
fn kmac_matches_the_reference_for_every_framing_boundary() {
    let mut rng = SplitMix(0x6b6d_6163);
    for key_len in [0, 1, 32, 128, 130, 131, 132, 136, 137, 200, 267, 268] {
        for custom_len in [0, 13, 126, 127, 140] {
            for len in [0, 3, 132, 133, 134, 135, 136, 137, 268, 269, 270, 409] {
                let key = pattern(KEY_SEED, key_len);
                let custom = pattern(CUSTOM_SEED, custom_len);
                let message = rng.bytes(len);
                for out_len in [32, 64, 137] {
                    let mut mac = Kmac256::new(&key, &custom);
                    absorb_in_pieces(&mut rng, &message, |piece| mac.absorb(piece));
                    let mut tag = vec![0u8; out_len];
                    mac.finalize(&mut tag);
                    assert_eq!(
                        tag,
                        reference_kmac256(&key, &custom, &message, out_len),
                        "|K| = {key_len}, |S| = {custom_len}, |X| = {len}, L = {}",
                        8 * out_len
                    );
                }
                assert_eq!(
                    kmac256_32(&key, &custom, &message)[..],
                    reference_kmac256(&key, &custom, &message, 32)[..]
                );
            }
        }
    }
}

#[test]
fn kmac_output_length_is_domain_separating() {
    let mut short = [0u8; 32];
    let mut long = [0u8; 64];
    Kmac256::new(b"key", b"custom").finalize(&mut short);
    Kmac256::new(b"key", b"custom").finalize(&mut long);
    assert_ne!(short[..], long[..32]);
}

#[test]
fn kmac_bit_lengths_match_the_reference() {
    let key = pattern(KEY_SEED, 32);
    let custom = pattern(CUSTOM_SEED, 13);
    for len in [0, 3, 133, 134, 136] {
        let message = pattern(MESSAGE_SEED, len);
        for bits in [
            0u64, 1, 4, 7, 8, 9, 15, 16, 100, 255, 256, 257, 511, 512, 1088, 1089,
        ] {
            let mut mac = Kmac256::new(&key, &custom);
            mac.absorb(&message);
            let mut out = vec![0xff; bits.div_ceil(8) as usize];
            mac.finalize_bits(&mut out, bits);
            assert_eq!(
                out,
                reference_kmac256_bits(&key, &custom, &message, bits),
                "|X| = {len}, L = {bits}"
            );
        }
    }
}

#[test]
#[should_panic(expected = "output buffer must hold exactly the requested bits")]
fn kmac_bit_length_must_match_the_buffer() {
    Kmac256::new(b"key", b"").finalize_bits(&mut [0; 2], 17);
}

#[test]
fn midstates_resume_exactly_at_rate_boundaries() {
    let mut rng = SplitMix(0x6d69_6473_7461);
    for blocks in 0..4 {
        for tail_len in [0, 1, 7, 8, 135, 136, 137, 300] {
            let tail = rng.bytes(tail_len);

            let head = rng.bytes(blocks * SHAKE128_RATE_BYTES);
            let mut shake128 = Shake128::new();
            shake128.absorb(&head);
            let midstate = shake128.midstate().expect("rate boundary");
            let mut resumed = Shake128::from_midstate(&midstate);
            resumed.absorb(&tail);
            shake128.absorb(&tail);
            assert_eq!(resumed.finalize_32(), shake128.finalize_32());

            let head = rng.bytes(blocks * SHAKE256_RATE_BYTES);
            let mut shake256 = Shake256::new();
            shake256.absorb(&head);
            let midstate = shake256.midstate().expect("rate boundary");
            let mut resumed = Shake256::from_midstate(&midstate);
            resumed.absorb(&tail);
            shake256.absorb(&tail);
            assert_eq!(resumed.finalize_32(), shake256.finalize_32());

            for (name, custom) in [
                (&b""[..], &b""[..]),
                (b"", b"Email Signature"),
                (b"KMAC", b""),
                (b"KMAC", &[0x3c; 140]),
            ] {
                let mut cshake = Cshake256::new(name, custom);
                cshake.absorb(&head);
                let midstate = cshake.midstate().expect("rate boundary");
                let rebuilt = Midstate::new(*midstate.lanes(), midstate.suffix());
                let mut resumed = Cshake256::from_midstate(&rebuilt);
                resumed.absorb(&tail);
                let mut one_shot = Vec::with_capacity(head.len() + tail.len());
                one_shot.extend_from_slice(&head);
                one_shot.extend_from_slice(&tail);
                assert_eq!(
                    resumed.finalize_32()[..],
                    reference_cshake256(name, custom, &one_shot, 32)[..]
                );
            }

            let key = rng.bytes(32 + blocks * 40);
            let keyed = Kmac256::new(&key, b"OBEND.KMAC/v1");
            let midstate = keyed
                .midstate()
                .expect("the key block ends on a rate boundary");
            let mut resumed = Kmac256::from_midstate(&midstate);
            resumed.absorb(&tail);
            let mut tag = [0u8; 32];
            resumed.finalize(&mut tag);
            assert_eq!(tag, kmac256_32(&key, b"OBEND.KMAC/v1", &tail));
        }
    }
}

#[test]
fn midstate_is_refused_off_a_boundary_and_after_squeezing() {
    let mut xof = Cshake256::customized(b"domain");
    assert!(xof.midstate().is_some());
    xof.absorb(&[0]);
    assert!(xof.midstate().is_none());
    xof.absorb(&[0; SHAKE256_RATE_BYTES - 1]);
    assert!(xof.midstate().is_some());
    xof.squeeze(&mut [0; SHAKE256_RATE_BYTES]);
    assert!(xof.midstate().is_none());
}

#[test]
fn delimited_suffix_can_fill_the_last_byte_of_a_block() {
    for len in [134, 135, 136, 271] {
        let message = pattern(MESSAGE_SEED, len);
        for suffix in [0x7f, 0x80, 0xff] {
            let mut sponge = obend_keccak::KeccakSponge::<136>::new(suffix);
            sponge.absorb(&message);
            assert_eq!(
                sponge.finalize_32().as_slice(),
                reference_sponge(136, suffix, &message, 32)
            );
        }
    }
}

#[test]
fn padded_lanes_are_what_the_final_permutation_consumes() {
    for len in [0, 1, 7, 8, 134, 135] {
        let message = pattern(MESSAGE_SEED, len);
        let mut xof = Cshake256::customized(b"domain");
        xof.absorb(&message);
        assert_eq!(xof.position(), len);
        let mut lanes = xof.padded_lanes();
        keccak_f1600(&mut lanes);
        let mut expected = [0u8; 32];
        for (bytes, lane) in expected.as_chunks_mut::<8>().0.iter_mut().zip(lanes) {
            *bytes = lane.to_le_bytes();
        }
        assert_eq!(xof.finalize_32(), expected);
    }
}

#[test]
fn nist_cshake256_samples() {
    let mut out = [0u8; 64];
    cshake256(b"Email Signature", &[0, 1, 2, 3], &mut out);
    assert_eq!(
        hex(&out),
        "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1\
         64020e2be0560858d9c00c037e34a96937c561a74c412bb4c746469527281c8c"
    );
    let message: Vec<u8> = (0..=0xc7).collect();
    cshake256(b"Email Signature", &message, &mut out);
    assert_eq!(
        hex(&out),
        "07dc27b11e51fbac75bc7b3c1d983e8b4b85fb1defaf218912ac864302730917\
         27f42b17ed1df63e8ec118f04b23633c1dfb1574c8fb55cb45da8e25afb092bb"
    );
}

#[test]
fn independent_corpus() {
    let mut checked = 0;
    let key: Vec<u8> = (0x40..0x60).collect();
    for line in VECTORS.lines().filter(|line| !line.starts_with('#')) {
        let fields: Vec<&str> = line.split(' ').collect();
        let number = |i: usize| fields[i].parse::<usize>().expect("length field");
        match fields[0] {
            "shake128" | "shake256" => {
                let message = pattern(MESSAGE_SEED, number(1));
                let mut out = vec![0u8; number(2)];
                if fields[0] == "shake128" {
                    let mut xof = Shake128::new();
                    xof.absorb(&message);
                    xof.squeeze(&mut out);
                } else {
                    shake256_into(&message, &mut out);
                }
                check_tag(line, fields[3], &out);
            }
            "sha3_256" => {
                check_tag(
                    line,
                    fields[2],
                    &sha3_256(&pattern(MESSAGE_SEED, number(1))),
                );
            }
            "sha3_512" => {
                check_tag(
                    line,
                    fields[2],
                    &sha3_512(&pattern(MESSAGE_SEED, number(1))),
                );
            }
            "cshake256" => {
                let name = pattern(NAME_SEED, number(1));
                let custom = pattern(CUSTOM_SEED, number(2));
                let mut xof = Cshake256::new(&name, &custom);
                xof.absorb(&pattern(MESSAGE_SEED, number(3)));
                let mut out = vec![0u8; number(4)];
                xof.squeeze(&mut out);
                check_tag(line, fields[5], &out);
            }
            "kmac256" => {
                let mut mac = Kmac256::new(
                    &pattern(KEY_SEED, number(1)),
                    &pattern(CUSTOM_SEED, number(2)),
                );
                mac.absorb(&pattern(MESSAGE_SEED, number(3)));
                let mut out = vec![0u8; number(4)];
                mac.finalize(&mut out);
                check_tag(line, fields[5], &out);
            }
            "kmac256_bits" => {
                let bits = number(4) as u64;
                let mut mac = Kmac256::new(
                    &pattern(KEY_SEED, number(1)),
                    &pattern(CUSTOM_SEED, number(2)),
                );
                mac.absorb(&pattern(MESSAGE_SEED, number(3)));
                let mut out = vec![0xff; bits.div_ceil(8) as usize];
                mac.finalize_bits(&mut out, bits);
                check_tag(line, fields[5], &out);
            }
            "nist_kmac256" => {
                let message: Vec<u8> = (0..number(2)).map(|i| i as u8).collect();
                let custom = if fields[3] == "-" {
                    Vec::new()
                } else {
                    unhex(fields[3])
                };
                let mut mac = Kmac256::new(&key, &custom);
                mac.absorb(&message);
                let mut out = vec![0u8; fields[4].len() / 2];
                mac.finalize(&mut out);
                check_tag(line, fields[4], &out);
            }
            "lean" | "acvp_key" | "acvp_custom" | "acvp_message" | "mini_cshake" | "mini_kmac"
            | "mini_midstate" => continue,
            other => panic!("unknown vector kind {other}"),
        }
        checked += 1;
    }
    assert_eq!(checked, 42 + 42 + 21 + 21 + 324 + 378 + 84 + 3);
}

#[test]
fn verified_lean_kmac_corpus() {
    let field = |kind: &str| -> Vec<u8> {
        let line = VECTORS
            .lines()
            .find(|line| line.split(' ').next() == Some(kind))
            .expect("ACVP field");
        unhex(line.split(' ').nth(1).expect("hex field"))
    };
    let range = |n: usize| -> Vec<u8> { (0..n).map(|i| i as u8).collect() };
    let customs = [Vec::new(), b"OBEND.KMAC/v1".to_vec(), range(140)];
    let mut vectors = Vec::new();
    for key_len in [0, 32, 128, 136, 200] {
        for custom in &customs {
            for len in [0, 3, 133, 134, 136, 409] {
                let message = if len == 3 {
                    b"abc".to_vec()
                } else {
                    range(len)
                };
                vectors.push((range(key_len), custom.clone(), message));
            }
        }
    }
    let vector_key: Vec<u8> = (0x40..0x60).collect();
    vectors.push((
        vector_key.clone(),
        b"My Tagged Application".to_vec(),
        vec![0, 1, 2, 3],
    ));
    vectors.push((
        vector_key,
        b"DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".to_vec(),
        b"abc".to_vec(),
    ));
    vectors.push((range(32), Vec::new(), range(132)));
    vectors.push((range(32), Vec::new(), range(135)));
    vectors.push((
        field("acvp_key"),
        field("acvp_custom"),
        field("acvp_message"),
    ));

    let tags: Vec<&str> = VECTORS
        .lines()
        .filter_map(|line| line.strip_prefix("lean "))
        .collect();
    assert_eq!((tags.len(), vectors.len()), (95, 95));
    for ((key, custom, message), tag) in vectors.iter().zip(tags) {
        assert_eq!(
            hex(&kmac256_32(key, custom, message)),
            tag,
            "|K| = {}, |S| = {}, |X| = {}",
            key.len(),
            custom.len(),
            message.len()
        );
    }
}

/// minidregg's seeded byte strings (`seeded` in `scripts/kernel-vectors.lean`).
fn minidregg_seeded(seed: u64, len: usize) -> Vec<u8> {
    let mut state = seed.wrapping_mul(2_654_435_761).wrapping_add(12_345);
    (0..len)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) as u8
        })
        .collect()
}

fn minidregg_field(field: &str) -> Vec<u8> {
    if field == "-" {
        return Vec::new();
    }
    if let Some(literal) = field.strip_prefix("x:") {
        return unhex(literal);
    }
    let (seed, len) = field
        .strip_prefix("s:")
        .and_then(|rest| rest.split_once(':'))
        .expect("seeded field");
    minidregg_seeded(
        seed.parse().expect("seed"),
        len.parse().expect("seeded length"),
    )
}

/// minidregg's serialized midstate: the lanes without the unabsorbed tail, the padding suffix,
/// then the tail.
fn minidregg_midstate(xof: &Cshake256, suffix: u8, absorbed: &[u8]) -> Vec<u8> {
    let tail = &absorbed[absorbed.len() - xof.position()..];
    let mut lanes = *xof.lanes();
    for (i, &byte) in tail.iter().enumerate() {
        lanes[i / 8] ^= u64::from(byte) << (8 * (i % 8));
    }
    let mut out: Vec<u8> = lanes.iter().flat_map(|lane| lane.to_le_bytes()).collect();
    out.push(suffix);
    out.extend_from_slice(tail);
    out
}

#[test]
fn minidregg_lean_vectors() {
    let (mut cshakes, mut kmacs, mut midstates) = (0, 0, 0);
    for line in VECTORS.lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        match fields[0] {
            "mini_cshake" => {
                let (custom, input) = (minidregg_field(fields[1]), minidregg_field(fields[2]));
                assert_eq!(hex(&cshake256_32(&custom, &input)), fields[3], "{line}");
                cshakes += 1;
            }
            "mini_kmac" => {
                let key = minidregg_field(fields[1]);
                let custom = minidregg_field(fields[2]);
                let input = minidregg_field(fields[3]);
                assert_eq!(hex(&kmac256_32(&key, &custom, &input)), fields[4], "{line}");
                kmacs += 1;
            }
            "mini_midstate" => {
                let custom = minidregg_field(fields[1]);
                let prefix = minidregg_field(fields[2]);
                let suffix = minidregg_field(fields[3]);
                let domain = if custom.is_empty() { 0x1f } else { 0x04 };
                let mut xof = Cshake256::customized(&custom);
                xof.absorb(&prefix);
                assert_eq!(xof.position(), prefix.len() % SHAKE256_RATE_BYTES);
                let serialized = minidregg_midstate(&xof, domain, &prefix);
                assert_eq!(hex(&sha3_256(&serialized)), fields[4], "{line}");
                if let Some(midstate) = xof.midstate() {
                    assert_eq!(midstate.suffix(), domain);
                    let mut resumed = Cshake256::from_midstate(&midstate);
                    resumed.absorb(&suffix);
                    assert_eq!(hex(&resumed.finalize_32()), fields[5], "{line}");
                }
                xof.absorb(&suffix);
                assert_eq!(hex(&xof.finalize_32()), fields[5], "{line}");
                midstates += 1;
            }
            _ => {}
        }
    }
    assert_eq!((cshakes, kmacs, midstates), (32, 32, 21));
}
