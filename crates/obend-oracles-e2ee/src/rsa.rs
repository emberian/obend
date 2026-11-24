//! RFC 8017 RSA signature verification: RSASSA-PKCS1-v1_5 (§8.2.2, SHA-256 / SHA-384 DigestInfo)
//! and RSASSA-PSS (§8.1.2, MGF1 with the message hash), moduli 2048..=4096 bits, over the
//! generic [`crate::bigint::Mont`] engine (`N = 64` limbs). Pure Rust, zero external crates.
//!
//! PKCS#1 v1.5 verification re-encodes the expected `EM = 00 01 FF…FF 00 ‖ DigestInfo ‖ H` and
//! compares all `k` bytes in constant time, so Bleichenbacher-2006 `e = 3` forgeries that hide
//! garbage after (or inside) the DigestInfo are refused by construction (no ASN.1 parsing of
//! attacker-controlled padding).

use crate::bigint::{limbs_bits, limbs_from_be, limbs_ge, Limbs, Mont};
use crate::curves::{CryptoError, HashAlg};
use obend_primitives::ct::ct_eq;

const LIMBS: usize = 64;
pub const RSA_MIN_BITS: usize = 2048;
pub const RSA_MAX_BITS: usize = 4096;

/// RFC 8017 §9.2 note 1 DigestInfo prefixes.
const DIGEST_INFO_SHA256: &[u8] = &[
    0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05,
    0x00, 0x04, 0x20,
];
const DIGEST_INFO_SHA384: &[u8] = &[
    0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05,
    0x00, 0x04, 0x30,
];

fn modulus(n: &[u8]) -> Result<(Limbs<LIMBS>, usize), CryptoError> {
    if n.is_empty() || n[0] == 0 {
        return Err(CryptoError::RsaModulusSize);
    }
    let n_l = limbs_from_be::<LIMBS>(n).ok_or(CryptoError::RsaModulusSize)?;
    let bits = limbs_bits(&n_l);
    if !(RSA_MIN_BITS..=RSA_MAX_BITS).contains(&bits) || n_l[0] & 1 == 0 {
        return Err(CryptoError::RsaModulusSize);
    }
    Ok((n_l, bits))
}

/// Validate an RSA public key: canonical big-endian `n` and `e` (no leading zero octets),
/// `2048 <= |n| <= 4096`, `n` odd, `e` odd, `3 <= e < n`.
pub fn validate_public_key(n: &[u8], e: &[u8]) -> Result<(), CryptoError> {
    let (n_l, _) = modulus(n)?;
    if e.is_empty() || e[0] == 0 || e.len() > n.len() {
        return Err(CryptoError::RsaBadExponent);
    }
    let e_l = limbs_from_be::<LIMBS>(e).ok_or(CryptoError::RsaBadExponent)?;
    if e_l[0] & 1 == 0 || limbs_bits(&e_l) < 2 || limbs_ge(&e_l, &n_l) {
        return Err(CryptoError::RsaBadExponent);
    }
    Ok(())
}

/// RSAVP1: `m = s^e mod n` as exactly `k` bytes, after length and range checks.
fn public_op(n: &[u8], e: &[u8], sig: &[u8]) -> Result<(Vec<u8>, usize), CryptoError> {
    validate_public_key(n, e)?;
    let (n_l, bits) = modulus(n)?;
    let k = bits.div_ceil(8);
    if sig.len() != k {
        return Err(CryptoError::BadSignatureLength);
    }
    let s = limbs_from_be::<LIMBS>(sig).ok_or(CryptoError::RsaSignatureOutOfRange)?;
    if limbs_ge(&s, &n_l) {
        return Err(CryptoError::RsaSignatureOutOfRange);
    }
    let m = Mont::<LIMBS>::new(n_l).ok_or(CryptoError::RsaModulusSize)?;
    let out = m.pow_be(&m.to_mont(&s), e);
    Ok((m.to_be(&out, k), bits))
}

fn emsa_pkcs1v15_encode(hash: HashAlg, msg: &[u8], k: usize) -> Result<Vec<u8>, CryptoError> {
    let prefix = match hash {
        HashAlg::Sha256 => DIGEST_INFO_SHA256,
        HashAlg::Sha384 => DIGEST_INFO_SHA384,
    };
    let t_len = prefix.len() + hash.output_len();
    if k < t_len + 11 {
        return Err(CryptoError::RsaModulusSize);
    }
    let mut em = Vec::with_capacity(k);
    em.extend_from_slice(&[0x00, 0x01]);
    em.extend(std::iter::repeat_n(0xffu8, k - t_len - 3));
    em.push(0x00);
    em.extend_from_slice(prefix);
    em.extend_from_slice(&hash.digest(msg));
    Ok(em)
}

/// RSASSA-PKCS1-v1_5 verification (RFC 8017 §8.2.2) by exact re-encoding comparison.
pub fn verify_pkcs1v15(
    n: &[u8],
    e: &[u8],
    hash: HashAlg,
    msg: &[u8],
    sig: &[u8],
) -> Result<(), CryptoError> {
    let (em, _) = public_op(n, e, sig)?;
    let expected = emsa_pkcs1v15_encode(hash, msg, em.len())?;
    if ct_eq(&em, &expected) {
        Ok(())
    } else {
        Err(CryptoError::BadPadding)
    }
}

fn mgf1(hash: HashAlg, seed: &[u8], len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len + hash.output_len());
    let mut counter = 0u32;
    while out.len() < len {
        let mut block = seed.to_vec();
        block.extend_from_slice(&counter.to_be_bytes());
        out.extend_from_slice(&hash.digest(&block));
        counter += 1;
    }
    out.truncate(len);
    out
}

fn pss_m_prime_hash(hash: HashAlg, msg: &[u8], salt: &[u8]) -> Vec<u8> {
    let mut m_prime = vec![0u8; 8];
    m_prime.extend_from_slice(&hash.digest(msg));
    m_prime.extend_from_slice(salt);
    hash.digest(&m_prime)
}

/// RSASSA-PSS verification (RFC 8017 §8.1.2 / §9.1.2) with MGF1(`hash`) and fixed `salt_len`.
pub fn verify_pss(
    n: &[u8],
    e: &[u8],
    hash: HashAlg,
    msg: &[u8],
    sig: &[u8],
    salt_len: usize,
) -> Result<(), CryptoError> {
    let bad = CryptoError::BadPadding;
    let (em_full, mod_bits) = public_op(n, e, sig)?;
    let em_bits = mod_bits - 1;
    let em_len = em_bits.div_ceil(8);
    let k = em_full.len();
    // I2OSP(m, emLen): when emLen < k the leading octet must be zero.
    if k > em_len && em_full[0] != 0 {
        return Err(bad);
    }
    let em = &em_full[k - em_len..];
    let h_len = hash.output_len();
    let min_em = h_len
        .checked_add(salt_len)
        .and_then(|v| v.checked_add(2))
        .ok_or(bad)?;
    if em_len < min_em || em[em_len - 1] != 0xbc {
        return Err(bad);
    }
    let db_len = em_len - h_len - 1;
    let (masked_db, rest) = em.split_at(db_len);
    let hh = &rest[..h_len];
    let zero_bits = 8 * em_len - em_bits;
    if zero_bits > 0 && masked_db[0] & (0xffu8 << (8 - zero_bits)) != 0 {
        return Err(bad);
    }
    let mut db: Vec<u8> = masked_db
        .iter()
        .zip(mgf1(hash, hh, db_len))
        .map(|(a, b)| a ^ b)
        .collect();
    if zero_bits > 0 {
        db[0] &= 0xffu8 >> zero_bits;
    }
    let ps_len = em_len - h_len - salt_len - 2;
    if db[..ps_len].iter().any(|&b| b != 0) || db[ps_len] != 0x01 {
        return Err(bad);
    }
    let salt = &db[ps_len + 1..];
    if ct_eq(hh, &pss_m_prime_hash(hash, msg, salt)) {
        Ok(())
    } else {
        Err(CryptoError::SignatureMismatch)
    }
}

// ---------------------------------------------------------------------------
// Embedded fixture keys (generated 2026-11-22 with pyca/cryptography 50.0.2; test-only)
// ---------------------------------------------------------------------------

/// Embedded RSA fixture key (`e = 65537`). Test/fixture use only — the private exponent is public.
pub struct FixtureRsaKey {
    n_hex: &'static [&'static str],
    d_hex: &'static [&'static str],
}

fn unhex(parts: &[&str]) -> Vec<u8> {
    let s: String = parts.concat();
    let s = if s.len() % 2 == 1 { format!("0{s}") } else { s };
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("fixture hex"))
        .collect()
}

impl FixtureRsaKey {
    pub fn n(&self) -> Vec<u8> {
        unhex(self.n_hex)
    }

    fn private_op(&self, em: &[u8]) -> Vec<u8> {
        let n = self.n();
        let (n_l, bits) = modulus(&n).expect("fixture modulus");
        let m = Mont::<LIMBS>::new(n_l).expect("odd modulus");
        let x = m.from_be_strict(em).expect("EM < n");
        let s = m.pow_be(&x, &unhex(self.d_hex));
        m.to_be(&s, bits.div_ceil(8))
    }
}

pub(crate) fn fixture_key(bits: usize) -> Option<&'static FixtureRsaKey> {
    match bits {
        2048 => Some(&RSA2048),
        3072 => Some(&RSA3072),
        4096 => Some(&RSA4096),
        _ => None,
    }
}

pub(crate) fn fixture_sign_pkcs1v15(key: &FixtureRsaKey, hash: HashAlg, msg: &[u8]) -> Vec<u8> {
    let k = key.n().len();
    key.private_op(&emsa_pkcs1v15_encode(hash, msg, k).expect("modulus large enough"))
}

/// Deterministic PSS (salt = first hLen bytes of `H(tag ‖ msg)`), salt length = hLen.
pub(crate) fn fixture_sign_pss(key: &FixtureRsaKey, hash: HashAlg, msg: &[u8]) -> Vec<u8> {
    let n = key.n();
    let (_, mod_bits) = modulus(&n).expect("fixture modulus");
    let k = n.len();
    let em_bits = mod_bits - 1;
    let em_len = em_bits.div_ceil(8);
    let h_len = hash.output_len();
    let mut tagged = b"OBEND.FIXTURE.PSS.SALT/v1".to_vec();
    tagged.extend_from_slice(msg);
    let salt = hash.digest(&tagged);
    let hh = pss_m_prime_hash(hash, msg, &salt);
    let db_len = em_len - h_len - 1;
    let mut db = vec![0u8; db_len - salt.len() - 1];
    db.push(0x01);
    db.extend_from_slice(&salt);
    let mut masked: Vec<u8> = db
        .iter()
        .zip(mgf1(hash, &hh, db_len))
        .map(|(a, b)| a ^ b)
        .collect();
    let zero_bits = 8 * em_len - em_bits;
    if zero_bits > 0 {
        masked[0] &= 0xffu8 >> zero_bits;
    }
    let mut em = vec![0u8; k - em_len];
    em.extend_from_slice(&masked);
    em.extend_from_slice(&hh);
    em.push(0xbc);
    key.private_op(&em)
}

pub(crate) static RSA2048: FixtureRsaKey = FixtureRsaKey {
    n_hex: &[
        "b2c81c7a32d85a620460f183a602d1bf2c480579140bd96097a577b08b19f9488c2fe730f1a4646d77e1aae4cf9d1696",
        "c29dad21cb252cd3efcf2f6fe7243978ff68ee910497da3055a725c3adf2c418f14de85f7156a8bf9994c2fe14cd420e",
        "1930749ca079189209c5868ea06704dbd87bb185798ceb3f868d7fb26ed45bf6836267704bff319d13630519c7264f72",
        "80b7c80c86e00aa7714e0006c567f4c48f22be4a00e7a23b0aeaf2a4e967e0163582f918805ec1c2b4e2cdd67fc299ea",
        "c5dd9b81e40f3476c5bc0a29d4e3b0f18a7046e8468790dfeb8bf77ce6374a4a3756d71f74a687e822bdbfe908946d46",
        "0b51af5e0509a9746827038d70346663",
    ],
    d_hex: &[
        "1e15dc7e187054b31c32ab04234df62725a5a6c6202e0bffc9ce5573a6f4e36e543b4497f5a45b4b3e5a700e95c60e37",
        "15290a72b0d172fc099cbf6edc3da7c092960158aaa65a0f03a41646d0cef07eb8e5e5adf32b922350a071390c1df554",
        "4a08dfbb6061499eee53bf25981d2bb1dc7a0691166ec74339715af2bc018e37f573e62fdd1a0fc9799c57244d9b0861",
        "04a0f21d1117a83229a53a6785e1fc690cc8f41ffe273b4f3026b4f3fb9b86b3cc8464a16a7d23748cb732f52b0a9594",
        "320e8db5abfae55f8d129bf46405c44aa274a968b6a0e789ffa8dba04c586920c5d1ddaf961bc4e377cc490487368a36",
        "6950c12441d163af4edf7840e5632f9",
    ],
};

pub(crate) static RSA3072: FixtureRsaKey = FixtureRsaKey {
    n_hex: &[
        "9df076740132716dc36cb351b2a8d755fc56a4846638549056afc10b9bab3c1eb07b47c2176ebb2deccc2abefe12ebab",
        "a1324532492af0b258d7beaf046c8b735f6199007516a7f6070f3e0241eddfa4a2625573ac6c63d2803e319ff133398b",
        "e6d27c71f7062b682d526ba9891441eecb7ec2a6c37b22638f328c26f1749f723274c1aaf7704aaaca993f6dbddbd039",
        "b23a965b61bc5904ac6eb5927812461a293126b2d295fc44817d9392f6d6d45333abf8e1c761811b7cb3c7abd684827e",
        "05c2c7f516acf1dc27f33c1f8380b55b9921108e5adc81bc59fcbef099180464097c792baa8a571453e29a276879f2a4",
        "7a7d5539f7f47acf42ca4d28ec0014014b8edaf45a867573fb97abb9d66ad528b6ac54884dc0b83bc1fdbf544c1a9d1d",
        "c7b95986241d02c58b9293d64656828c2364713984af2c1c8e75c46273241d3a73e6cdf9ad5bef5a494256bfc1fcdecb",
        "5d05066250acdca39cfc4b2bea1a6aa14a0391c7b66b668a2fcc88aaba25424e0070dc344bcf0ea7e8e55d2cdb937ee7",
    ],
    d_hex: &[
        "f4854d5edc5b947133961f29e548b1da560a6e3aed6758c4fef0ac17a4b2bf296461f8feedf869a2f8723fdbe2d0b83d",
        "c81b64362e4164d539e70b393bc8313e35f58c43c1038a96c4e73c4192810d367e916f6adf10109bde206c040c121a8e",
        "1696da4437063e3dd3ad3f32032071d39b0a6da2721339729a48cfe39affcbbba9924a24bf6202b7d962d968b60093a8",
        "3fdfa4d965bf8cb247a43f48bccccdebc2ca6df77d40e887c752fc1f143a160f9a782da2a064bcd62982cd27a5bf11a6",
        "4b0555864b5eede36872b16b3e33499110212fbaa31bdd7f663c1648911fa73972d51366ec84c3657cca8a06df756112",
        "da75d243834c3c9752fac298341f2ae4a322a5be780e267b0a0696982773ab5ce1361bfadceb00c888aee02e7d0ce5d9",
        "c40d3bad2d59a8a4802cadacf6983d05d870bd6d3b7fa897c5e119fef191ecbf19e5d64a09f2d0dd7c5c2cf6d4c5730a",
        "c73bc7c23bae25eabbb4c7391a349385a0091165d0795a5d4477577d264fcc577a955bce4a3182c09eaa94b93639239",
    ],
};

pub(crate) static RSA4096: FixtureRsaKey = FixtureRsaKey {
    n_hex: &[
        "da07bd2c530b5bbb4dfde31de870490da803c2b9d6d7ca34b84344b9c59ecb53ad28dfcc6c8aa37c8df1c7d04403a446",
        "9952e89904505e30b37a7e5217e87f05309400307c1e8c405ca9444e7aabb9546317847a72b467feb31bf0d28d6ab7f3",
        "903db8842147b456d91f91026efa4033e1b46f8eb020251298aae463d1c73d4516becf3c7aedd0668bc2c45b9fa4ea37",
        "3cb1735b0021d57f2ffdee8943d1385cc4eaea08e9a1ab400442fadd4db2cbf8f8fd85fea0d306ffb03bf7616433ead4",
        "d55303716c3d53f4c4214ffa805afd8c1082275c28d4fc2922790cd463225665cb083fc00d95cc858a0f869f4b513c5a",
        "ea9aa4532eb3dcdeea948183bf23a21c8a43617b30ce3602dab905243af2a95cb03411e521762d8eb1e58f212d603b6b",
        "0e83bee161602aec8905d7654999db0adf2899019fe8a808f3ff4d949242e4772f7d4055a449ebc89145cd72b1078432",
        "733654e2a9e6152abe2aedf67b1c92c6ca4177f27522a35db91a1c56651604b98b5bb6d6851b8aafbf705ac1a16f7183",
        "796ed4c22110dfff503395378c49e898dde7758513c6abd42d84bc674b38cc055f6cf865c53943f7ab03ebd94fba7212",
        "36e739f2a7a9c95136a3ae35053539b1e3476c0a8a17183fa8b294c05d5cba4af12ac03ac71184d63a2fab6d7b69b642",
        "486947c6c15d7f6e26260fba9265301d3a925e773fe39c246b4eb9da2f4012f5",
    ],
    d_hex: &[
        "4769e5829128d5410288b84d6186f5c6ad539e0274e6756ad337e558dbebe9395d2c58318313ddfcbc19879325d3f388",
        "d44b9db810fba9fe55ab3798f80fc51b141046079b7ffdfc4edd7a6c222e01242cd8d521ae547d03a5f2eeec68399e4a",
        "fee1d8801ece77b942a0de4467c93c2242397198d103966102f4669e7365c921ca137199a3c2255291509834529417cb",
        "43ebf396c8f24c15bec873cb2e15675aab7d2e6f00e75d4a389b1fc440e0e182893bb119f7df671974c60f7f2cecfc6b",
        "fdfb94d31fdaee96eb6ee5dd6d11609ef2014f971620bcff5435460882f80a48893a0877857b9d63d816c1c78749f274",
        "ed06fdefe90a2cbc2f25b94e47db0a0ba83dfc948c977b9b9c2cf1e658ec71a3429bcdf7149211e7563890194d994909",
        "4ffcda1735b40a510262b8c8bf91fe604b1f794508e752e91d191ac482aa2bdad6b94aa65ebb10c67b1841dfa09c61d9",
        "c74ec76ec0629c4f2a69ec424ebd5b3ab9bf4bbf63ad1d30c8d75d8e6fecf2cd7d71b01a907eab8e679115809cd403ff",
        "b837c1f8d91f3ac65b8fae81c06c7e74cb4694edd2732c7d1c1bb233513834057edcc9f615f815b4145b3e17edc1be7b",
        "3595b32956a0d9ab47693ef575ef52f0db270521b9615f2f118d9c4d13b88553d9543f7b4602dc23efae21a1654d46c7",
        "f42a8bfda2167ed14bef181863b27db16ba1623a83606f3d772a1d804cba7739",
    ],
};

#[cfg(test)]
mod tests {
    use super::*;

    fn h(s: &str) -> Vec<u8> {
        unhex(&[s])
    }
    const E65537: &[u8] = &[1, 0, 1];
    const MSG: &[u8] = b"obend-w10-kat";

    /// External KATs signed by pyca/cryptography 50.0.2 (OpenSSL backend), independent of this code.
    #[test]
    fn external_known_answers() {
        assert!(verify_pkcs1v15(&RSA2048.n(), E65537, HashAlg::Sha256, MSG, &h("356b9f2cc3d7a2db8acb1dc00185e8003d99ca0f58fe4388e9d8855181d07c089e993f5f45d697a2488c49782d82ddec4f26ab8d7ca5981c50c7aa0f0739e58add3408b0f4313ea5fd790685854da7f63bfbdab5125d04a78cd7091a57f4a764b2e1d7d55411be34ab821a94304bab2cce992072a1763ff520ff1065a2384b46090a6a04be660a1f80f64ab7e4f9fe9b2e74212009fefe4e0ad0228963c2fe5cd8858aa140046059097664ebe220152a22e0617cd34501082c596c7db99cf51bdb80654e82e7db9d06a0d7539ac9c757d57b4729027b6e8abe4894c9943e57c6776d8aec2083ea799fa0e4658cc2e34186216be461bc08b43fc6e3f5d70b09f8")).is_ok());
        assert!(verify_pkcs1v15(&RSA3072.n(), E65537, HashAlg::Sha384, MSG, &h("4d6fa70ded9cf4c56c5f00ff623d7187df53f592d17ccd670377beb6a7ec647a453b8b0e6cec641129cfa6ad9dd0edbd6f0d85a5ed902ace70ff7361aab7ab9911b10c09f89b796743e9094c1538ab066798b54e28d71b05b362270e76b9291c9ec84f78636595c6397ddb2217ed62732e21e74c6774a0320581651eb6ebf90a4ab4a42d3ea2429041cea6d3137dd080e7fddc6a269bc6bda4726b3cee216a98e85d2c360effbc3d42d6e04988fa522d3ac4e8885866c2be45daf719801be5afd336f5c846dcb348aa583fa34e6e93e70a9aab652e0ecc7edc7acf8ae9c4f34caa92dc13af5b924578503fa31eb296dc07f51b57d28f45a1baeba12e4912f3d04b313d785c3a5af9fbb6c5fff41041d175315cd9a74688d2a00bed79f30e27e2028aaa1d1dc47da36e23246c4c14c69314351c2cd19101a78b990c4c723bf3bf59d8b0ee5a597ef516bff26cc5e36aa336a6dbd1e1acc8f54767c53d731f9907c60b59f9c1387062d1e9e5b5f24eb993826e69ff67211153cdaad65512eca2dc")).is_ok());
        assert!(verify_pss(&RSA4096.n(), E65537, HashAlg::Sha384, MSG, &h("556da0bec92ed6319b6d64ce2c339ca18be001f6c4c96cf734d46a7ced62318a539024f3bc87838374c70f945491370eed64a1fa0a29cf27d286f5748f3501cb2c3f3c13017ee0ed7ac076b4f4911872fcb07c09407887c62e9e68e6460fefee5fe44db8d5d01f69d71fbd55e65827a89ad6b29a5ca05c07926a3278df4ec687d441fd72e268b6eca140e8b8650f8c52a99a517e2d0bcd6e135dc109e99b32919d6b1ce0209c1ff8bd01a07bbce6221d8409047c93a2212b2e02d87ae56d6e3f302e7d223414587a972c18a605625a2aaa518c14a64492a0ecdec0de90f7af5038e616a936853ed03392e22d9132fd50c417bec2818df4e96121dd5ca6200c8cc803d8044402ffdbb9d1d68357ed48330f3bd026288f376c3758dc0c9216363cb37e88531f34ec638d15bf5670292f8c3191eea09d1d3108b60bd348a50a0cac17ad2a88a2a9e10b4de6714ca708e48a8db7be36029719446ff4457ffe279317f885d6dd9dec62042dc910cf237a133cd448f7743601fac7b87578ef5cb3e2a606565c7d375833ea6c2be19e7b75f897390587fc9c351eaa4532bd7171ad8618c235d504bb1abed1c88560da9bb274d3289e69666a20cc604e5a5523b2f6a3c4c6fd7fa23b6635cda7ce1f320e26c485fde47a09c11fa5e5ca191622ce9c9d352c36063310a45d9c9f5d5b22cd07315ab021da43d649ccda00cb5c8712e304ee"), 48).is_ok());
        assert!(verify_pss(&RSA2048.n(), E65537, HashAlg::Sha256, MSG, &h("af17ed1731517e5d29941e3e2dfb2660b476c3235ea10bbfaf21be8140d2289395b35c3e562dc41c90517056a128f459d8be3cb603917ad5741bec751c77bc54e2761789cc9a635e6f93b94a2c0c8c85c1600b0bfbf11fcfab9b3c18f3709dca1d9a23865e56a20d29211019a6f9bdf1a9496419ee5dd9ecfe49aa294436c8efd174caf5444521761da06eada9509e31855d4ed0ebbcee0e5ff6bdeddff7b5c27dd8c84f721b5051782f3a7be864696a124e3ba9f1c49db615759fc74518c51c556460f1f49c89f9303e18e553b1708027df5e34246b7b13b4a4618361d5f312e78bfe04f570e85188d612d724866059eab189d07d3b3576e41e0fcddc55ffed"), 32).is_ok());
        // Wrong hash / wrong message / wrong scheme are refused.
        assert!(verify_pkcs1v15(&RSA2048.n(), E65537, HashAlg::Sha384, MSG, &h("356b9f2cc3d7a2db8acb1dc00185e8003d99ca0f58fe4388e9d8855181d07c089e993f5f45d697a2488c49782d82ddec4f26ab8d7ca5981c50c7aa0f0739e58add3408b0f4313ea5fd790685854da7f63bfbdab5125d04a78cd7091a57f4a764b2e1d7d55411be34ab821a94304bab2cce992072a1763ff520ff1065a2384b46090a6a04be660a1f80f64ab7e4f9fe9b2e74212009fefe4e0ad0228963c2fe5cd8858aa140046059097664ebe220152a22e0617cd34501082c596c7db99cf51bdb80654e82e7db9d06a0d7539ac9c757d57b4729027b6e8abe4894c9943e57c6776d8aec2083ea799fa0e4658cc2e34186216be461bc08b43fc6e3f5d70b09f8")).is_err());
        assert!(verify_pkcs1v15(&RSA2048.n(), E65537, HashAlg::Sha256, b"other", &h("356b9f2cc3d7a2db8acb1dc00185e8003d99ca0f58fe4388e9d8855181d07c089e993f5f45d697a2488c49782d82ddec4f26ab8d7ca5981c50c7aa0f0739e58add3408b0f4313ea5fd790685854da7f63bfbdab5125d04a78cd7091a57f4a764b2e1d7d55411be34ab821a94304bab2cce992072a1763ff520ff1065a2384b46090a6a04be660a1f80f64ab7e4f9fe9b2e74212009fefe4e0ad0228963c2fe5cd8858aa140046059097664ebe220152a22e0617cd34501082c596c7db99cf51bdb80654e82e7db9d06a0d7539ac9c757d57b4729027b6e8abe4894c9943e57c6776d8aec2083ea799fa0e4658cc2e34186216be461bc08b43fc6e3f5d70b09f8")).is_err());
        assert!(verify_pss(&RSA2048.n(), E65537, HashAlg::Sha256, MSG, &h("356b9f2cc3d7a2db8acb1dc00185e8003d99ca0f58fe4388e9d8855181d07c089e993f5f45d697a2488c49782d82ddec4f26ab8d7ca5981c50c7aa0f0739e58add3408b0f4313ea5fd790685854da7f63bfbdab5125d04a78cd7091a57f4a764b2e1d7d55411be34ab821a94304bab2cce992072a1763ff520ff1065a2384b46090a6a04be660a1f80f64ab7e4f9fe9b2e74212009fefe4e0ad0228963c2fe5cd8858aa140046059097664ebe220152a22e0617cd34501082c596c7db99cf51bdb80654e82e7db9d06a0d7539ac9c757d57b4729027b6e8abe4894c9943e57c6776d8aec2083ea799fa0e4658cc2e34186216be461bc08b43fc6e3f5d70b09f8"), 32).is_err());
        assert!(verify_pkcs1v15(&RSA2048.n(), E65537, HashAlg::Sha256, MSG, &h("af17ed1731517e5d29941e3e2dfb2660b476c3235ea10bbfaf21be8140d2289395b35c3e562dc41c90517056a128f459d8be3cb603917ad5741bec751c77bc54e2761789cc9a635e6f93b94a2c0c8c85c1600b0bfbf11fcfab9b3c18f3709dca1d9a23865e56a20d29211019a6f9bdf1a9496419ee5dd9ecfe49aa294436c8efd174caf5444521761da06eada9509e31855d4ed0ebbcee0e5ff6bdeddff7b5c27dd8c84f721b5051782f3a7be864696a124e3ba9f1c49db615759fc74518c51c556460f1f49c89f9303e18e553b1708027df5e34246b7b13b4a4618361d5f312e78bfe04f570e85188d612d724866059eab189d07d3b3576e41e0fcddc55ffed")).is_err());
    }

    /// Bleichenbacher 2006: for `e = 3` a cube root of `00 01 FF 00 ‖ DigestInfo ‖ H ‖ garbage`
    /// passes a verifier that parses padding and ignores trailing bytes. Genuine `e = 3`
    /// signatures verify; the forgery (computed offline by integer cube root, no private key) must not.
    #[test]
    fn bleichenbacher_e3_forgery_refused() {
        let n = h("ba8a8c60dc64ed2e33aa097da6454de0d83687ed99383e5156fd6122bf941169702a72acc246e384ebcc394ea402539001e7ba99509ea64a48326382d00d2458dd5519d996df4217448fd057b69b3fa2c6f8d249b1fe02b64d68e0d93708c25151c3058111dd0ba9791577f637b40e5740c008b764751ac1c38f1d944ac7701e9c86764e27b096d701b8dfbdf4c3c403de05d04b3330650f7164f7cdd4dd24567c08a931594ffde3aaba2e942e86d6f2aac687955ae66d73d34f2880e8ae5d887b6be325b589c0b95035b693d1bc49ce9065293f0bef3fa0798792a70844fa95801793e1f88b6c53be9cbfa8c40fa325a7554e863751d8706d0dac5cd86c3c05");
        let e3 = [3u8];
        assert!(verify_pkcs1v15(&n, &e3, HashAlg::Sha256, MSG, &h("988614c2f0ca9ad80f6737dae236d22f27a39a47554f6d0f5f0a8813679f047fc96e9f453c09f8ff9bdd2e48063918d9ca2687ba7fcd9909f8bfd228589ebc82372e92949399e43f7ee61c1105fb4cf64ef0a46e572f678be31d3c3d44046c9754152a8e629a9b27969023fb389c1e2d6c60af4eae83992a4b85f9e6cfcfe7f9449308963e0f22f246ea1fb48b14c98a7e64f6c3df113b73830267700d1dc396a0769ff32d80962e2a0e2eefbd0b08c31fb172a7806fa6151d7d4b8cec319fb25e2f7a01c4e7fa49f6addf32bfe1a46134b777db0e6b316ea0681821d07867239aa0fc9c193d22b3cf95b8f52445cddc84eaf2f213700399097f7a0d72651cf3")).is_ok());
        let forged = h("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032c38624845911817bf125c3cf15343cee1389f8cefffb6c17ecc978b62db70432e9fb658f8b7b39dba48c0a6636b15fca097db414040419cd899c19d7397d6a15ab94308a4a5fa8acce1e7fee22a2ab85e4a964be");
        // Tooth: the forgery really does decode to the lax-parser prefix ...
        let (em, _) = public_op(&n, &e3, &forged).unwrap();
        let mut lax_prefix = vec![0x00, 0x01, 0xff, 0x00];
        lax_prefix.extend_from_slice(DIGEST_INFO_SHA256);
        lax_prefix.extend_from_slice(&HashAlg::Sha256.digest(MSG));
        assert!(em.starts_with(&lax_prefix));
        // ... and the strict re-encoding verifier refuses it.
        assert_eq!(
            verify_pkcs1v15(&n, &e3, HashAlg::Sha256, MSG, &forged),
            Err(CryptoError::BadPadding)
        );
    }

    #[test]
    fn fixture_roundtrip_and_range_refusals() {
        for bits in [2048usize, 3072, 4096] {
            let key = fixture_key(bits).unwrap();
            let n = key.n();
            for hash in [HashAlg::Sha256, HashAlg::Sha384] {
                let s1 = fixture_sign_pkcs1v15(key, hash, MSG);
                assert!(verify_pkcs1v15(&n, E65537, hash, MSG, &s1).is_ok());
                let s2 = fixture_sign_pss(key, hash, MSG);
                assert!(verify_pss(&n, E65537, hash, MSG, &s2, hash.output_len()).is_ok());
                let mut flipped = s2.clone();
                flipped[bits / 16] ^= 0x10;
                assert!(verify_pss(&n, E65537, hash, MSG, &flipped, hash.output_len()).is_err());
            }
        }
        let n = RSA2048.n();
        let s = fixture_sign_pkcs1v15(&RSA2048, HashAlg::Sha256, MSG);
        // s >= n, short signature, and prepended zero are refused.
        assert_eq!(
            verify_pkcs1v15(&n, E65537, HashAlg::Sha256, MSG, &n),
            Err(CryptoError::RsaSignatureOutOfRange)
        );
        assert_eq!(
            verify_pkcs1v15(&n, E65537, HashAlg::Sha256, MSG, &s[1..]),
            Err(CryptoError::BadSignatureLength)
        );
        let mut long = vec![0u8];
        long.extend_from_slice(&s);
        assert_eq!(
            verify_pkcs1v15(&n, E65537, HashAlg::Sha256, MSG, &long),
            Err(CryptoError::BadSignatureLength)
        );
        // 1024-bit modulus, even modulus, even exponent, e = 1 are refused.
        let mut small = vec![0x80u8];
        small.extend(std::iter::repeat_n(0u8, 126));
        small.push(1);
        assert_eq!(
            validate_public_key(&small, E65537),
            Err(CryptoError::RsaModulusSize)
        );
        let mut even = n.clone();
        *even.last_mut().unwrap() &= 0xfe;
        assert_eq!(
            validate_public_key(&even, E65537),
            Err(CryptoError::RsaModulusSize)
        );
        assert_eq!(
            validate_public_key(&n, &[2]),
            Err(CryptoError::RsaBadExponent)
        );
        assert_eq!(
            validate_public_key(&n, &[1]),
            Err(CryptoError::RsaBadExponent)
        );
    }
}
