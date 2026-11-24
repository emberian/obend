//! Independent known-answer and Wycheproof conformance for the pure-Rust signature engines
//! (`curves`, `rsa`, `ed25519`). Vectors: C2SP/wycheproof `testvectors_v1` (see each
//! `tests/vectors/*.txt` header) and pyca/cryptography 50.0.2 signatures generated 2026-11-22.

use obend_oracles_e2ee::{
    verify_ecdsa_raw, verify_signature, FixtureSigner, SignatureAlgorithm, SubjectPublicKey,
};

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[derive(Default, Debug)]
struct Tally {
    valid_ok: usize,
    invalid_rejected: usize,
    acceptable: usize,
}

/// Run one Wycheproof file. `raw` selects fixed-width `r ‖ s` (P1363) ECDSA decoding.
fn run_wycheproof(text: &str, alg: SignatureAlgorithm, raw: bool) -> Tally {
    let mut tally = Tally::default();
    let mut key: Option<SubjectPublicKey> = None;
    for line in text.lines() {
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split(' ').collect();
        match parts[0] {
            "K" => key = SubjectPublicKey::from_spki_der(&unhex(parts[1])).ok(),
            "T" => {
                let (tc, result, msg, sig) = (parts[1], parts[2], unhex(parts[3]), unhex(parts[4]));
                let ok = key.as_ref().is_some_and(|k| {
                    if raw {
                        verify_ecdsa_raw(k, alg, &msg, &sig).is_ok()
                    } else {
                        verify_signature(k, alg, &msg, &sig).is_ok()
                    }
                });
                match result {
                    "valid" => {
                        assert!(ok, "wycheproof tcId {tc} ({alg:?}) valid signature refused");
                        tally.valid_ok += 1;
                    }
                    "invalid" => {
                        assert!(
                            !ok,
                            "wycheproof tcId {tc} ({alg:?}) INVALID signature accepted"
                        );
                        tally.invalid_rejected += 1;
                    }
                    _ => tally.acceptable += 1,
                }
            }
            other => panic!("bad vector line tag {other}"),
        }
    }
    tally
}

macro_rules! wycheproof_test {
    ($name:ident, $file:literal, $alg:expr, $raw:expr, $valid:expr, $invalid:expr) => {
        #[test]
        fn $name() {
            let t = run_wycheproof(include_str!(concat!("vectors/", $file)), $alg, $raw);
            assert_eq!(
                (t.valid_ok, t.invalid_rejected),
                ($valid, $invalid),
                "{t:?}"
            );
        }
    };
}

wycheproof_test!(
    wycheproof_ecdsa_p256_sha256_der,
    "wycheproof_ecdsa_secp256r1_sha256.txt",
    SignatureAlgorithm::EcdsaP256Sha256,
    false,
    174,
    310
);
wycheproof_test!(
    wycheproof_ecdsa_p384_sha384_der,
    "wycheproof_ecdsa_secp384r1_sha384.txt",
    SignatureAlgorithm::EcdsaP384Sha384,
    false,
    194,
    310
);
wycheproof_test!(
    wycheproof_ecdsa_p256_sha256_p1363,
    "wycheproof_ecdsa_secp256r1_sha256_p1363.txt",
    SignatureAlgorithm::EcdsaP256Sha256,
    true,
    173,
    89
);
wycheproof_test!(
    wycheproof_ecdsa_p384_sha384_p1363,
    "wycheproof_ecdsa_secp384r1_sha384_p1363.txt",
    SignatureAlgorithm::EcdsaP384Sha384,
    true,
    193,
    87
);
wycheproof_test!(
    wycheproof_ed25519,
    "wycheproof_ed25519.txt",
    SignatureAlgorithm::Ed25519,
    false,
    117,
    64
);
wycheproof_test!(
    wycheproof_rsa_pkcs1_2048_sha256,
    "wycheproof_rsa_signature_2048_sha256.txt",
    SignatureAlgorithm::RsaPkcs1Sha256,
    false,
    9,
    249
);
wycheproof_test!(
    wycheproof_rsa_pss_2048_sha256_s32,
    "wycheproof_rsa_pss_2048_sha256_mgf1_32.txt",
    SignatureAlgorithm::RsaPssSha256,
    false,
    63,
    45
);
wycheproof_test!(
    wycheproof_rsa_pss_4096_sha384_s48,
    "wycheproof_rsa_pss_4096_sha384_mgf1_48.txt",
    SignatureAlgorithm::RsaPssSha384,
    false,
    95,
    46
);

/// pyca/cryptography (OpenSSL) ECDSA signatures with random nonces: verify-only KATs, plus
/// RFC 6979 deterministic signatures that our fixture signer must reproduce byte-for-byte.
#[test]
fn pyca_ecdsa_known_answers() {
    let msg = b"obend-w10-kat";
    for (alg, spki, sig, det, d) in [
        (SignatureAlgorithm::EcdsaP256Sha256, "3059301306072a8648ce3d020106082a8648ce3d030107034200044ecd9c2b544155d77702389f22fe31aa9715006608e95eb067378d58a9a4ef03681d6bca5ff99aa6677c29d94f2264571ac5fdd210fb740bb99351814edf49e8", "3045022100f7c101a9a061f3441d9ec47b3fd138b9b0449448d50dbeb005d88a5e854dc5a602206d7d511d7979243d20b0dce02442851597dd51bea0da68bdd6d408bf935d60a8", "3046022100bc3bb850fbd7b86b39b47b73f71a98aa9ad6116345f887b5b9e5fb4ef07f9a6d022100a3b5bb0bf56debf7624063ceafa76cd9e9a66a79d3c5e7b657bbb64ce924d247", "3c7af1478e4f2f1669a5de361e723fb1c5e0d5e19191d984c719b6b8cee78c49"),
        (SignatureAlgorithm::EcdsaP384Sha384, "3076301006072a8648ce3d020106052b81040022036200045ace74c2115b370012fbb2e6bade28d0de7dbac146da66a48bcff2d17abbb3333abc458d3d54c7ee9cb47fce0de64e9d4862fd2e041f40303f6243d959025034380d1d210b4ab4282c662cd3527512b7a835f3c43aba914841d29b94f61fd962", "306402303fc842930756f2816fede3773398d34bb9529c83bb88eb714da227911f552c40bc68ebbe96e869485bcd030f10508cd4023058f463700df4ee87a49948bfe1b6ac56e5fdb77d95d66521ba3dd414045c7c48f2f9997f4331fc5779c2f3100fa44620", "306502303894984ae1f8cd045306cdaa550e1de39ce969e9067da74de8c28b44442b3a83eb1efc7328a0aeb51f5f639288f2d655023100c69a791f5d6dce38de97d16d76728d5704d5e92e6fb64c7d6fc0f0bc4ed5dbf8dbe6fe97d04b2f456f85e24417296d26", "233f023c7f171fee2e6ef89fb32f6a97b68799b45c895b348daf64b396ba5dd080d223233fec490ccdeb61c790849ded"),
    ] {
        let pk = SubjectPublicKey::from_spki_der(&unhex(spki)).unwrap();
        assert_eq!(pk.to_spki_der(), unhex(spki));
        assert!(verify_signature(&pk, alg, msg, &unhex(sig)).is_ok());
        assert!(verify_signature(&pk, alg, msg, &unhex(det)).is_ok());
        assert!(verify_signature(&pk, alg, b"obend-w10-kaT", &unhex(sig)).is_err());
        let d = unhex(d);
        let signer = match alg {
            SignatureAlgorithm::EcdsaP256Sha256 => FixtureSigner::p256_from_scalar(&d),
            _ => FixtureSigner::p384_from_scalar(&d),
        }
        .unwrap();
        assert_eq!(signer.public_key(), pk);
        assert_eq!(signer.sign(alg, msg), unhex(det));
    }
    for spki in ["302a300506032b6570032100edfd61a6106c382c3bba3877a8ffd3c400e8e0723caabed246b134585c345ac0", "30820122300d06092a864886f70d01010105000382010f003082010a0282010100b2c81c7a32d85a620460f183a602d1bf2c480579140bd96097a577b08b19f9488c2fe730f1a4646d77e1aae4cf9d1696c29dad21cb252cd3efcf2f6fe7243978ff68ee910497da3055a725c3adf2c418f14de85f7156a8bf9994c2fe14cd420e1930749ca079189209c5868ea06704dbd87bb185798ceb3f868d7fb26ed45bf6836267704bff319d13630519c7264f7280b7c80c86e00aa7714e0006c567f4c48f22be4a00e7a23b0aeaf2a4e967e0163582f918805ec1c2b4e2cdd67fc299eac5dd9b81e40f3476c5bc0a29d4e3b0f18a7046e8468790dfeb8bf77ce6374a4a3756d71f74a687e822bdbfe908946d460b51af5e0509a9746827038d703466630203010001"] {
        let pk = SubjectPublicKey::from_spki_der(&unhex(spki)).unwrap();
        assert_eq!(pk.to_spki_der(), unhex(spki));
    }
}
