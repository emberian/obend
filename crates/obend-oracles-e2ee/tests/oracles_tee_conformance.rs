#![forbid(unsafe_code)]
//! Conformance, Live-Silicon KAT, & Adversarial Suite for `obend-oracles-e2ee`
//! (`0` external crates, `0` boolean signature shortcuts, `0` synthetic signed preimages):
//! - **Live Silicon & Vendor PKI KATs**:
//!   - Live AWS Nitro Enclaves `COSE_Sign1` capture (`tests/vectors/tee/nitro_att.bin`) + AWS Nitro Root G1.
//!   - Live Chutes Intel TDX DCAP v4 binary Quote (`tests/vectors/tee/chutes_tdx_quote.bin`) + Intel SGX Root CA.
//!   - Live AMD KDS Genoa RSA-4096-PSS `ARK -> ASK` chain (`tests/vectors/tee/amd_genoa_cert_chain.pem`).
//!   - Live NVIDIA Hopper CoRIM VBIOS ISO 19770-2 SWID XML-DSig `.swidtag` + NVIDIA CoRIM Root CA.
//! - **`CAP-24`**: RFC 5280 DER X.509 certificate chains across P-384, P-256, Ed25519, RSA-PSS/PKCS#1.
//! - **`CAP-25`**: AMD SEV-SNP `1184`-byte (`0x4A0`) ABI Table 21/22 `ATTESTATION_REPORT` + real AMD KDS
//!   VCEK OIDs + mandatory ARK-signed DER CRL + 72-byte LE P-384 signature verification.
//! - **`CAP-26`**: Intel TDX DCAP v4/v5 (`48`B `QuoteHeader` + `584`/`648`B `TDQuoteBody` + `384`B QE Report)
//!   and NVIDIA Hopper/Blackwell SPDM 1.1 + RFC 6960 OCSP + ISO 19770-2 SWID XML-DSig CoRIM.
//! - **`V3` & `V4`**: Registry-pinned TLSNotary & `calltree` with real P-256 / Ed25519 notary signatures.
//! - **E2EE Channel Binding & Exact Integer `FHSDD001` / `FHQPB001` KKT Oracle Verifier**.

use std::collections::BTreeMap;

use obend_oracles_e2ee::curves::der_encode;
use obend_oracles_e2ee::kkt::solver_quote_commitment;
use obend_oracles_e2ee::tlsn_e2ee::compute_calltree_root;
use obend_oracles_e2ee::{
    base64_decode_strict, chutes_report_data_binding, extract_der_dice_fwid,
    extract_json_field_strict, fixture_build_amd_snp_report, fixture_build_aws_nitro_cose,
    fixture_build_intel_tdx_quote, fixture_build_nvidia_rim_swid_xml, fixture_issue_cert_der,
    fixture_issue_crl_der, fixture_issue_ocsp_der, fixture_notarize, fixture_sign_spdm_report,
    fold_nitro_pcrs, hex_decode_strict, hex_encode_lower, hkdf_sha256_expand, hkdf_sha256_extract,
    hmac_sha256, notary_key_fingerprint, parse_der_basic_constraints, parse_der_key_usage,
    parse_intel_tdx_quote, parse_pem_cert_records, parse_spdm_gpu_report, sha256,
    verify_amd_sev_snp, verify_attested_solver_quote, verify_aws_nitro, verify_calltree_recording,
    verify_certified_qp, verify_e2ee_channel, verify_ecdsa_raw, verify_intel_tdx,
    verify_nvidia_gpu, verify_rfc5280_cert_chain, verify_sdd_factor_witness, verify_signature,
    verify_tlsn_transcript, verify_zero_kkt_certified_qp, AmdSnpAttestation, AmdSnpCrl,
    AmdSnpPolicy, AmdSnpProduct, AmdSnpTcbVersion, AwsNitroAttestation, AwsNitroPolicy,
    BasicConstraints, CallTreeEdge, CallTreeError, CallTreeHop, CallTreeRecording, CertChainError,
    CertRecord, ChannelDirection, CryptoError, E2eeChannelError, E2eeChannelInput,
    E2eeChannelPolicy, E2eeSessionGuard, ExactQpCertificateBundle, ExactQpCertificateBundleError,
    ExactQpKktCert, ExactQpProblem, ExactSddPsdCertificate, ExactSddPsdCertificateError,
    FixtureCertSpec, FixtureNitroDocFields, FixtureSigner, FixtureSnpReportFields,
    FixtureTdxQuoteFields, GpuArch, IntelTdxAttestation, IntelTdxMeasurementPin, IntelTdxPolicy,
    KeyUsage, NvidiaGpuAttestation, NvidiaGpuPolicy, NvidiaOcspResponse, NvidiaOcspStatus,
    NvidiaRimManifest, OracleError, PinnedNotaryEntry, PinnedNotaryRegistry, QpProblemBindingError,
    SddFactorEdge, SddFactorError, SddFactorWitness, SignatureAlgorithm, SubjectPublicKey,
    TcbPosture, TeeError, TeeVendor, TlsnTranscriptEnvelope, KEY_USAGE_CRL_SIGN,
    KEY_USAGE_DIGITAL_SIGNATURE, KEY_USAGE_KEY_CERT_SIGN, ML_KEM_768_PUBKEY_LEN, NO_SERVICE_TD,
    OPAQUE_CHIP_SKU, OPAQUE_FWID, OPAQUE_PROJECT, OPAQUE_PROJECT_SKU, QP_CERT_EXACT_SCALE,
    SNP_REPORT_LEN,
};

const NOW: u64 = 1_780_000_000;

fn base64_encode_std(input: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let b0 = chunk[0];
        let b1 = if chunk.len() > 1 { chunk[1] } else { 0 };
        let b2 = if chunk.len() > 2 { chunk[2] } else { 0 };
        out.push(TABLE[(b0 >> 2) as usize] as char);
        out.push(TABLE[(((b0 & 0x03) << 4) | (b1 >> 4)) as usize] as char);
        if chunk.len() > 1 {
            out.push(TABLE[(((b1 & 0x0f) << 2) | (b2 >> 6)) as usize] as char);
        } else {
            out.push('=');
        }
        if chunk.len() > 2 {
            out.push(TABLE[(b2 & 0x3f) as usize] as char);
        } else {
            out.push('=');
        }
    }
    out
}

/// Who a fixture certificate names and who signs it.
struct CertIdentity<'a> {
    subject_cn: &'a str,
    issuer_cn: &'a str,
    serial: u8,
    subject_signer: &'a FixtureSigner,
    issuer_signer: &'a FixtureSigner,
    sig_alg: SignatureAlgorithm,
}

fn issue_ca_cert(identity: CertIdentity<'_>, path_len: Option<u8>, crl: bool) -> CertRecord {
    let CertIdentity {
        subject_cn,
        issuer_cn,
        serial,
        subject_signer,
        issuer_signer,
        sig_alg,
    } = identity;
    let bits = KEY_USAGE_KEY_CERT_SIGN | if crl { KEY_USAGE_CRL_SIGN } else { 0 };
    let der = fixture_issue_cert_der(
        &FixtureCertSpec {
            subject_cn,
            issuer_cn,
            serial: &[serial],
            not_before: NOW - 86_400,
            not_after: NOW + 86_400,
            subject_key: subject_signer.public_key(),
            basic_constraints: Some(BasicConstraints {
                is_ca: true,
                path_len_constraint: path_len,
            }),
            key_usage: Some(KeyUsage::new(bits)),
            ocsp_signing_eku: false,
            dice_fwid: None,
            amd_vcek_ext: None,
        },
        issuer_signer,
        sig_alg,
    );
    CertRecord::from_der(&der).expect("valid CA DER certificate")
}

fn issue_leaf_cert(
    identity: CertIdentity<'_>,
    fwid: Option<[u8; 48]>,
    amd_vcek_ext: Option<(AmdSnpTcbVersion, [u8; 64])>,
) -> CertRecord {
    let CertIdentity {
        subject_cn,
        issuer_cn,
        serial,
        subject_signer,
        issuer_signer,
        sig_alg,
    } = identity;
    let der = fixture_issue_cert_der(
        &FixtureCertSpec {
            subject_cn,
            issuer_cn,
            serial: &[serial],
            not_before: NOW - 86_400,
            not_after: NOW + 86_400,
            subject_key: subject_signer.public_key(),
            basic_constraints: Some(BasicConstraints {
                is_ca: false,
                path_len_constraint: None,
            }),
            key_usage: Some(KeyUsage::new(KEY_USAGE_DIGITAL_SIGNATURE)),
            ocsp_signing_eku: false,
            dice_fwid: fwid,
            amd_vcek_ext,
        },
        issuer_signer,
        sig_alg,
    );
    CertRecord::from_der(&der).expect("valid Leaf DER certificate")
}

fn build_signed_spdm_report(
    req_nonce: [u8; 32],
    resp_nonce: [u8; 32],
    measurements: &[(u8, &[u8])],
    opaque: &[(u16, &[u8])],
    gpu_leaf_signer: &FixtureSigner,
) -> Vec<u8> {
    let mut req = vec![0u8; 37];
    req[0] = 0x11;
    req[1] = 0xE0;
    req[4..36].copy_from_slice(&req_nonce);

    let mut rec = Vec::new();
    for &(idx, val) in measurements {
        let dmtf_len = 3 + val.len();
        rec.push(idx);
        rec.push(1);
        rec.extend_from_slice(&(dmtf_len as u16).to_le_bytes());
        rec.push(0x01);
        rec.extend_from_slice(&(val.len() as u16).to_le_bytes());
        rec.extend_from_slice(val);
    }

    let mut opaque_buf = Vec::new();
    for &(ty, val) in opaque {
        opaque_buf.extend_from_slice(&ty.to_le_bytes());
        opaque_buf.extend_from_slice(&(val.len() as u16).to_le_bytes());
        opaque_buf.extend_from_slice(val);
    }

    let mut resp = Vec::new();
    resp.extend_from_slice(&[0x11, 0x60, 0x00, 0x00]);
    resp.push(measurements.len() as u8);
    let rec_len = rec.len();
    resp.push((rec_len & 0xff) as u8);
    resp.push(((rec_len >> 8) & 0xff) as u8);
    resp.push((rec_len >> 16) as u8);
    resp.extend_from_slice(&rec);
    resp.extend_from_slice(&resp_nonce);
    resp.extend_from_slice(&(opaque_buf.len() as u16).to_le_bytes());
    resp.extend_from_slice(&opaque_buf);
    resp.extend_from_slice(&[0u8; 96]);

    let mut full = req;
    full.extend_from_slice(&resp);
    fixture_sign_spdm_report(&mut full, gpu_leaf_signer);
    full
}

// ---------------------------------------------------------------------------
// 0. Crypto KATs & Real Live-Silicon Attestation Captures (Nitro, TDX, AMD Genoa, NVIDIA CoRIM)
// ---------------------------------------------------------------------------

#[test]
fn sha256_hmac_hkdf_kats() {
    assert_eq!(
        hex_encode_lower(&sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        hex_encode_lower(&hmac_sha256(b"Jefe", b"what do ya want for nothing?")),
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    );
    let ikm = [0x0bu8; 22];
    let salt: [u8; 13] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
    ];
    let prk = hkdf_sha256_extract(&salt, &ikm);
    assert_eq!(
        hex_encode_lower(&prk),
        "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
    );
    let okm = hkdf_sha256_expand(
        &prk,
        &[0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9],
    );
    assert_eq!(
        hex_encode_lower(&okm),
        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf"
    );
    let raw = [0x11u8; ML_KEM_768_PUBKEY_LEN];
    let b64 = base64_encode_std(&raw);
    assert_eq!(base64_decode_strict(&b64).unwrap(), raw);
    assert!(base64_decode_strict("AB==").is_none());
}

#[test]
fn real_live_silicon_nitro_tdx_amd_genoa_and_nvidia_corim_captures_verify() {
    // 1. REAL LIVE AWS NITRO ENCLAVES COSE_Sign1 CAPTURE (`us-east-1`, `c5.xlarge`, `user_data=[0xAB; 32]`):
    let nitro_root_pem = include_bytes!("vectors/tee/aws_nitro_root_g1.pem");
    let nitro_root = &parse_pem_cert_records(nitro_root_pem).expect("AWS Nitro Root G1 PEM")[0];
    let real_nitro_bytes = include_bytes!("vectors/tee/nitro_att.bin");
    let expected_nitro_meas: [u8; 32] =
        hex_decode_strict("81c611f35bff79491538b2f7cf201c7597a661a5c549633541c62bdc8af1613f")
            .unwrap()
            .try_into()
            .unwrap();
    let nitro_policy = AwsNitroPolicy {
        pinned_root_sha256: nitro_root.cert_sha256(),
        expected_measurement: expected_nitro_meas,
        max_age_secs: Some(3600),
    };
    let nitro_ev = verify_aws_nitro(
        &nitro_policy,
        &AwsNitroAttestation {
            cose_sign1_bytes: real_nitro_bytes.to_vec(),
        },
        1_783_792_500,
    )
    .expect("real live AWS Nitro Enclaves COSE_Sign1 capture must verify");
    assert_eq!(nitro_ev.report_data_32(), [0xABu8; 32]);
    assert_eq!(nitro_ev.tcb_posture(), TcbPosture::NoPolicyOnPlatform);

    let mut tampered_nitro = real_nitro_bytes.to_vec();
    let mid = tampered_nitro.len() / 2;
    tampered_nitro[mid] ^= 0xFF;
    assert!(verify_aws_nitro(
        &nitro_policy,
        &AwsNitroAttestation {
            cose_sign1_bytes: tampered_nitro
        },
        1_783_792_500
    )
    .is_err());

    // 2. REAL LIVE CHUTES INTEL TDX DCAP v4 BINARY QUOTE (`tests/vectors/tee/chutes_tdx_quote.bin`):
    let intel_root_pem = include_bytes!("vectors/tee/intel_sgx_root_ca.pem");
    let intel_root = &parse_pem_cert_records(intel_root_pem).expect("Intel SGX Root CA PEM")[0];
    let real_tdx_quote = include_bytes!("vectors/tee/chutes_tdx_quote.bin");
    let parsed_q = parse_intel_tdx_quote(real_tdx_quote).expect("parse real Chutes TDX v4 quote");
    assert_eq!(parsed_q.version, 4);
    assert_eq!(parsed_q.signed_quote_len, 632);

    let h48 = |s: &str| -> [u8; 48] { hex_decode_strict(s).unwrap().try_into().unwrap() };
    let tdx_policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256(),
        measurement_pin: IntelTdxMeasurementPin {
            mr_td: h48("261ce538b435e2d0e85fc97e254bc99154c507b7a8e13d59b69f8532384f1d0bfaadfddf3fccc6e0a411203840bbee8d"),
            rt_mr0: h48("ed373dfcc4e3b9cc57282773784c88445699f95705ec0995959c4aa95f9dec454c76da891fa56f820f547b02db8c1f2f"),
            rt_mr1: h48("9b8b2915351a3166f742024edafb6cce244c1df4056eb1f9eb608c3616b9d63729ae00c98d1dc108009c0978b19dc207"),
            rt_mr2: h48("8471360414fe80b4343fb17dd59e442bdc55b5955df0adf610b1de15ad7b454e98fb8e9d38cc188b82369f4f620b6968"),
            pin_rtmr3: None,
        },
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: vec![],
    };
    let tdx_ev = verify_intel_tdx(
        &tdx_policy,
        &IntelTdxAttestation {
            quote_bytes: real_tdx_quote.to_vec(),
            tcb_status: "UpToDate".to_string(),
        },
        1_783_800_000,
    )
    .expect("real live Chutes Intel TDX v4 quote must pass full PCK->QE->AK->Quote crypto");
    assert_eq!(tdx_ev.vendor(), TeeVendor::IntelTdx);

    // 3. REAL AMD KDS GENOA RSA-4096-PSS `ARK -> ASK` CHAIN (`amd_genoa_cert_chain.pem`):
    let amd_genoa_pem = include_bytes!("vectors/tee/amd_genoa_cert_chain.pem");
    let genoa_certs = parse_pem_cert_records(amd_genoa_pem).expect("AMD Genoa KDS PEM");
    assert_eq!(genoa_certs.len(), 2);
    let (genoa_ask, genoa_ark) = (&genoa_certs[0], &genoa_certs[1]);
    assert_eq!(
        hex_encode_lower(&genoa_ark.cert_sha256()),
        "4c6598d19c18719c5dfd4a7d335f674e5bfe1d8f800cea2cf270c10d103db2f1"
    );
    verify_signature(
        genoa_ark.spki(),
        genoa_ark.signature_alg(),
        genoa_ark.tbs_der(),
        genoa_ark.signature_bytes(),
    )
    .expect("real AMD Genoa ARK RSA-4096-PSS self-signature verifies");
    verify_signature(
        genoa_ark.spki(),
        genoa_ask.signature_alg(),
        genoa_ask.tbs_der(),
        genoa_ask.signature_bytes(),
    )
    .expect("real AMD Genoa ASK RSA-4096-PSS signature under ARK verifies");

    // 4. REAL NVIDIA CoRIM VBIOS `.swidtag` (`nvidia_rim_vbios_1010_0200_882_96009F0001.swidtag`):
    //    Full Canonical XML 1.1 + SHA-384 Reference digest + 4-cert NVIDIA CoRIM X.509 chain +
    //    W3C XML-DSig `ecdsa-sha384` signature verification!
    let nv_corim_root_pem = include_bytes!("vectors/tee/nvidia_corim_root_ca.pem");
    let nv_corim_root = &parse_pem_cert_records(nv_corim_root_pem).expect("NVIDIA CoRIM Root")[0];
    let real_vbios_swid =
        include_bytes!("vectors/tee/nvidia_rim_vbios_1010_0200_882_96009F0001.swidtag");
    let verified_rim = obend_oracles_e2ee::verify_nvidia_rim_swid(
        real_vbios_swid,
        &nv_corim_root.cert_sha256(),
        1_783_800_000,
    )
    .expect("real NVIDIA Hopper GH100 VBIOS CoRIM .swidtag must pass C14N + X.509 + ECDSA-P384");
    assert_eq!(verified_rim.product(), "GH100");
    assert_eq!(verified_rim.colloquial_version(), "96.00.9F.00.01");
    assert_eq!(verified_rim.cert_chain_root_to_leaf().len(), 4);
    assert_eq!(verified_rim.active_measurements().len(), 12);
    assert_eq!(verified_rim.active_measurements()[&13].len(), 4);

    let mut tampered_swid = real_vbios_swid.to_vec();
    let idx = tampered_swid
        .windows(14)
        .position(|w| w == b"96.00.9F.00.01")
        .unwrap();
    tampered_swid[idx] = b'8';
    assert_eq!(
        obend_oracles_e2ee::verify_nvidia_rim_swid(
            &tampered_swid,
            &nv_corim_root.cert_sha256(),
            1_783_800_000,
        ),
        Err(TeeError::ReportSignatureInvalid)
    );
}

// ---------------------------------------------------------------------------
// 1. CAP-24: Real DER X.509 Chains + TBS Tamper / Wrong Key / Spliced SPKI / Scalar / Subgroup Refusals
// ---------------------------------------------------------------------------

#[test]
fn cap24_rfc5280_real_x509_chains_and_cryptographic_forgery_refusals() {
    assert_eq!(
        parse_der_basic_constraints(&[0x30, 0x06, 0x01, 0x01, 0xFF, 0x02, 0x01, 0x01]),
        Some(BasicConstraints {
            is_ca: true,
            path_len_constraint: Some(1)
        })
    );
    assert_eq!(
        parse_der_basic_constraints(&[0x30, 0x00]),
        Some(BasicConstraints {
            is_ca: false,
            path_len_constraint: None
        })
    );
    assert!(parse_der_basic_constraints(&[0x30, 0x03, 0x01, 0x01, 0x01]).is_none());
    let ku = parse_der_key_usage(&[0x03, 0x02, 0x01, 0x06]).unwrap();
    assert!(ku.key_cert_sign() && ku.crl_sign() && !ku.digital_signature());

    let root_k = FixtureSigner::p384(b"cap24-root");
    let inter_k = FixtureSigner::p384(b"cap24-inter");
    let leaf_k = FixtureSigner::p384(b"cap24-leaf");
    let rogue_k = FixtureSigner::p384(b"cap24-rogue");

    let root = issue_ca_cert(
        CertIdentity {
            subject_cn: "Root",
            issuer_cn: "Root",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        Some(1),
        true,
    );
    let inter = issue_ca_cert(
        CertIdentity {
            subject_cn: "Intermediate",
            issuer_cn: "Root",
            serial: 2,
            subject_signer: &inter_k,
            issuer_signer: &root_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        Some(0),
        true,
    );
    let leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "Leaf",
            issuer_cn: "Intermediate",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &inter_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        None,
        None,
    );
    let pinned_root = root.cert_sha256();

    assert!(verify_rfc5280_cert_chain(
        &[root.clone(), inter.clone(), leaf.clone()],
        &pinned_root,
        NOW
    )
    .is_ok());
    let ed_root_k = FixtureSigner::ed25519(b"ed-root");
    let rsa_leaf_k = FixtureSigner::rsa(2048);
    let ed_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "EdRoot",
            issuer_cn: "EdRoot",
            serial: 10,
            subject_signer: &ed_root_k,
            issuer_signer: &ed_root_k,
            sig_alg: SignatureAlgorithm::Ed25519,
        },
        Some(0),
        true,
    );
    let rsa_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "RsaLeaf",
            issuer_cn: "EdRoot",
            serial: 11,
            subject_signer: &rsa_leaf_k,
            issuer_signer: &ed_root_k,
            sig_alg: SignatureAlgorithm::Ed25519,
        },
        None,
        None,
    );
    assert!(
        verify_rfc5280_cert_chain(&[ed_root.clone(), rsa_leaf], &ed_root.cert_sha256(), NOW)
            .is_ok()
    );

    let mut tampered_der = leaf.cert_der().to_vec();
    let cn_pos = tampered_der
        .windows(4)
        .position(|w| w == b"Leaf")
        .expect("Leaf CN in DER");
    tampered_der[cn_pos] ^= 0x01;
    let tampered_leaf = CertRecord::from_der(&tampered_der).expect("still valid DER syntax");
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), inter.clone(), tampered_leaf],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::BadChainSignature { index: 2 })
    );

    let wrong_issuer_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "Leaf",
            issuer_cn: "Intermediate",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &rogue_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        None,
        None,
    );
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), inter.clone(), wrong_issuer_leaf],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::BadChainSignature { index: 2 })
    );

    let orig_spki = inter_k.public_key().to_spki_der();
    let rogue_spki = rogue_k.public_key().to_spki_der();
    assert_eq!(orig_spki.len(), rogue_spki.len());
    let mut spliced_inter_der = inter.cert_der().to_vec();
    let spki_pos = spliced_inter_der
        .windows(orig_spki.len())
        .position(|w| w == orig_spki.as_slice())
        .expect("SPKI in inter DER");
    spliced_inter_der[spki_pos..spki_pos + rogue_spki.len()].copy_from_slice(&rogue_spki);
    let spliced_inter = CertRecord::from_der(&spliced_inter_der).expect("spliced SPKI parses");
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), spliced_inter, leaf.clone()],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::BadChainSignature { index: 1 })
    );

    let p384_n: [u8; 48] = [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37,
        0x2d, 0xdf, 0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc,
        0xc5, 0x29, 0x73,
    ];
    let valid_raw = leaf_k.sign_ecdsa_raw(SignatureAlgorithm::EcdsaP384Sha384, b"scalar-test");
    for (bad_r, bad_s) in [
        (&[0u8; 48][..], &valid_raw[48..]),
        (&valid_raw[..48], &[0u8; 48][..]),
        (&p384_n[..], &valid_raw[48..]),
        (&valid_raw[..48], &p384_n[..]),
    ] {
        let forged = [bad_r, bad_s].concat();
        assert_eq!(
            verify_ecdsa_raw(
                &leaf_k.public_key(),
                SignatureAlgorithm::EcdsaP384Sha384,
                b"scalar-test",
                &forged
            ),
            Err(CryptoError::ScalarOutOfRange)
        );
    }

    let mut torsion_pk = [0u8; 32];
    torsion_pk[0] = 0x01;
    let torsion_spki = SubjectPublicKey::Ed25519(torsion_pk).to_spki_der();
    assert_eq!(
        SubjectPublicKey::from_spki_der(&torsion_spki),
        Err(CryptoError::InvalidEd25519Key)
    );
    let SubjectPublicKey::P384(mut off_curve_p384) = leaf_k.public_key() else {
        panic!()
    };
    off_curve_p384[96] ^= 0x01;
    let bad_p384_spki = SubjectPublicKey::P384(off_curve_p384).to_spki_der();
    assert_eq!(
        SubjectPublicKey::from_spki_der(&bad_p384_spki),
        Err(CryptoError::PointNotOnCurve)
    );
    let _ = der_encode;

    let forged_child_k = FixtureSigner::p384(b"forged-child");
    let forged_child = issue_leaf_cert(
        CertIdentity {
            subject_cn: "ForgedChild",
            issuer_cn: "Leaf",
            serial: 4,
            subject_signer: &forged_child_k,
            issuer_signer: &leaf_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        None,
        None,
    );
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), inter.clone(), leaf.clone(), forged_child],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::NonCaIssuer { index: 2 })
    );

    let bad_ku_inter_der = fixture_issue_cert_der(
        &FixtureCertSpec {
            subject_cn: "Intermediate",
            issuer_cn: "Root",
            serial: &[2],
            not_before: NOW - 86_400,
            not_after: NOW + 86_400,
            subject_key: inter_k.public_key(),
            basic_constraints: Some(BasicConstraints {
                is_ca: true,
                path_len_constraint: Some(0),
            }),
            key_usage: Some(KeyUsage::new(KEY_USAGE_DIGITAL_SIGNATURE)),
            ocsp_signing_eku: false,
            dice_fwid: None,
            amd_vcek_ext: None,
        },
        &root_k,
        SignatureAlgorithm::EcdsaP384Sha384,
    );
    let bad_ku_inter = CertRecord::from_der(&bad_ku_inter_der).unwrap();
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), bad_ku_inter, leaf.clone()],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::MissingKeyCertSign { index: 1 })
    );

    let strict_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "Root",
            issuer_cn: "Root",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        Some(0),
        true,
    );
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[strict_root.clone(), inter.clone(), leaf.clone()],
            &strict_root.cert_sha256(),
            NOW
        ),
        Err(CertChainError::PathLenConstraintExceeded {
            index: 0,
            max_allowed: 0,
            actual: 1
        })
    );

    let ca_as_leaf = issue_ca_cert(
        CertIdentity {
            subject_cn: "LeafCA",
            issuer_cn: "Intermediate",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &inter_k,
            sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
        },
        None,
        false,
    );
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), inter.clone(), ca_as_leaf],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::LeafMustNotBeCa)
    );

    assert_eq!(
        verify_rfc5280_cert_chain(&[root, inter, leaf], &pinned_root, 0),
        Err(CertChainError::InvalidClock)
    );
}

// ---------------------------------------------------------------------------
// 2. CAP-25: AMD SEV-SNP (1184-Byte ABI Table 21/22 Report + RSA-4096-PSS CRL + VCEK P-384)
// ---------------------------------------------------------------------------

#[test]
fn cap25_amd_sev_snp_real_rsa4096_pss_crl_and_vcek_p384_signatures() {
    let ark_k = FixtureSigner::rsa(4096);
    let ask_k = FixtureSigner::rsa(3072);
    let vcek_k = FixtureSigner::p384(b"amd-genoa-vcek-chip42");
    let rogue_k = FixtureSigner::p384(b"rogue-vcek");

    let min_tcb = AmdSnpTcbVersion {
        fmc: 0,
        bootloader: 3,
        tee: 1,
        snp: 8,
        microcode: 72,
    };
    let chip_id = [0x11u8; 64];

    let ark = issue_ca_cert(
        CertIdentity {
            subject_cn: "AMD-ARK-Genoa",
            issuer_cn: "AMD-ARK-Genoa",
            serial: 1,
            subject_signer: &ark_k,
            issuer_signer: &ark_k,
            sig_alg: SignatureAlgorithm::RsaPssSha384,
        },
        Some(1),
        true,
    );
    let ask = issue_ca_cert(
        CertIdentity {
            subject_cn: "AMD-ASK-Genoa",
            issuer_cn: "AMD-ARK-Genoa",
            serial: 2,
            subject_signer: &ask_k,
            issuer_signer: &ark_k,
            sig_alg: SignatureAlgorithm::RsaPssSha384,
        },
        Some(0),
        true,
    );
    let vcek = issue_leaf_cert(
        CertIdentity {
            subject_cn: "AMD-VCEK-Chip42",
            issuer_cn: "AMD-ASK-Genoa",
            serial: 3,
            subject_signer: &vcek_k,
            issuer_signer: &ask_k,
            sig_alg: SignatureAlgorithm::RsaPssSha384,
        },
        None,
        Some((min_tcb, chip_id)),
    );

    let launch_meas = [0x5Au8; 48];
    let policy = AmdSnpPolicy {
        product: AmdSnpProduct::Genoa,
        pinned_ark_sha256: ark.cert_sha256(),
        expected_measurement: sha256(&launch_meas),
        min_tcb,
        allow_debug: false,
        allow_migration_agent: false,
        max_vmpl: 0,
        min_guest_svn: 1,
    };

    let crl_der = fixture_issue_crl_der(
        "AMD-ARK-Genoa",
        NOW - 3600,
        NOW + 3600,
        &[vec![99]],
        &ark_k,
        SignatureAlgorithm::RsaPssSha384,
    );
    let valid_crl = AmdSnpCrl::from_der(&crl_der).expect("valid DER CRL");

    let fields = FixtureSnpReportFields {
        guest_svn: 2,
        guest_policy: 1 << 17,
        vmpl: 0,
        signing_key: 0,
        reported_tcb: min_tcb,
        launch_measurement: launch_meas,
        report_data: [0x22; 64],
        chip_id,
    };
    let report_bytes = fixture_build_amd_snp_report(&fields, AmdSnpProduct::Genoa, &vcek_k);
    assert_eq!(report_bytes.len(), SNP_REPORT_LEN);

    let att = AmdSnpAttestation {
        report_bytes,
        cert_chain: vec![ark.clone(), ask.clone(), vcek.clone()],
        crls: vec![valid_crl.clone()],
    };

    let sealed = verify_amd_sev_snp(&policy, &att, NOW).expect("honest 1184B SNP report passes");
    assert_eq!(sealed.vendor(), TeeVendor::AmdSevSnp(AmdSnpProduct::Genoa));
    assert_eq!(sealed.tcb_posture(), TcbPosture::VerifiedFloor);

    // 1-byte tamper in `report_data` (@ 0x050) without re-signing refused by P-384 verifier!
    let mut tampered_rep = att.clone();
    tampered_rep.report_bytes[0x050] ^= 0x01;
    assert_eq!(
        verify_amd_sev_snp(&policy, &tampered_rep, NOW),
        Err(TeeError::ReportSignatureInvalid)
    );

    // Non-zero high byte in 72-byte little-endian `r` padding (`0x2A0 + 48`) refused!
    let mut non_zero_sig_pad = att.clone();
    non_zero_sig_pad.report_bytes[0x2A0 + 48] = 0x01;
    assert_eq!(
        verify_amd_sev_snp(&policy, &non_zero_sig_pad, NOW),
        Err(TeeError::ReportSignatureInvalid)
    );

    // Wrong VCEK signing key refused!
    let mut wrong_sig = att.clone();
    wrong_sig.report_bytes = fixture_build_amd_snp_report(&fields, AmdSnpProduct::Genoa, &rogue_k);
    assert_eq!(
        verify_amd_sev_snp(&policy, &wrong_sig, NOW),
        Err(TeeError::ReportSignatureInvalid)
    );

    // Forged CRL signature (ASK claims issuer="AMD-ARK-Genoa"!) refused!
    let forged_crl_der = fixture_issue_crl_der(
        "AMD-ARK-Genoa",
        NOW - 3600,
        NOW + 3600,
        &[],
        &ask_k,
        SignatureAlgorithm::RsaPssSha384,
    );
    let mut bad_crl = att.clone();
    bad_crl.crls = vec![AmdSnpCrl::from_der(&forged_crl_der).unwrap()];
    assert_eq!(
        verify_amd_sev_snp(&policy, &bad_crl, NOW),
        Err(TeeError::SnpCrlSignatureInvalid)
    );

    // Empty CRL list refused
    let mut no_crl = att.clone();
    no_crl.crls.clear();
    assert_eq!(
        verify_amd_sev_snp(&policy, &no_crl, NOW),
        Err(TeeError::SnpMissingCrl)
    );

    // Expired CRL refused
    let exp_crl_der = fixture_issue_crl_der(
        "AMD-ARK-Genoa",
        NOW - 3600,
        NOW,
        &[],
        &ark_k,
        SignatureAlgorithm::RsaPssSha384,
    );
    let mut exp_crl = att.clone();
    exp_crl.crls = vec![AmdSnpCrl::from_der(&exp_crl_der).unwrap()];
    assert_eq!(
        verify_amd_sev_snp(&policy, &exp_crl, NOW),
        Err(TeeError::SnpCrlNotCurrent)
    );

    // ASK-only CRL without ARK-signed CRL refused (`SnpMissingArkCrl`)
    let ask_clean_crl_der = fixture_issue_crl_der(
        "AMD-ASK-Genoa",
        NOW - 3600,
        NOW + 3600,
        &[],
        &ask_k,
        SignatureAlgorithm::RsaPssSha384,
    );
    let mut ask_only = att.clone();
    ask_only.crls = vec![AmdSnpCrl::from_der(&ask_clean_crl_der).unwrap()];
    assert_eq!(
        verify_amd_sev_snp(&policy, &ask_only, NOW),
        Err(TeeError::SnpMissingArkCrl)
    );

    // Revoked VCEK serial refused
    let rev_crl_der = fixture_issue_crl_der(
        "AMD-ASK-Genoa",
        NOW - 3600,
        NOW + 3600,
        &[vcek.serial().to_vec()],
        &ask_k,
        SignatureAlgorithm::RsaPssSha384,
    );
    let mut rev_vcek = att.clone();
    rev_vcek.crls = vec![valid_crl, AmdSnpCrl::from_der(&rev_crl_der).unwrap()];
    assert_eq!(
        verify_amd_sev_snp(&policy, &rev_vcek, NOW),
        Err(TeeError::SnpCertificateRevoked)
    );

    // TCB below floor refused inside the gate (even when ASK genuinely signed the down-level VCEK!)
    let mut low_tcb_val = min_tcb;
    low_tcb_val.microcode = 71;
    let low_vcek = issue_leaf_cert(
        CertIdentity {
            subject_cn: "AMD-VCEK-Chip42",
            issuer_cn: "AMD-ASK-Genoa",
            serial: 4,
            subject_signer: &vcek_k,
            issuer_signer: &ask_k,
            sig_alg: SignatureAlgorithm::RsaPssSha384,
        },
        None,
        Some((low_tcb_val, chip_id)),
    );
    let mut low_fields = fields.clone();
    low_fields.reported_tcb = low_tcb_val;
    let mut low_tcb = att.clone();
    low_tcb.cert_chain[2] = low_vcek;
    low_tcb.report_bytes = fixture_build_amd_snp_report(&low_fields, AmdSnpProduct::Genoa, &vcek_k);
    assert_eq!(
        verify_amd_sev_snp(&policy, &low_tcb, NOW),
        Err(TeeError::SnpTcbBelowFloor)
    );

    // Debug guest forbidden
    let mut dbg_fields = fields;
    dbg_fields.guest_policy |= 1 << 19;
    let mut dbg = att;
    dbg.report_bytes = fixture_build_amd_snp_report(&dbg_fields, AmdSnpProduct::Genoa, &vcek_k);
    assert_eq!(
        verify_amd_sev_snp(&policy, &dbg, NOW),
        Err(TeeError::SnpDebugGuestForbidden)
    );
}

// ---------------------------------------------------------------------------
// 3. CAP-26: Intel TDX DCAP v4/v5 Binary Quote & NVIDIA Hopper/Blackwell SPDM + OCSP + SWID RIM
// ---------------------------------------------------------------------------

#[test]
fn cap26_intel_tdx_real_p256_qe_and_quote_signatures() {
    let root_k = FixtureSigner::p256(b"intel-sgx-root");
    let pck_ca_k = FixtureSigner::p256(b"intel-pck-ca");
    let pck_leaf_k = FixtureSigner::p256(b"intel-pck-leaf");
    let att_k = FixtureSigner::p256(b"tdx-qe-att-key");
    let rogue_att_k = FixtureSigner::p256(b"rogue-att-key");

    let intel_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "Intel-SGX-Root",
            issuer_cn: "Intel-SGX-Root",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: SignatureAlgorithm::EcdsaP256Sha256,
        },
        Some(1),
        true,
    );
    let pck_ca = issue_ca_cert(
        CertIdentity {
            subject_cn: "Intel-PCK-CA",
            issuer_cn: "Intel-SGX-Root",
            serial: 2,
            subject_signer: &pck_ca_k,
            issuer_signer: &root_k,
            sig_alg: SignatureAlgorithm::EcdsaP256Sha256,
        },
        Some(0),
        true,
    );
    let pck_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "Intel-PCK-Leaf",
            issuer_cn: "Intel-PCK-CA",
            serial: 3,
            subject_signer: &pck_leaf_k,
            issuer_signer: &pck_ca_k,
            sig_alg: SignatureAlgorithm::EcdsaP256Sha256,
        },
        None,
        None,
    );
    let pck_chain = vec![intel_root.clone(), pck_ca, pck_leaf];

    let pin = IntelTdxMeasurementPin {
        mr_td: [0x10; 48],
        rt_mr0: [0x20; 48],
        rt_mr1: [0x30; 48],
        rt_mr2: [0x40; 48],
        pin_rtmr3: None,
    };
    let pinned_svc_td = [0x99; 48];
    let policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256(),
        measurement_pin: pin.clone(),
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: vec![pinned_svc_td],
    };

    // Test both DCAP v4 (TD 1.0, 632B signed prefix) and DCAP v5 TD 1.5 (`mr_servicetd`)!
    let mut fields = FixtureTdxQuoteFields {
        mr_td: pin.mr_td,
        rt_mr0: pin.rt_mr0,
        rt_mr1: pin.rt_mr1,
        rt_mr2: pin.rt_mr2,
        rt_mr3: [0xFF; 48],
        mr_servicetd: None,
        td_attributes: 0,
        report_data: [0x33; 64],
        qe_auth_data: b"intel-qe-auth-v1".to_vec(),
    };
    let v4_quote = fixture_build_intel_tdx_quote(&fields, &pck_chain, &pck_leaf_k, &att_k);
    let att_v4 = IntelTdxAttestation {
        quote_bytes: v4_quote,
        tcb_status: "UpToDate".to_string(),
    };
    let sealed_v4 = verify_intel_tdx(&policy, &att_v4, NOW).expect("DCAP v4 quote passes");
    assert_eq!(sealed_v4.vendor(), TeeVendor::IntelTdx);

    // 1-byte tamper in `report_data` (@ 48 + 520 = 568) in v4 quote refused!
    let mut bad_quote = att_v4.clone();
    bad_quote.quote_bytes[48 + 520] ^= 0x01;
    assert_eq!(
        verify_intel_tdx(&policy, &bad_quote, NOW),
        Err(TeeError::ReportSignatureInvalid)
    );

    // Spliced `att_pub_key_64` (@ 636 + 64 = 700..764) without PCK QE signature refused!
    let mut spliced_ak = att_v4.clone();
    let SubjectPublicKey::P256(rpk) = rogue_att_k.public_key() else {
        panic!()
    };
    spliced_ak.quote_bytes[700..764].copy_from_slice(&rpk[1..65]);
    assert_eq!(
        verify_intel_tdx(&policy, &spliced_ak, NOW),
        Err(TeeError::TdxQeReportSignatureInvalid)
    );

    // Debug TD (`td_attributes` bit 0 set) refused!
    let mut dbg_fields = fields.clone();
    dbg_fields.td_attributes = 1;
    let dbg_quote = fixture_build_intel_tdx_quote(&dbg_fields, &pck_chain, &pck_leaf_k, &att_k);
    assert_eq!(
        verify_intel_tdx(
            &policy,
            &IntelTdxAttestation {
                quote_bytes: dbg_quote,
                tcb_status: "UpToDate".to_string()
            },
            NOW
        ),
        Err(TeeError::TdxDebugTdForbidden)
    );

    // TD 1.5 pinned `mr_servicetd` passes; unpinned nonzero `mr_servicetd` refused!
    fields.mr_servicetd = Some(pinned_svc_td);
    let v5_pinned = fixture_build_intel_tdx_quote(&fields, &pck_chain, &pck_leaf_k, &att_k);
    assert!(verify_intel_tdx(
        &policy,
        &IntelTdxAttestation {
            quote_bytes: v5_pinned,
            tcb_status: "UpToDate".to_string()
        },
        NOW
    )
    .is_ok());

    fields.mr_servicetd = Some([0x77; 48]);
    let v5_rogue_svc = fixture_build_intel_tdx_quote(&fields, &pck_chain, &pck_leaf_k, &att_k);
    assert_eq!(
        verify_intel_tdx(
            &policy,
            &IntelTdxAttestation {
                quote_bytes: v5_rogue_svc,
                tcb_status: "UpToDate".to_string()
            },
            NOW
        ),
        Err(TeeError::TdxServiceTdNotPinned)
    );

    // Wrong RTMR2 refused
    let mut bad_rtmr_fields = fields;
    bad_rtmr_fields.mr_servicetd = None;
    bad_rtmr_fields.rt_mr2[0] ^= 1;
    let bad_rtmr_q =
        fixture_build_intel_tdx_quote(&bad_rtmr_fields, &pck_chain, &pck_leaf_k, &att_k);
    assert_eq!(
        verify_intel_tdx(
            &policy,
            &IntelTdxAttestation {
                quote_bytes: bad_rtmr_q,
                tcb_status: "UpToDate".to_string()
            },
            NOW
        ),
        Err(TeeError::TdxRtmrMismatch(2))
    );

    // OutOfDate TCB refused
    let mut ood = att_v4.clone();
    ood.tcb_status = "OutOfDate".to_string();
    assert_eq!(
        verify_intel_tdx(&policy, &ood, NOW),
        Err(TeeError::TdxTcbStatusRejected("OutOfDate".to_string()))
    );

    assert_eq!(
        verify_intel_tdx(&policy, &att_v4, 0),
        Err(TeeError::InvalidClock)
    );
}

struct NvidiaFixtureKeys {
    dev_inter_k: FixtureSigner,
    dev_leaf_k: FixtureSigner,
}

fn make_nvidia_fixture(
    arch: GpuArch,
    nonce: [u8; 32],
    fwid: [u8; 48],
) -> (NvidiaGpuPolicy, NvidiaGpuAttestation, NvidiaFixtureKeys) {
    let dev_root_k = FixtureSigner::p384(b"nv-dev-root");
    let dev_inter_k = FixtureSigner::p384(b"nv-dev-inter");
    let dev_leaf_k = FixtureSigner::p384(b"nv-gpu-leaf");

    let rim_root_k = FixtureSigner::p384(b"nv-rim-root");
    let rim_inter_k = FixtureSigner::p384(b"nv-rim-inter");
    let drv_leaf_k = FixtureSigner::p384(b"nv-drv-rim-leaf");
    let vbios_leaf_k = FixtureSigner::p384(b"nv-vbios-rim-leaf");

    let alg = SignatureAlgorithm::EcdsaP384Sha384;
    let dev_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "NV-Dev-Root",
            issuer_cn: "NV-Dev-Root",
            serial: 1,
            subject_signer: &dev_root_k,
            issuer_signer: &dev_root_k,
            sig_alg: alg,
        },
        Some(1),
        true,
    );
    let dev_inter = issue_ca_cert(
        CertIdentity {
            subject_cn: "NV-Dev-L1",
            issuer_cn: "NV-Dev-Root",
            serial: 2,
            subject_signer: &dev_inter_k,
            issuer_signer: &dev_root_k,
            sig_alg: alg,
        },
        Some(0),
        true,
    );
    let dev_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "NV-GPU-Leaf",
            issuer_cn: "NV-Dev-L1",
            serial: 3,
            subject_signer: &dev_leaf_k,
            issuer_signer: &dev_inter_k,
            sig_alg: alg,
        },
        Some(fwid),
        None,
    );

    let rim_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "NV-CoRIM-Root",
            issuer_cn: "NV-CoRIM-Root",
            serial: 10,
            subject_signer: &rim_root_k,
            issuer_signer: &rim_root_k,
            sig_alg: alg,
        },
        Some(1),
        true,
    );
    let rim_inter = issue_ca_cert(
        CertIdentity {
            subject_cn: "NV-CoRIM-L1",
            issuer_cn: "NV-CoRIM-Root",
            serial: 11,
            subject_signer: &rim_inter_k,
            issuer_signer: &rim_root_k,
            sig_alg: alg,
        },
        Some(0),
        true,
    );
    let drv_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "NV-Drv-RIM",
            issuer_cn: "NV-CoRIM-L1",
            serial: 12,
            subject_signer: &drv_leaf_k,
            issuer_signer: &rim_inter_k,
            sig_alg: alg,
        },
        None,
        None,
    );
    let vbios_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "NV-VBIOS-RIM",
            issuer_cn: "NV-CoRIM-L1",
            serial: 13,
            subject_signer: &vbios_leaf_k,
            issuer_signer: &rim_inter_k,
            sig_alg: alg,
        },
        None,
        None,
    );

    let m1 = vec![0xAAu8; 48];
    let m2 = vec![0xBBu8; 48];
    let report_bytes = build_signed_spdm_report(
        nonce,
        [0x55; 32],
        &[(1, &m1), (2, &m2)],
        &[
            (OPAQUE_FWID, &fwid),
            (OPAQUE_PROJECT, b"1010"),
            (OPAQUE_PROJECT_SKU, b"0200"),
            (OPAQUE_CHIP_SKU, b"890"),
        ],
        &dev_leaf_k,
    );
    let mut drv_goldens = BTreeMap::new();
    drv_goldens.insert(1, vec![m1]);
    let mut vbios_goldens = BTreeMap::new();
    vbios_goldens.insert(2, vec![m2]);

    let ocsp_responses = vec![
        NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
            &dev_root,
            &dev_inter,
            NvidiaOcspStatus::Good,
            NOW - 600,
            NOW + 600,
            &dev_root_k,
            alg,
        ))
        .unwrap(),
        NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
            &dev_inter,
            &dev_leaf,
            NvidiaOcspStatus::Good,
            NOW - 600,
            NOW + 600,
            &dev_inter_k,
            alg,
        ))
        .unwrap(),
        NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
            &rim_root,
            &rim_inter,
            NvidiaOcspStatus::Good,
            NOW - 600,
            NOW + 600,
            &rim_root_k,
            alg,
        ))
        .unwrap(),
        NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
            &rim_inter,
            &drv_leaf,
            NvidiaOcspStatus::Good,
            NOW - 600,
            NOW + 600,
            &rim_inter_k,
            alg,
        ))
        .unwrap(),
        NvidiaOcspResponse::from_der(&fixture_issue_ocsp_der(
            &rim_inter,
            &vbios_leaf,
            NvidiaOcspStatus::Good,
            NOW - 600,
            NOW + 600,
            &rim_inter_k,
            alg,
        ))
        .unwrap(),
    ];

    let driver_rim = fixture_build_nvidia_rim_swid_xml(
        arch,
        "570.124.06",
        &[rim_root.clone(), rim_inter.clone(), drv_leaf],
        &drv_goldens,
        &drv_leaf_k,
    );
    let vbios_rim = fixture_build_nvidia_rim_swid_xml(
        arch,
        "96.00.A5.00.01",
        &[rim_root.clone(), rim_inter, vbios_leaf],
        &vbios_goldens,
        &vbios_leaf_k,
    );

    let policy = NvidiaGpuPolicy {
        arch,
        pinned_device_root_sha256: dev_root.cert_sha256(),
        pinned_corim_root_sha256: rim_root.cert_sha256(),
        expected_driver_version: "570.124.06".to_string(),
        expected_vbios_version: "96.00.A5.00.01".to_string(),
        pinned_fwid: fwid,
    };
    let att = NvidiaGpuAttestation {
        spdm_report_bytes: report_bytes,
        device_cert_chain: vec![dev_root, dev_inter, dev_leaf],
        driver_rim,
        vbios_rim,
        ocsp_responses,
    };
    (
        policy,
        att,
        NvidiaFixtureKeys {
            dev_inter_k,
            dev_leaf_k,
        },
    )
}

#[test]
fn cap26_nvidia_hopper_and_blackwell_real_spdm_ocsp_and_rim_signatures() {
    let nonce = [0x42; 32];
    let fwid = [0xCD; 48];
    assert_eq!(
        extract_der_dice_fwid(&{
            let mut v = vec![0x04, 0x30];
            v.extend_from_slice(&fwid);
            v
        }),
        Some(fwid)
    );

    for arch in [GpuArch::HopperH100, GpuArch::BlackwellB200] {
        let (policy, att, keys) = make_nvidia_fixture(arch, nonce, fwid);
        let parsed = parse_spdm_gpu_report(&att.spdm_report_bytes).expect("SPDM 1.1 parse");
        assert_eq!(parsed.fwid(), Some(fwid));

        let sealed = verify_nvidia_gpu(&policy, &att, &nonce, NOW).expect("GPU must verify");
        assert_eq!(sealed.vendor(), TeeVendor::NvidiaGpu(arch));
        assert_eq!(sealed.gpu_fwid(), Some(fwid));

        // 1-byte tamper in SPDM signed prefix refused by P-384 verifier!
        let mut bad_spdm = att.clone();
        bad_spdm.spdm_report_bytes[45] ^= 0x01;
        assert_eq!(
            verify_nvidia_gpu(&policy, &bad_spdm, &nonce, NOW),
            Err(TeeError::ReportSignatureInvalid)
        );

        // 1-char hex tamper inside SWID XML `<ns0:Payload>` `Hash0="..."` without re-signing RIM refused!
        let mut bad_rim = att.clone();
        let xml_str = std::str::from_utf8(&bad_rim.driver_rim.swid_xml).unwrap();
        let h_pos = xml_str.find("Hash0=\"").unwrap() + 7;
        bad_rim.driver_rim.swid_xml[h_pos] = if bad_rim.driver_rim.swid_xml[h_pos] == b'a' {
            b'b'
        } else {
            b'a'
        };
        assert_eq!(
            verify_nvidia_gpu(&policy, &bad_rim, &nonce, NOW),
            Err(TeeError::ReportSignatureInvalid)
        );

        // XML comment smuggling / DOCTYPE outside strict XML subset refused!
        let mut comment_rim = att.clone();
        let injected = std::str::from_utf8(&comment_rim.driver_rim.swid_xml)
            .unwrap()
            .replacen("<ns0:Payload>", "<!-- x --><ns0:Payload>", 1);
        comment_rim.driver_rim = NvidiaRimManifest {
            swid_xml: injected.into_bytes(),
        };
        assert_eq!(
            verify_nvidia_gpu(&policy, &comment_rim, &nonce, NOW),
            Err(TeeError::GpuMalformedRimXml)
        );

        // Policy FWID mismatch refused
        let mut wrong_pin = policy.clone();
        wrong_pin.pinned_fwid[0] ^= 0xFF;
        assert_eq!(
            verify_nvidia_gpu(&wrong_pin, &att, &nonce, NOW),
            Err(TeeError::GpuFwidRimPinMismatch)
        );

        // Cert DICE FWID differs from SPDM TLV 20 FWID
        let mut bad_fwid = fwid;
        bad_fwid[47] ^= 1;
        let bad_leaf = issue_leaf_cert(
            CertIdentity {
                subject_cn: "NV-GPU-Leaf",
                issuer_cn: "NV-Dev-L1",
                serial: 3,
                subject_signer: &keys.dev_leaf_k,
                issuer_signer: &keys.dev_inter_k,
                sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
            },
            Some(bad_fwid),
            None,
        );
        let mut forged_cert_fwid = att.clone();
        forged_cert_fwid.device_cert_chain[2] = bad_leaf;
        assert_eq!(
            verify_nvidia_gpu(&policy, &forged_cert_fwid, &nonce, NOW),
            Err(TeeError::GpuFwidCertMismatch)
        );

        // Trailing byte after SPDM signature refused
        let mut trailing = att.clone();
        trailing.spdm_report_bytes.push(0x00);
        assert_eq!(
            verify_nvidia_gpu(&policy, &trailing, &nonce, NOW),
            Err(TeeError::SpdmTrailingBytes(1))
        );

        // CAP-24 attack on GPU chain: Leaf-signed child cert appended to device chain!
        let rogue_child_k = FixtureSigner::p384(b"rogue-gpu-child");
        let rogue_child = issue_leaf_cert(
            CertIdentity {
                subject_cn: "RogueGpuChild",
                issuer_cn: "NV-GPU-Leaf",
                serial: 99,
                subject_signer: &rogue_child_k,
                issuer_signer: &keys.dev_leaf_k,
                sig_alg: SignatureAlgorithm::EcdsaP384Sha384,
            },
            Some(fwid),
            None,
        );
        let mut leaf_forged = att.clone();
        fixture_sign_spdm_report(&mut leaf_forged.spdm_report_bytes, &rogue_child_k);
        leaf_forged.device_cert_chain.push(rogue_child);
        assert_eq!(
            verify_nvidia_gpu(&policy, &leaf_forged, &nonce, NOW),
            Err(TeeError::CertChain(CertChainError::NonCaIssuer {
                index: 2
            }))
        );

        // Signed Revoked OCSP response refused (both appended after Good AND direct replacement)
        let rev_ocsp_der = fixture_issue_ocsp_der(
            &att.device_cert_chain[1],
            &att.device_cert_chain[2],
            NvidiaOcspStatus::Revoked,
            NOW - 600,
            NOW + 600,
            &keys.dev_inter_k,
            SignatureAlgorithm::EcdsaP384Sha384,
        );
        let rev_ocsp = NvidiaOcspResponse::from_der(&rev_ocsp_der).unwrap();
        let mut masked_revoked = att.clone();
        masked_revoked.ocsp_responses.push(rev_ocsp.clone());
        assert_eq!(
            verify_nvidia_gpu(&policy, &masked_revoked, &nonce, NOW),
            Err(TeeError::GpuOcspRevoked)
        );
        let mut revoked = att;
        revoked.ocsp_responses[1] = rev_ocsp;
        assert_eq!(
            verify_nvidia_gpu(&policy, &revoked, &nonce, NOW),
            Err(TeeError::GpuOcspRevoked)
        );
    }
}

#[test]
fn aws_nitro_real_cose_es384_and_honest_tcb_posture() {
    let root_k = FixtureSigner::p384(b"nitro-root");
    let inter_k = FixtureSigner::p384(b"nitro-inter");
    let leaf_k = FixtureSigner::p384(b"nitro-leaf");
    let alg = SignatureAlgorithm::EcdsaP384Sha384;

    let root = issue_ca_cert(
        CertIdentity {
            subject_cn: "AWS-Nitro-Root-G1",
            issuer_cn: "AWS-Nitro-Root-G1",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(1),
        false,
    );
    let inter = issue_ca_cert(
        CertIdentity {
            subject_cn: "AWS-Nitro-Regional",
            issuer_cn: "AWS-Nitro-Root-G1",
            serial: 2,
            subject_signer: &inter_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(0),
        false,
    );
    let leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "AWS-NSM-Leaf",
            issuer_cn: "AWS-Nitro-Regional",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &inter_k,
            sig_alg: alg,
        },
        None,
        None,
    );
    let chain = vec![root.clone(), inter, leaf];

    let pcr0 = [0x10u8; 48];
    let pcr1 = [0x20u8; 48];
    let pcr2 = [0x30u8; 48];
    let meas = fold_nitro_pcrs(&pcr0, &pcr1, &pcr2);
    let policy = AwsNitroPolicy {
        pinned_root_sha256: root.cert_sha256(),
        expected_measurement: meas,
        max_age_secs: Some(3600),
    };
    let cose_bytes = fixture_build_aws_nitro_cose(
        &FixtureNitroDocFields {
            module_id: "i-0123456789abcdef0-enc0123456789abcdef",
            cert_chain_root_to_leaf: &chain,
            doc_timestamp_ms: NOW * 1000,
            pcr0: &pcr0,
            pcr1: &pcr1,
            pcr2: &pcr2,
            user_data: &[0x77; 64],
        },
        &leaf_k,
    );
    let att = AwsNitroAttestation {
        cose_sign1_bytes: cose_bytes,
    };

    let sealed = verify_aws_nitro(&policy, &att, NOW).expect("honest CBOR COSE_Sign1 Nitro passes");
    assert_eq!(sealed.vendor(), TeeVendor::AwsNitro);
    assert_eq!(sealed.tcb_posture(), TcbPosture::NoPolicyOnPlatform);

    // 1-byte tamper inside CBOR `user_data` payload without re-signing COSE_Sign1 refused!
    let mut tampered = att.clone();
    let ud_pos = tampered
        .cose_sign1_bytes
        .windows(16)
        .position(|w| w == [0x77; 16])
        .unwrap();
    tampered.cose_sign1_bytes[ud_pos] ^= 0x01;
    assert_eq!(
        verify_aws_nitro(&policy, &tampered, NOW),
        Err(TeeError::ReportSignatureInvalid)
    );

    let future_bytes = fixture_build_aws_nitro_cose(
        &FixtureNitroDocFields {
            module_id: "i-0123456789abcdef0-enc0123456789abcdef",
            cert_chain_root_to_leaf: &chain,
            doc_timestamp_ms: (NOW + 120) * 1000,
            pcr0: &pcr0,
            pcr1: &pcr1,
            pcr2: &pcr2,
            user_data: &[0x77; 64],
        },
        &leaf_k,
    );
    assert_eq!(
        verify_aws_nitro(
            &policy,
            &AwsNitroAttestation {
                cose_sign1_bytes: future_bytes
            },
            NOW
        ),
        Err(TeeError::NitroFutureTimestamp { ahead_secs: 120 })
    );
}

// ---------------------------------------------------------------------------
// 4. V3 & V4: Registry-Pinned TLSNotary & CallTree (Real Notary Signatures!)
// ---------------------------------------------------------------------------

#[test]
fn v3_rogue_notary_key_and_v4_redaction_and_calltree() {
    let trusted_signer = FixtureSigner::p256(b"obend-trusted-notary-pk-v1");
    let rogue_signer = FixtureSigner::p256(b"attacker-self-hosted-rogue-notary");
    let trusted_notary_key = notary_key_fingerprint(&trusted_signer.public_key());
    let rogue_notary_key = notary_key_fingerprint(&rogue_signer.public_key());

    let registry = PinnedNotaryRegistry::new(vec![PinnedNotaryEntry {
        operator_id: "obend-notary-prod-1".to_string(),
        notary_key_sha256: trusted_notary_key,
        allowed_servers: vec!["api.coinbase.com".to_string(), "api.github.com".to_string()],
        valid_from: NOW - 86_400,
        valid_until: NOW + 86_400,
    }]);

    let mut honest_env = TlsnTranscriptEnvelope {
        server_name: "api.coinbase.com".to_string(),
        expected_path: "/v2/prices/BTC-USD/spot".to_string(),
        connection_time: NOW - 10,
        sent_bytes: b"GET /v2/prices/BTC-USD/spot HTTP/1.1\r\nHost: api.coinbase.com\r\n\r\n"
            .to_vec(),
        recv_bytes: b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"data\":{\"base\":\"BTC\",\"amount\":\"98450.25\"}}"
            .to_vec(),
        unauthed_recv_ranges: vec![],
        notary_public_key: trusted_signer.public_key(),
        notary_signature_alg: SignatureAlgorithm::EcdsaP256Sha256,
        notary_signature: Vec::new(),
        claimed_notary_key_hex: Some(hex_encode_lower(&trusted_notary_key)),
    };
    fixture_notarize(
        &mut honest_env,
        &trusted_signer,
        SignatureAlgorithm::EcdsaP256Sha256,
    );

    let verified = verify_tlsn_transcript(&registry, &honest_env, Some("data.amount"), NOW)
        .expect("registry-pinned transcript passes");
    assert_eq!(verified.extracted_field(), Some("98450.25"));
    assert_eq!(verified.notary_operator(), "obend-notary-prod-1");
    assert_eq!(verified.legs().len(), 4);

    let mut rogue_env = honest_env.clone();
    rogue_env.claimed_notary_key_hex = Some(hex_encode_lower(&rogue_notary_key));
    fixture_notarize(
        &mut rogue_env,
        &rogue_signer,
        SignatureAlgorithm::EcdsaP256Sha256,
    );
    assert_eq!(
        verify_tlsn_transcript(&registry, &rogue_env, Some("data.amount"), NOW),
        Err(OracleError::UntrustedNotaryKey)
    );

    let mut redacted = honest_env.clone();
    let body_idx = redacted.recv_bytes.len() - 8;
    redacted.unauthed_recv_ranges = vec![(body_idx, body_idx + 4)];
    fixture_notarize(
        &mut redacted,
        &trusted_signer,
        SignatureAlgorithm::EcdsaP256Sha256,
    );
    assert_eq!(
        verify_tlsn_transcript(&registry, &redacted, Some("data.amount"), NOW),
        Err(OracleError::UnauthedBodyBytes {
            range_start: body_idx,
            range_end: body_idx + 4
        })
    );

    let mut wrong_path = honest_env.clone();
    wrong_path.expected_path = "/v2/prices/ETH-USD/spot".to_string();
    assert_eq!(
        verify_tlsn_transcript(&registry, &wrong_path, Some("data.amount"), NOW),
        Err(OracleError::RequestPathMismatch)
    );

    assert_eq!(
        extract_json_field_strict(r#"{"amount":"100","amount":"999999"}"#, "amount"),
        Err(OracleError::JsonDuplicateKey("amount".to_string()))
    );

    let ed_notary = FixtureSigner::ed25519(b"obend-ed25519-notary");
    let mut reg2 = registry;
    reg2.push(PinnedNotaryEntry {
        operator_id: "obend-notary-prod-2".to_string(),
        notary_key_sha256: notary_key_fingerprint(&ed_notary.public_key()),
        allowed_servers: vec!["api.github.com".to_string()],
        valid_from: NOW - 86_400,
        valid_until: NOW + 86_400,
    });
    let mut hop2_env = TlsnTranscriptEnvelope {
        server_name: "api.github.com".to_string(),
        expected_path: "/repos/obend/oracle?price=98450.25".to_string(),
        connection_time: NOW - 5,
        sent_bytes:
            b"GET /repos/obend/oracle?price=98450.25 HTTP/1.1\r\nHost: api.github.com\r\n\r\n"
                .to_vec(),
        recv_bytes: b"HTTP/1.1 200 OK\r\n\r\n{\"ok\":true}".to_vec(),
        unauthed_recv_ranges: vec![],
        notary_public_key: ed_notary.public_key(),
        notary_signature_alg: SignatureAlgorithm::Ed25519,
        notary_signature: Vec::new(),
        claimed_notary_key_hex: None,
    };
    fixture_notarize(&mut hop2_env, &ed_notary, SignatureAlgorithm::Ed25519);

    let v2 = verify_tlsn_transcript(&reg2, &hop2_env, Some("ok"), NOW).unwrap();
    let policy_digest = sha256(b"calltree-policy-v1");
    let edges = vec![CallTreeEdge {
        parent_index: 0,
        child_index: 1,
        binding_token: "98450.25".to_string(),
    }];
    let expected_root = compute_calltree_root(
        &policy_digest,
        &[verified.transcript_digest(), v2.transcript_digest()],
        &edges,
    );
    let rec = CallTreeRecording {
        policy_digest,
        hops: vec![
            CallTreeHop {
                hop_id: "coinbase".to_string(),
                envelope: honest_env,
                extract_field: Some("data.amount".to_string()),
            },
            CallTreeHop {
                hop_id: "github".to_string(),
                envelope: hop2_env,
                extract_field: Some("ok".to_string()),
            },
        ],
        edges,
    };
    let ct = verify_calltree_recording(&reg2, &rec, &expected_root, NOW)
        .expect("honest calltree passes");
    assert_eq!(ct.root_digest(), expected_root);

    let bad_root = sha256(b"wrong-root");
    assert!(matches!(
        verify_calltree_recording(&reg2, &rec, &bad_root, NOW),
        Err(CallTreeError::RootDigestMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------
// 5. E2EE Prompt/Response Channel Binding & MITM Refusal
// ---------------------------------------------------------------------------

#[test]
fn e2ee_channel_binding_mitm_and_replay_refusal() {
    let nonce_bytes = [0x3Cu8; 32];
    let nonce_hex = hex_encode_lower(&nonce_bytes);
    let mlkem_pk = [0x5Au8; ML_KEM_768_PUBKEY_LEN];
    let pubkey_b64 = base64_encode_std(&mlkem_pk);

    let root_k = FixtureSigner::p256(b"e2ee-intel-root");
    let ca_k = FixtureSigner::p256(b"e2ee-pck-ca");
    let leaf_k = FixtureSigner::p256(b"e2ee-pck-leaf");
    let att_k = FixtureSigner::p256(b"e2ee-att-key");
    let alg = SignatureAlgorithm::EcdsaP256Sha256;

    let intel_root = issue_ca_cert(
        CertIdentity {
            subject_cn: "Intel-SGX-Root",
            issuer_cn: "Intel-SGX-Root",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(1),
        true,
    );
    let pck_ca = issue_ca_cert(
        CertIdentity {
            subject_cn: "Intel-PCK-CA",
            issuer_cn: "Intel-SGX-Root",
            serial: 2,
            subject_signer: &ca_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(0),
        true,
    );
    let pck_leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "Intel-PCK-Leaf",
            issuer_cn: "Intel-PCK-CA",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &ca_k,
            sig_alg: alg,
        },
        None,
        None,
    );

    let pin = IntelTdxMeasurementPin {
        mr_td: [0x11; 48],
        rt_mr0: [0x22; 48],
        rt_mr1: [0x33; 48],
        rt_mr2: [0x44; 48],
        pin_rtmr3: None,
    };
    let tdx_policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256(),
        measurement_pin: pin.clone(),
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: vec![],
    };
    let mut rd = [0u8; 64];
    rd[..32].copy_from_slice(&chutes_report_data_binding(&nonce_hex, &pubkey_b64));
    let quote_bytes = fixture_build_intel_tdx_quote(
        &FixtureTdxQuoteFields {
            mr_td: pin.mr_td,
            rt_mr0: pin.rt_mr0,
            rt_mr1: pin.rt_mr1,
            rt_mr2: pin.rt_mr2,
            rt_mr3: [0; 48],
            mr_servicetd: Some(NO_SERVICE_TD),
            td_attributes: 0,
            report_data: rd,
            qe_auth_data: b"e2ee-qe".to_vec(),
        },
        &[intel_root, pck_ca, pck_leaf],
        &leaf_k,
        &att_k,
    );
    let tdx_att = IntelTdxAttestation {
        quote_bytes,
        tcb_status: "UpToDate".to_string(),
    };
    let cpu_tee = verify_intel_tdx(&tdx_policy, &tdx_att, NOW).expect("TDX CPU tee");

    let (gpu_policy, gpu_att, _) =
        make_nvidia_fixture(GpuArch::BlackwellB200, nonce_bytes, [0xEF; 48]);
    let gpu_tee =
        verify_nvidia_gpu(&gpu_policy, &gpu_att, &nonce_bytes, NOW).expect("B200 GPU tee");

    let input = E2eeChannelInput {
        chute_id: "chute-qwen35".to_string(),
        instance_id: "inst-b200-01".to_string(),
        attestation_nonce_hex: nonce_hex,
        e2e_pubkey_b64: pubkey_b64,
    };
    let ch_policy = E2eeChannelPolicy::default();
    let channel = verify_e2ee_channel(
        &ch_policy,
        &input,
        &cpu_tee,
        std::slice::from_ref(&gpu_tee),
        NOW,
    )
    .expect("CPU+GPU bound E2EE channel passes");

    let shared = [0x91u8; 32];
    let kem_ct = [0x24u8; 1088];
    let k_req = channel
        .derive_bound_session_key(&shared, &kem_ct, ChannelDirection::Request)
        .unwrap();
    let k_resp = channel
        .derive_bound_session_key(&shared, &kem_ct, ChannelDirection::Response)
        .unwrap();
    assert_ne!(k_req, k_resp);

    let mut guard = E2eeSessionGuard::new(channel);
    let aad1 = guard
        .authorize_invocation("inv-001", ChannelDirection::Request, NOW + 10)
        .expect("first invocation");
    assert_eq!(
        guard.authorize_invocation("inv-001", ChannelDirection::Request, NOW + 11),
        Err(E2eeChannelError::InvocationNonceReplayed)
    );
    assert_eq!(
        guard.authorize_invocation("inv-002", ChannelDirection::Request, NOW + 1800),
        Err(E2eeChannelError::SessionExpired)
    );
    assert_ne!(aad1, [0u8; 32]);

    let mut mitm_pk = mlkem_pk;
    mitm_pk[0] ^= 0xFF;
    let mut mitm_input = input.clone();
    mitm_input.e2e_pubkey_b64 = base64_encode_std(&mitm_pk);
    assert_eq!(
        verify_e2ee_channel(
            &ch_policy,
            &mitm_input,
            &cpu_tee,
            std::slice::from_ref(&gpu_tee),
            NOW
        ),
        Err(E2eeChannelError::ReportDataBindingMismatch)
    );

    let two_gpu_policy = E2eeChannelPolicy {
        min_gpus: 2,
        ..ch_policy
    };
    assert_eq!(
        verify_e2ee_channel(
            &two_gpu_policy,
            &input,
            &cpu_tee,
            &[gpu_tee.clone(), gpu_tee],
            NOW
        ),
        Err(E2eeChannelError::DuplicateGpuDevice)
    );

    assert_eq!(
        verify_e2ee_channel(&ch_policy, &input, &cpu_tee, &[], NOW),
        Err(E2eeChannelError::InsufficientAttestedGpus {
            required: 1,
            actual: 0
        })
    );
}

// ---------------------------------------------------------------------------
// 6. Exact Integer FHSDD001 & FHQPB001 KKT Oracle Verifier (0 floats!)
// ---------------------------------------------------------------------------

#[test]
fn fhsdd001_and_fhqpb001_exact_kkt_matrix_pin_and_attested_quote() {
    let s: i128 = 10i128.pow(QP_CERT_EXACT_SCALE);
    let witness = SddFactorWitness {
        dimension: 2,
        scale: QP_CERT_EXACT_SCALE,
        edges: vec![SddFactorEdge {
            u: 0,
            v: 1,
            weight: s,
            negative_offdiag: true,
        }],
        diag_slack: vec![s, s],
    };
    assert!(verify_sdd_factor_witness(&witness).is_ok());
    let admission = witness
        .to_sdd_certificate()
        .expect("SDD cert from O(|E|) factor");
    assert_eq!(admission.exact_entries(), &[2 * s, -s, -s, 2 * s]);
    assert_eq!(admission.row_radii(), &[s, s]);

    let mut bad_edge = witness;
    bad_edge.edges[0].weight = -1;
    assert_eq!(
        verify_sdd_factor_witness(&bad_edge),
        Err(SddFactorError::NegativeEdgeWeight { edge_index: 0 })
    );

    assert_eq!(
        ExactSddPsdCertificate::from_exact_matrix(
            2,
            QP_CERT_EXACT_SCALE,
            vec![s, 2 * s, 2 * s, s],
            vec![2 * s, 2 * s]
        ),
        Err(ExactSddPsdCertificateError::NotDiagonallyDominant { row: 0 })
    );

    let half = s / 2;
    let problem = ExactQpProblem {
        n: 2,
        mc: 1,
        scale: QP_CERT_EXACT_SCALE,
        p: vec![2 * s, -s, -s, 2 * s],
        q: vec![-s, -s],
        a: vec![s, s],
        l: vec![s],
        u: vec![s],
    };
    let kkt = ExactQpKktCert {
        n: 2,
        mc: 1,
        scale: QP_CERT_EXACT_SCALE,
        p: problem.p.clone(),
        q: problem.q.clone(),
        a: problem.a.clone(),
        l: problem.l.clone(),
        u: problem.u.clone(),
        x: vec![half, half],
        y: vec![half],
        epsilon: 0,
    };
    let bundle =
        ExactQpCertificateBundle::new(admission.clone(), kkt.clone()).expect("valid FHQPB001");
    let wire = bundle.to_wire_bytes().expect("encode FHQPB001");

    let verified_zero =
        verify_zero_kkt_certified_qp(&problem, &wire).expect("exact-zero KKT QP verifies");
    assert_eq!(verified_zero.program_digest(), problem.program_digest());
    assert_eq!(
        verified_zero.objective().twice_numerator(),
        -(3 * s * s * (s / 2))
    );

    let other_psd = ExactSddPsdCertificate::from_exact_matrix(
        2,
        QP_CERT_EXACT_SCALE,
        vec![s, 0, 0, s],
        vec![0, 0],
    )
    .unwrap();
    assert_eq!(
        ExactQpCertificateBundle::new(other_psd.clone(), kkt.clone()),
        Err(ExactQpCertificateBundleError::MatrixPinMismatch { index: 0 })
    );

    let other_psd_wire = other_psd.to_wire_bytes().unwrap();
    let orig_psd_wire = admission.to_wire_bytes().unwrap();
    assert_eq!(other_psd_wire.len(), orig_psd_wire.len());
    let mut forged_wire = wire.clone();
    let header_len = 8 + 1 + 4 + 4 + 4 + 4;
    forged_wire[header_len..header_len + other_psd_wire.len()].copy_from_slice(&other_psd_wire);
    let payload_len = forged_wire.len() - 32;
    let mut h = obend_oracles_e2ee::Sha256::new();
    let domain = b"fhir/exact-qp-certificate-bundle/v1";
    h.update(&(domain.len() as u64).to_be_bytes());
    h.update(domain);
    h.update(&(payload_len as u64).to_be_bytes());
    h.update(&forged_wire[..payload_len]);
    let forged_checksum = h.finalize();
    forged_wire[payload_len..].copy_from_slice(&forged_checksum);
    assert_eq!(
        ExactQpCertificateBundle::from_wire_bytes(&forged_wire),
        Err(ExactQpCertificateBundleError::MatrixPinMismatch { index: 0 })
    );

    let forged_dual = ExactQpKktCert {
        n: 1,
        mc: 1,
        scale: QP_CERT_EXACT_SCALE,
        p: vec![2 * s],
        q: vec![-2 * s],
        a: vec![s],
        l: vec![0],
        u: vec![2 * s],
        x: vec![0],
        y: vec![2 * s],
        epsilon: 0,
    };
    let forged_rep = forged_dual.check();
    assert!(forged_rep.primal_feasible && forged_rep.dual_feasible);
    assert!(!forged_rep.normal_cone && !forged_rep.valid);

    let mut different_problem = problem.clone();
    different_problem.q[0] = -2 * s;
    assert_eq!(
        verify_certified_qp(&different_problem, &wire),
        Err(ExactQpCertificateBundleError::ProgramBinding(
            QpProblemBindingError::FieldMismatch {
                field: "q",
                index: 0
            }
        ))
    );

    let mut ovf = kkt;
    ovf.x[0] = i128::MAX;
    let ovf_rep = ovf.check();
    assert!(ovf_rep.overflow && !ovf_rep.valid);

    let quote_nonce = [0x88u8; 32];
    let mut wire_checksum = [0u8; 32];
    wire_checksum.copy_from_slice(&wire[wire.len() - 32..]);
    let commitment =
        solver_quote_commitment(&problem.program_digest(), &wire_checksum, &quote_nonce);

    let root_k = FixtureSigner::p384(b"solver-nitro-root");
    let inter_k = FixtureSigner::p384(b"solver-nitro-inter");
    let leaf_k = FixtureSigner::p384(b"solver-nitro-leaf");
    let alg = SignatureAlgorithm::EcdsaP384Sha384;
    let root = issue_ca_cert(
        CertIdentity {
            subject_cn: "AWS-Nitro-Root-G1",
            issuer_cn: "AWS-Nitro-Root-G1",
            serial: 1,
            subject_signer: &root_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(1),
        false,
    );
    let inter = issue_ca_cert(
        CertIdentity {
            subject_cn: "AWS-Nitro-Regional",
            issuer_cn: "AWS-Nitro-Root-G1",
            serial: 2,
            subject_signer: &inter_k,
            issuer_signer: &root_k,
            sig_alg: alg,
        },
        Some(0),
        false,
    );
    let leaf = issue_leaf_cert(
        CertIdentity {
            subject_cn: "AWS-NSM-Solver",
            issuer_cn: "AWS-Nitro-Regional",
            serial: 3,
            subject_signer: &leaf_k,
            issuer_signer: &inter_k,
            sig_alg: alg,
        },
        None,
        None,
    );

    let pcr0 = [0xA1u8; 48];
    let pcr1 = [0xA2u8; 48];
    let pcr2 = [0xA3u8; 48];
    let meas = fold_nitro_pcrs(&pcr0, &pcr1, &pcr2);
    let mut user_data = [0u8; 64];
    user_data[..32].copy_from_slice(&commitment);
    let nitro_cose = fixture_build_aws_nitro_cose(
        &FixtureNitroDocFields {
            module_id: "i-solver-enc01",
            cert_chain_root_to_leaf: &[root.clone(), inter, leaf],
            doc_timestamp_ms: NOW * 1000,
            pcr0: &pcr0,
            pcr1: &pcr1,
            pcr2: &pcr2,
            user_data: &user_data,
        },
        &leaf_k,
    );
    let solver_tee = verify_aws_nitro(
        &AwsNitroPolicy {
            pinned_root_sha256: root.cert_sha256(),
            expected_measurement: meas,
            max_age_secs: Some(3600),
        },
        &AwsNitroAttestation {
            cose_sign1_bytes: nitro_cose,
        },
        NOW,
    )
    .expect("solver TEE");

    let quote = verify_attested_solver_quote(&solver_tee, &problem, &wire, &quote_nonce)
        .expect("attested solver quote passes");
    assert_eq!(quote.quote_commitment(), commitment);

    let bad_nonce = [0x99u8; 32];
    assert_eq!(
        verify_attested_solver_quote(&solver_tee, &problem, &wire, &bad_nonce),
        Err(ExactQpCertificateBundleError::QuoteAttestationMismatch)
    );

    let (gpu_pol, gpu_att, _) = make_nvidia_fixture(GpuArch::HopperH100, commitment, [0xAB; 48]);
    let gpu_tee = verify_nvidia_gpu(&gpu_pol, &gpu_att, &commitment, NOW).unwrap();
    assert_eq!(
        verify_attested_solver_quote(&gpu_tee, &problem, &wire, &quote_nonce),
        Err(ExactQpCertificateBundleError::QuoteAttestationMismatch)
    );
}
