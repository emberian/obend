//! Conformance & adversarial test suite for `obend-oracles-e2ee`:
//! - `CAP-24`: RFC 5280 `BasicConstraints` (`is_ca`, `pathLenConstraint`) & `KeyUsage`
//!   (including real ASN.1 DER parsing and leaf-signed child cert forgery refusal)
//! - `CAP-25`: AMD SEV-SNP mandatory non-expired CRL + TCB floor enforcement
//! - `CAP-26`: Intel TDX 1.5 `MR_SERVICETD` + `RTMR0..2` policy pin, clock fail-closed,
//!   and NVIDIA Hopper (`H100`) & Blackwell (`B200`) SPDM 1.1 + RIM `FWID` 3-way pin
//! - `V3` & `V4`: Registry-pinned TLSNotary & `calltree` (rogue notary key refusal,
//!   unauthed body range `'X'` injection refusal, host/path pinning, RFC 8259 duplicate-key refusal)
//! - E2EE Channel Binding: ML-KEM-768 pubkey + nonce bound to `VerifiedTeeEvidence.report_data`,
//!   mandatory GPU attestation, MITM pubkey swap refusal, single-use invocation nonce & TTL
//! - `FHSDD001` & `FHQPB001`: Pure-integer `O(|E|)` SDD-to-PSD + KKT + Matrix-Pin verifier
//!   (omitted/mismatched Matrix-Pin refusal, wrong-sign dual forgery, overflow fail-closed,
//!   and TEE-attested off-chain solver quote binding).

use std::collections::BTreeMap;

use obend_oracles_e2ee::kkt::solver_quote_commitment;
use obend_oracles_e2ee::tlsn_e2ee::compute_calltree_root;
use obend_oracles_e2ee::{
    base64_decode_strict, chutes_report_data_binding, extract_der_dice_fwid,
    extract_json_field_strict, fold_nitro_pcrs, hex_encode_lower, hkdf_sha256_expand,
    hkdf_sha256_extract, hmac_sha256, parse_der_basic_constraints, parse_der_key_usage,
    parse_spdm_gpu_report, sha256, verify_amd_sev_snp, verify_attested_solver_quote,
    verify_aws_nitro, verify_calltree_recording, verify_certified_qp, verify_e2ee_channel,
    verify_intel_tdx, verify_nvidia_gpu, verify_rfc5280_cert_chain, verify_sdd_factor_witness,
    verify_tlsn_transcript, verify_zero_kkt_certified_qp, AmdSnpAttestation, AmdSnpCrl,
    AmdSnpPolicy, AmdSnpProduct, AmdSnpTcbVersion, AwsNitroAttestation, AwsNitroPolicy,
    BasicConstraints, CallTreeEdge, CallTreeError, CallTreeHop, CallTreeRecording, CertChainError,
    CertRecord, ChannelDirection, E2eeChannelError, E2eeChannelInput, E2eeChannelPolicy,
    E2eeSessionGuard, ExactQpCertificateBundle, ExactQpCertificateBundleError, ExactQpKktCert,
    ExactQpProblem, ExactSddPsdCertificate, ExactSddPsdCertificateError, GpuArch,
    IntelTdxAttestation, IntelTdxMeasurementPin, IntelTdxPolicy, KeyUsage, NvidiaGpuAttestation,
    NvidiaGpuPolicy, NvidiaOcspResponse, NvidiaOcspStatus, NvidiaRimManifest, OracleError,
    PinnedNotaryEntry, PinnedNotaryRegistry, QpProblemBindingError, SddFactorEdge, SddFactorError,
    SddFactorWitness, TcbPosture, TeeError, TeeVendor, TlsnTranscriptEnvelope,
    KEY_USAGE_CRL_SIGN, KEY_USAGE_DIGITAL_SIGNATURE, KEY_USAGE_KEY_CERT_SIGN,
    ML_KEM_768_PUBKEY_LEN, NO_SERVICE_TD, OPAQUE_CHIP_SKU, OPAQUE_FWID, OPAQUE_PROJECT,
    OPAQUE_PROJECT_SKU, QP_CERT_EXACT_SCALE,
};

const NOW: u64 = 1_780_000_000;

fn base64_encode_std(input: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(((input.len() + 2) / 3) * 4);
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

fn ca_cert(subject: &str, issuer: &str, serial: u8, path_len: Option<u8>, crl: bool) -> CertRecord {
    let bits = KEY_USAGE_KEY_CERT_SIGN | if crl { KEY_USAGE_CRL_SIGN } else { 0 };
    // Real ASN.1 DER BasicConstraints: SEQUENCE { BOOLEAN TRUE, [INTEGER path_len] }
    let mut bc_der = vec![0x30, if path_len.is_some() { 6 } else { 3 }, 0x01, 0x01, 0xFF];
    if let Some(p) = path_len {
        bc_der.extend_from_slice(&[0x02, 0x01, p]);
    }
    // Real ASN.1 DER KeyUsage BIT STRING: bit 5 = 0x04, bit 6 = 0x02 (unused bits = 1)
    let ku_byte = 0x04 | if crl { 0x02 } else { 0x00 };
    let ku_der = vec![0x03, 0x02, 0x01, ku_byte];
    CertRecord {
        subject: subject.to_string(),
        issuer: issuer.to_string(),
        serial: vec![serial],
        cert_sha256: sha256(subject.as_bytes()),
        not_before: NOW - 86_400,
        not_after: NOW + 86_400,
        basic_constraints: Some(BasicConstraints {
            is_ca: true,
            path_len_constraint: path_len,
        }),
        basic_constraints_der: Some(bc_der),
        key_usage: Some(KeyUsage::new(bits)),
        key_usage_der: Some(ku_der),
        sig_verified: true,
        dice_fwid_ext_der: None,
    }
}

fn leaf_cert(subject: &str, issuer: &str, serial: u8, fwid: Option<[u8; 48]>) -> CertRecord {
    // Real ASN.1 DER BasicConstraints: SEQUENCE {} (is_ca = false)
    let bc_der = vec![0x30, 0x00];
    // Real ASN.1 DER KeyUsage BIT STRING: bit 0 (digitalSignature = 0x80), 7 unused bits
    let ku_der = vec![0x03, 0x02, 0x07, 0x80];
    let dice_fwid_ext_der = fwid.map(|f| {
        let mut ext = vec![0x30, 0x32, 0x04, 0x30];
        ext.extend_from_slice(&f);
        ext
    });
    CertRecord {
        subject: subject.to_string(),
        issuer: issuer.to_string(),
        serial: vec![serial],
        cert_sha256: sha256(subject.as_bytes()),
        not_before: NOW - 86_400,
        not_after: NOW + 86_400,
        basic_constraints: Some(BasicConstraints {
            is_ca: false,
            path_len_constraint: None,
        }),
        basic_constraints_der: Some(bc_der),
        key_usage: Some(KeyUsage::new(KEY_USAGE_DIGITAL_SIGNATURE)),
        key_usage_der: Some(ku_der),
        sig_verified: true,
        dice_fwid_ext_der,
    }
}

fn build_spdm_report(
    req_nonce: [u8; 32],
    resp_nonce: [u8; 32],
    measurements: &[(u8, &[u8])],
    opaque: &[(u16, &[u8])],
) -> Vec<u8> {
    let mut req = vec![0u8; 37];
    req[0] = 0x11; // SPDM 1.1
    req[1] = 0xE0; // GET_MEASUREMENTS
    req[4..36].copy_from_slice(&req_nonce);

    let mut rec = Vec::new();
    for &(idx, val) in measurements {
        let dmtf_len = 3 + val.len();
        rec.push(idx);
        rec.push(1); // DMTF spec
        rec.extend_from_slice(&(dmtf_len as u16).to_le_bytes());
        rec.push(0x01); // DMTF value type
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
    resp.extend_from_slice(&[0x11, 0x60, 0x00, 0x00]); // MEASUREMENTS response
    resp.push(measurements.len() as u8);
    let rec_len = rec.len();
    resp.push((rec_len & 0xff) as u8);
    resp.push(((rec_len >> 8) & 0xff) as u8);
    resp.push(((rec_len >> 16) & 0xff) as u8);
    resp.extend_from_slice(&rec);
    resp.extend_from_slice(&resp_nonce);
    resp.extend_from_slice(&(opaque_buf.len() as u16).to_le_bytes());
    resp.extend_from_slice(&opaque_buf);
    resp.extend_from_slice(&[0xABu8; 96]); // 96-byte P-384 signature

    let mut full = req;
    full.extend_from_slice(&resp);
    full
}

// ---------------------------------------------------------------------------
// 0. Crypto KATs (NIST SHA-256, RFC 4231 HMAC-SHA256, RFC 5869 HKDF-SHA256)
// ---------------------------------------------------------------------------

#[test]
fn sha256_hmac_hkdf_kats() {
    // NIST SHA-256("abc")
    assert_eq!(
        hex_encode_lower(&sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    // RFC 4231 Test Case 2: HMAC-SHA256("Jefe", "what do ya want for nothing?")
    assert_eq!(
        hex_encode_lower(&hmac_sha256(b"Jefe", b"what do ya want for nothing?")),
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    );
    // RFC 5869 Test Case 1: HKDF-SHA256 Extract
    let ikm = [0x0bu8; 22];
    let salt: [u8; 13] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
    ];
    let prk = hkdf_sha256_extract(&salt, &ikm);
    assert_eq!(
        hex_encode_lower(&prk),
        "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
    );
    let okm = hkdf_sha256_expand(&prk, &[0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]);
    assert_eq!(
        hex_encode_lower(&okm),
        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf"
    );
    // Base64 strict roundtrip
    let raw = [0x11u8; ML_KEM_768_PUBKEY_LEN];
    let b64 = base64_encode_std(&raw);
    assert_eq!(base64_decode_strict(&b64).unwrap(), raw);
    // Non-canonical base64 padding bits rejected
    assert!(base64_decode_strict("AB==").is_none());
}

// ---------------------------------------------------------------------------
// 1. CAP-24: RFC 5280 BasicConstraints / KeyUsage / PathLen / Leaf-Signed Forgery
// ---------------------------------------------------------------------------

#[test]
fn cap24_rfc5280_cert_chain_and_der_enforcement() {
    // Real ASN.1 DER parsing checks
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
    // Non-canonical DER BOOLEAN (0x01 instead of 0xFF) rejected
    assert!(parse_der_basic_constraints(&[0x30, 0x03, 0x01, 0x01, 0x01]).is_none());
    let ku = parse_der_key_usage(&[0x03, 0x02, 0x01, 0x06]).unwrap();
    assert!(ku.key_cert_sign() && ku.crl_sign() && !ku.digital_signature());

    let root = ca_cert("CN=Root", "CN=Root", 1, Some(1), true);
    let inter = ca_cert("CN=Intermediate", "CN=Root", 2, Some(0), true);
    let leaf = leaf_cert("CN=Leaf", "CN=Intermediate", 3, None);
    let pinned_root = root.cert_sha256;

    // Honest 3-cert chain passes
    assert!(verify_rfc5280_cert_chain(&[root.clone(), inter.clone(), leaf.clone()], &pinned_root, NOW).is_ok());

    // CAP-24 attack 1: Leaf signs a forged child certificate (forging device_chain[0])
    let forged_child = leaf_cert("CN=ForgedChild", "CN=Leaf", 4, None);
    assert_eq!(
        verify_rfc5280_cert_chain(
            &[root.clone(), inter.clone(), leaf.clone(), forged_child],
            &pinned_root,
            NOW
        ),
        Err(CertChainError::NonCaIssuer { index: 2 })
    );

    // CAP-24 attack 2: Intermediate missing keyCertSign KeyUsage
    let mut bad_ku_inter = inter.clone();
    bad_ku_inter.key_usage = Some(KeyUsage::new(KEY_USAGE_DIGITAL_SIGNATURE));
    bad_ku_inter.key_usage_der = None;
    assert_eq!(
        verify_rfc5280_cert_chain(&[root.clone(), bad_ku_inter, leaf.clone()], &pinned_root, NOW),
        Err(CertChainError::MissingKeyCertSign { index: 1 })
    );

    // CAP-24 attack 3: pathLenConstraint exceeded (root allows 0 intermediates, but 1 present)
    let strict_root = ca_cert("CN=Root", "CN=Root", 1, Some(0), true);
    assert_eq!(
        verify_rfc5280_cert_chain(&[strict_root, inter.clone(), leaf.clone()], &pinned_root, NOW),
        Err(CertChainError::PathLenConstraintExceeded {
            index: 0,
            max_allowed: 0,
            actual: 1
        })
    );

    // CAP-24 attack 4: Leaf has is_ca = true
    let ca_as_leaf = ca_cert("CN=LeafCA", "CN=Intermediate", 3, None, false);
    assert_eq!(
        verify_rfc5280_cert_chain(&[root.clone(), inter.clone(), ca_as_leaf], &pinned_root, NOW),
        Err(CertChainError::LeafMustNotBeCa)
    );

    // Fail-closed clock=0 rejected
    assert_eq!(
        verify_rfc5280_cert_chain(&[root, inter, leaf], &pinned_root, 0),
        Err(CertChainError::InvalidClock)
    );
}

// ---------------------------------------------------------------------------
// 2. CAP-25: AMD SEV-SNP Mandatory Non-Expired CRL + TCB Floor
// ---------------------------------------------------------------------------

#[test]
fn cap25_amd_sev_snp_mandatory_crl_and_tcb_floor() {
    let ark = ca_cert("CN=AMD-ARK-Genoa", "CN=AMD-ARK-Genoa", 1, Some(1), true);
    let ask = ca_cert("CN=AMD-ASK-Genoa", "CN=AMD-ARK-Genoa", 2, Some(0), true);
    let vcek = leaf_cert("CN=AMD-VCEK-Chip42", "CN=AMD-ASK-Genoa", 3, None);
    let launch_meas = [0x5Au8; 48];
    let min_tcb = AmdSnpTcbVersion {
        fmc: 0,
        bootloader: 3,
        tee: 1,
        snp: 8,
        microcode: 72,
    };
    let policy = AmdSnpPolicy {
        product: AmdSnpProduct::Genoa,
        pinned_ark_sha256: ark.cert_sha256,
        expected_measurement: sha256(&launch_meas),
        min_tcb,
        allow_debug: false,
        allow_migration_agent: false,
        max_vmpl: 0,
        min_guest_svn: 1,
    };
    let valid_crl = AmdSnpCrl {
        issuer: ark.subject.clone(),
        last_update: NOW - 3600,
        next_update: NOW + 3600,
        revoked_serials: vec![vec![99]],
        sig_verified: true,
    };
    let att = AmdSnpAttestation {
        cert_chain: vec![ark.clone(), ask.clone(), vcek.clone()],
        crls: vec![valid_crl.clone()],
        report_sig_ok: true,
        signing_key: 0,
        reported_tcb: min_tcb,
        vcek_ext_tcb: min_tcb,
        report_chip_id: [0x11; 64],
        vcek_ext_hw_id: [0x11; 64],
        guest_policy: 1 << 17, // RESERVED_MBO set, debug=0
        vmpl: 0,
        guest_svn: 2,
        launch_measurement: launch_meas,
        report_data: [0x22; 64],
    };

    let sealed = verify_amd_sev_snp(&policy, &att, NOW).expect("honest SNP must pass");
    assert_eq!(sealed.vendor(), TeeVendor::AmdSevSnp(AmdSnpProduct::Genoa));
    assert_eq!(sealed.tcb_posture(), TcbPosture::VerifiedFloor);

    // CAP-25 attack 1: Empty CRL list MUST be refused
    let mut no_crl = att.clone();
    no_crl.crls.clear();
    assert_eq!(
        verify_amd_sev_snp(&policy, &no_crl, NOW),
        Err(TeeError::SnpMissingCrl)
    );

    // CAP-25 attack 2: Expired CRL refused
    let mut exp_crl = att.clone();
    exp_crl.crls[0].next_update = NOW;
    assert_eq!(
        verify_amd_sev_snp(&policy, &exp_crl, NOW),
        Err(TeeError::SnpCrlNotCurrent)
    );

    // CAP-25 attack 3: Revoked VCEK serial refused
    let mut rev_vcek = att.clone();
    rev_vcek.crls[0].revoked_serials.push(vcek.serial.clone());
    assert_eq!(
        verify_amd_sev_snp(&policy, &rev_vcek, NOW),
        Err(TeeError::SnpCertificateRevoked)
    );

    // CAP-25 attack 4: TCB below floor MUST fail closed inside the gate
    let mut low_tcb = att.clone();
    low_tcb.reported_tcb.microcode = 71;
    low_tcb.vcek_ext_tcb.microcode = 71;
    assert_eq!(
        verify_amd_sev_snp(&policy, &low_tcb, NOW),
        Err(TeeError::SnpTcbBelowFloor)
    );

    // Debug guest forbidden
    let mut dbg = att;
    dbg.guest_policy |= 1 << 19;
    assert_eq!(
        verify_amd_sev_snp(&policy, &dbg, NOW),
        Err(TeeError::SnpDebugGuestForbidden)
    );
}

// ---------------------------------------------------------------------------
// 3. CAP-26: Intel TDX 1.5 (MR_SERVICETD + RTMR) & NVIDIA Hopper/Blackwell SPDM + FWID
// ---------------------------------------------------------------------------

#[test]
fn cap26_intel_tdx_servicetd_and_rtmr_policy() {
    let intel_root = ca_cert("CN=Intel-SGX-Root", "CN=Intel-SGX-Root", 1, Some(1), true);
    let pck_ca = ca_cert("CN=Intel-PCK-CA", "CN=Intel-SGX-Root", 2, Some(0), true);
    let pck_leaf = leaf_cert("CN=Intel-PCK-Leaf", "CN=Intel-PCK-CA", 3, None);

    let pin = IntelTdxMeasurementPin {
        mr_td: [0x10; 48],
        rt_mr0: [0x20; 48],
        rt_mr1: [0x30; 48],
        rt_mr2: [0x40; 48],
        pin_rtmr3: None,
    };
    let pinned_svc_td = [0x99; 48];
    let policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256,
        measurement_pin: pin.clone(),
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: vec![pinned_svc_td],
    };
    let att = IntelTdxAttestation {
        pck_cert_chain: vec![intel_root, pck_ca, pck_leaf],
        dcap_quote_sig_ok: true,
        tcb_status: "UpToDate".to_string(),
        mr_td: pin.mr_td,
        rt_mr0: pin.rt_mr0,
        rt_mr1: pin.rt_mr1,
        rt_mr2: pin.rt_mr2,
        rt_mr3: [0xFF; 48],
        mr_servicetd: Some(pinned_svc_td),
        report_data: [0x33; 64],
    };

    // Pinned nonzero TD 1.5 MR_SERVICETD passes (fixing dcap-qvl new_prod bug!)
    let sealed = verify_intel_tdx(&policy, &att, NOW).expect("pinned service TD must pass");
    assert_eq!(sealed.vendor(), TeeVendor::IntelTdx);

    // Unpinned nonzero MR_SERVICETD refused
    let mut rogue_svc = att.clone();
    rogue_svc.mr_servicetd = Some([0x77; 48]);
    assert_eq!(
        verify_intel_tdx(&policy, &rogue_svc, NOW),
        Err(TeeError::TdxServiceTdNotPinned)
    );

    // Wrong RTMR2 refused
    let mut bad_rtmr = att.clone();
    bad_rtmr.rt_mr2[0] ^= 1;
    assert_eq!(
        verify_intel_tdx(&policy, &bad_rtmr, NOW),
        Err(TeeError::TdxRtmrMismatch(2))
    );

    // OutOfDate TCB refused
    let mut ood = att.clone();
    ood.tcb_status = "OutOfDate".to_string();
    assert_eq!(
        verify_intel_tdx(&policy, &ood, NOW),
        Err(TeeError::TdxTcbStatusRejected("OutOfDate".to_string()))
    );

    // Clock fallback 0 refused
    assert_eq!(
        verify_intel_tdx(&policy, &att, 0),
        Err(TeeError::InvalidClock)
    );
}

fn make_nvidia_fixture(arch: GpuArch, nonce: [u8; 32], fwid: [u8; 48]) -> (NvidiaGpuPolicy, NvidiaGpuAttestation) {
    let dev_root = ca_cert("CN=NVIDIA-Device-Root", "CN=NVIDIA-Device-Root", 1, Some(1), true);
    let dev_inter = ca_cert("CN=NVIDIA-Device-L1", "CN=NVIDIA-Device-Root", 2, Some(0), true);
    let dev_leaf = leaf_cert("CN=NVIDIA-GPU-Leaf", "CN=NVIDIA-Device-L1", 3, Some(fwid));

    let rim_root = ca_cert("CN=NVIDIA-CoRIM-Root", "CN=NVIDIA-CoRIM-Root", 10, Some(1), true);
    let rim_inter = ca_cert("CN=NVIDIA-CoRIM-L1", "CN=NVIDIA-CoRIM-Root", 11, Some(0), true);
    let drv_leaf = leaf_cert("CN=NVIDIA-Driver-RIM", "CN=NVIDIA-CoRIM-L1", 12, None);
    let vbios_leaf = leaf_cert("CN=NVIDIA-VBIOS-RIM", "CN=NVIDIA-CoRIM-L1", 13, None);

    let m1 = vec![0xAAu8; 48];
    let m2 = vec![0xBBu8; 48];
    let report_bytes = build_spdm_report(
        nonce,
        [0x55; 32],
        &[(1, &m1), (2, &m2)],
        &[
            (OPAQUE_FWID, &fwid),
            (OPAQUE_PROJECT, b"1010"),
            (OPAQUE_PROJECT_SKU, b"0200"),
            (OPAQUE_CHIP_SKU, b"890"),
        ],
    );
    let mut drv_goldens = BTreeMap::new();
    drv_goldens.insert(1, vec![m1]);
    let mut vbios_goldens = BTreeMap::new();
    vbios_goldens.insert(2, vec![m2]);

    let make_ocsp = |c: &CertRecord| NvidiaOcspResponse {
        cert_sha256: c.cert_sha256,
        status: NvidiaOcspStatus::Good,
        this_update: NOW - 600,
        next_update: NOW + 600,
        sig_verified: true,
    };
    let ocsp_responses = vec![
        make_ocsp(&dev_inter),
        make_ocsp(&dev_leaf),
        make_ocsp(&rim_inter),
        make_ocsp(&drv_leaf),
        make_ocsp(&vbios_leaf),
    ];

    let policy = NvidiaGpuPolicy {
        arch,
        pinned_device_root_sha256: dev_root.cert_sha256,
        pinned_corim_root_sha256: rim_root.cert_sha256,
        expected_driver_version: "570.124.06".to_string(),
        expected_vbios_version: "96.00.A5.00.01".to_string(),
        pinned_fwid: fwid,
    };
    let att = NvidiaGpuAttestation {
        spdm_report_bytes: report_bytes,
        device_cert_chain: vec![dev_root, dev_inter, dev_leaf],
        spdm_sig_ok: true,
        driver_rim: NvidiaRimManifest {
            arch,
            version: "570.124.06".to_string(),
            cert_chain: vec![rim_root.clone(), rim_inter.clone(), drv_leaf],
            rim_sig_ok: true,
            expected_fwid: fwid,
            golden_measurements: drv_goldens,
        },
        vbios_rim: NvidiaRimManifest {
            arch,
            version: "96.00.A5.00.01".to_string(),
            cert_chain: vec![rim_root, rim_inter, vbios_leaf],
            rim_sig_ok: true,
            expected_fwid: fwid,
            golden_measurements: vbios_goldens,
        },
        ocsp_responses,
    };
    (policy, att)
}

#[test]
fn cap26_nvidia_hopper_and_blackwell_spdm_rim_fwid_pin() {
    let nonce = [0x42; 32];
    let fwid = [0xCD; 48];
    assert_eq!(extract_der_dice_fwid(&{
        let mut v = vec![0x04, 0x30];
        v.extend_from_slice(&fwid);
        v
    }), Some(fwid));

    for arch in [GpuArch::HopperH100, GpuArch::BlackwellB200] {
        let (policy, att) = make_nvidia_fixture(arch, nonce, fwid);
        let parsed = parse_spdm_gpu_report(&att.spdm_report_bytes).expect("SPDM 1.1 parse");
        assert_eq!(parsed.fwid(), Some(fwid));

        let sealed = verify_nvidia_gpu(&policy, &att, &nonce, NOW).expect("GPU must verify");
        assert_eq!(sealed.vendor(), TeeVendor::NvidiaGpu(arch));
        assert_eq!(sealed.gpu_fwid(), Some(fwid));

        // CAP-26 attack 1: Policy FWID mismatch refused
        let mut wrong_pin = policy.clone();
        wrong_pin.pinned_fwid[0] ^= 0xFF;
        assert_eq!(
            verify_nvidia_gpu(&wrong_pin, &att, &nonce, NOW),
            Err(TeeError::GpuFwidRimPinMismatch)
        );

        // CAP-26 attack 2: Cert DICE FWID differs from SPDM TLV 20 FWID
        let mut forged_cert_fwid = att.clone();
        let mut bad_fwid = fwid;
        bad_fwid[47] ^= 1;
        let mut ext = vec![0x30, 0x32, 0x04, 0x30];
        ext.extend_from_slice(&bad_fwid);
        forged_cert_fwid.device_cert_chain[2].dice_fwid_ext_der = Some(ext);
        assert_eq!(
            verify_nvidia_gpu(&policy, &forged_cert_fwid, &nonce, NOW),
            Err(TeeError::GpuFwidCertMismatch)
        );

        // CAP-26 attack 3: Trailing byte after SPDM signature refused
        let mut trailing = att.clone();
        trailing.spdm_report_bytes.push(0x00);
        assert_eq!(
            verify_nvidia_gpu(&policy, &trailing, &nonce, NOW),
            Err(TeeError::SpdmTrailingBytes(1))
        );

        // CAP-24 attack on GPU chain: Leaf-signed child cert appended to device chain
        let mut leaf_forged = att.clone();
        let rogue_child = leaf_cert("CN=RogueGpuChild", "CN=NVIDIA-GPU-Leaf", 99, Some(fwid));
        leaf_forged.device_cert_chain.push(rogue_child);
        assert_eq!(
            verify_nvidia_gpu(&policy, &leaf_forged, &nonce, NOW),
            Err(TeeError::CertChain(CertChainError::NonCaIssuer { index: 2 }))
        );

        // Revoked OCSP refused
        let mut revoked = att;
        revoked.ocsp_responses[0].status = NvidiaOcspStatus::Revoked;
        assert_eq!(
            verify_nvidia_gpu(&policy, &revoked, &nonce, NOW),
            Err(TeeError::GpuOcspRevoked)
        );
    }
}

#[test]
fn aws_nitro_cap24_and_honest_tcb_posture() {
    let root = ca_cert("CN=AWS-Nitro-Root-G1", "CN=AWS-Nitro-Root-G1", 1, Some(1), false);
    let inter = ca_cert("CN=AWS-Nitro-Regional", "CN=AWS-Nitro-Root-G1", 2, Some(0), false);
    let leaf = leaf_cert("CN=AWS-NSM-Leaf", "CN=AWS-Nitro-Regional", 3, None);
    let meas = fold_nitro_pcrs(b"pcr0", b"pcr1", b"pcr2");
    let policy = AwsNitroPolicy {
        pinned_root_sha256: root.cert_sha256,
        expected_measurement: meas,
        max_age_secs: Some(3600),
    };
    let att = AwsNitroAttestation {
        cert_chain: vec![root, inter, leaf],
        cose_es384_sig_ok: true,
        doc_timestamp_ms: NOW * 1000,
        pcr0: b"pcr0".to_vec(),
        pcr1: b"pcr1".to_vec(),
        pcr2: b"pcr2".to_vec(),
        user_data: [0x77; 64],
    };
    let sealed = verify_aws_nitro(&policy, &att, NOW).expect("honest Nitro passes");
    assert_eq!(sealed.vendor(), TeeVendor::AwsNitro);
    assert_eq!(sealed.tcb_posture(), TcbPosture::NoPolicyOnPlatform);

    let mut future = att;
    future.doc_timestamp_ms = (NOW + 120) * 1000;
    assert_eq!(
        verify_aws_nitro(&policy, &future, NOW),
        Err(TeeError::NitroFutureTimestamp { ahead_secs: 120 })
    );
}

// ---------------------------------------------------------------------------
// 4. V3 & V4: Registry-Pinned TLSNotary & CallTree (Rogue Notary Key Refused!)
// ---------------------------------------------------------------------------

#[test]
fn v3_rogue_notary_key_and_v4_redaction_and_calltree() {
    let trusted_notary_key = sha256(b"obend-trusted-notary-pk-v1");
    let rogue_notary_key = sha256(b"attacker-self-hosted-rogue-notary");
    let registry = PinnedNotaryRegistry::new(vec![PinnedNotaryEntry {
        operator_id: "obend-notary-prod-1".to_string(),
        notary_key_sha256: trusted_notary_key,
        allowed_servers: vec!["api.coinbase.com".to_string(), "api.github.com".to_string()],
        valid_from: NOW - 86_400,
        valid_until: NOW + 86_400,
    }]);

    let honest_env = TlsnTranscriptEnvelope {
        server_name: "api.coinbase.com".to_string(),
        expected_path: "/v2/prices/BTC-USD/spot".to_string(),
        connection_time: NOW - 10,
        sent_bytes: b"GET /v2/prices/BTC-USD/spot HTTP/1.1\r\nHost: api.coinbase.com\r\n\r\n"
            .to_vec(),
        recv_bytes: b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"data\":{\"base\":\"BTC\",\"amount\":\"98450.25\"}}"
            .to_vec(),
        unauthed_recv_ranges: vec![],
        tls_cert_chain_ok: true,
        mpc_signature_ok: true,
        authenticated_notary_key_sha256: trusted_notary_key,
        claimed_notary_key_hex: Some(hex_encode_lower(&trusted_notary_key)),
    };

    let verified = verify_tlsn_transcript(&registry, &honest_env, Some("data.amount"), NOW)
        .expect("registry-pinned transcript passes");
    assert_eq!(verified.extracted_field(), Some("98450.25"));
    assert_eq!(verified.notary_operator(), "obend-notary-prod-1");
    assert_eq!(verified.legs().len(), 4);

    // V3 ATTACK: Attacker signs transcript with rogue notary AND puts rogue key in claimed_notary_key_hex!
    let mut rogue_env = honest_env.clone();
    rogue_env.authenticated_notary_key_sha256 = rogue_notary_key;
    rogue_env.claimed_notary_key_hex = Some(hex_encode_lower(&rogue_notary_key));
    assert_eq!(
        verify_tlsn_transcript(&registry, &rogue_env, Some("data.amount"), NOW),
        Err(OracleError::UntrustedNotaryKey)
    );

    // V4 ATTACK: Unauthenticated redacted bytes ('X' placeholder) inside HTTP body
    let mut redacted = honest_env.clone();
    let body_idx = redacted.recv_bytes.len() - 8;
    redacted.unauthed_recv_ranges = vec![(body_idx, body_idx + 4)];
    assert_eq!(
        verify_tlsn_transcript(&registry, &redacted, Some("data.amount"), NOW),
        Err(OracleError::UnauthedBodyBytes {
            range_start: body_idx,
            range_end: body_idx + 4
        })
    );

    // V3 URL path mismatch refused
    let mut wrong_path = honest_env.clone();
    wrong_path.expected_path = "/v2/prices/ETH-USD/spot".to_string();
    assert_eq!(
        verify_tlsn_transcript(&registry, &wrong_path, Some("data.amount"), NOW),
        Err(OracleError::RequestPathMismatch)
    );

    // RFC 8259 duplicate-key JSON smuggling refused
    assert_eq!(
        extract_json_field_strict(r#"{"amount":"100","amount":"999999"}"#, "amount"),
        Err(OracleError::JsonDuplicateKey("amount".to_string()))
    );

    // Multi-hop CallTree DAG verification
    let hop2_env = TlsnTranscriptEnvelope {
        server_name: "api.github.com".to_string(),
        expected_path: "/repos/obend/oracle?price=98450.25".to_string(),
        connection_time: NOW - 5,
        sent_bytes: b"GET /repos/obend/oracle?price=98450.25 HTTP/1.1\r\nHost: api.github.com\r\n\r\n"
            .to_vec(),
        recv_bytes: b"HTTP/1.1 200 OK\r\n\r\n{\"ok\":true}".to_vec(),
        unauthed_recv_ranges: vec![],
        tls_cert_chain_ok: true,
        mpc_signature_ok: true,
        authenticated_notary_key_sha256: trusted_notary_key,
        claimed_notary_key_hex: None,
    };
    let v2 = verify_tlsn_transcript(&registry, &hop2_env, Some("ok"), NOW).unwrap();
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
    let ct = verify_calltree_recording(&registry, &rec, &expected_root, NOW)
        .expect("honest calltree passes");
    assert_eq!(ct.root_digest(), expected_root);

    let bad_root = sha256(b"wrong-root");
    assert!(matches!(
        verify_calltree_recording(&registry, &rec, &bad_root, NOW),
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

    // Mint sealed Intel TDX evidence whose report_data[0..32] commits to (nonce_hex || pubkey_b64)
    let intel_root = ca_cert("CN=Intel-SGX-Root", "CN=Intel-SGX-Root", 1, Some(1), true);
    let pck_ca = ca_cert("CN=Intel-PCK-CA", "CN=Intel-SGX-Root", 2, Some(0), true);
    let pck_leaf = leaf_cert("CN=Intel-PCK-Leaf", "CN=Intel-PCK-CA", 3, None);
    let pin = IntelTdxMeasurementPin {
        mr_td: [0x11; 48],
        rt_mr0: [0x22; 48],
        rt_mr1: [0x33; 48],
        rt_mr2: [0x44; 48],
        pin_rtmr3: None,
    };
    let tdx_policy = IntelTdxPolicy {
        pinned_intel_root_sha256: intel_root.cert_sha256,
        measurement_pin: pin.clone(),
        accepted_tcb_statuses: vec!["UpToDate".to_string()],
        accepted_service_tds: vec![],
    };
    let mut rd = [0u8; 64];
    rd[..32].copy_from_slice(&chutes_report_data_binding(&nonce_hex, &pubkey_b64));
    let cpu_tee = verify_intel_tdx(
        &tdx_policy,
        &IntelTdxAttestation {
            pck_cert_chain: vec![intel_root, pck_ca, pck_leaf],
            dcap_quote_sig_ok: true,
            tcb_status: "UpToDate".to_string(),
            mr_td: pin.mr_td,
            rt_mr0: pin.rt_mr0,
            rt_mr1: pin.rt_mr1,
            rt_mr2: pin.rt_mr2,
            rt_mr3: [0; 48],
            mr_servicetd: Some(NO_SERVICE_TD),
            report_data: rd,
        },
        NOW,
    )
    .expect("TDX CPU tee");

    // Mint paired NVIDIA Blackwell B200 GPU evidence bound to the SAME nonce_bytes
    let (gpu_policy, gpu_att) = make_nvidia_fixture(GpuArch::BlackwellB200, nonce_bytes, [0xEF; 48]);
    let gpu_tee = verify_nvidia_gpu(&gpu_policy, &gpu_att, &nonce_bytes, NOW).expect("B200 GPU tee");

    let input = E2eeChannelInput {
        chute_id: "chute-qwen35".to_string(),
        instance_id: "inst-b200-01".to_string(),
        attestation_nonce_hex: nonce_hex.clone(),
        e2e_pubkey_b64: pubkey_b64,
    };
    let ch_policy = E2eeChannelPolicy::default();
    let channel = verify_e2ee_channel(&ch_policy, &input, &cpu_tee, &[gpu_tee.clone()], NOW)
        .expect("CPU+GPU bound E2EE channel passes");

    // Directional bound keys differ across Request / Response / Stream
    let shared = [0x91u8; 32];
    let kem_ct = [0x24u8; 1088];
    let k_req = channel
        .derive_bound_session_key(&shared, &kem_ct, ChannelDirection::Request)
        .unwrap();
    let k_resp = channel
        .derive_bound_session_key(&shared, &kem_ct, ChannelDirection::Response)
        .unwrap();
    assert_ne!(k_req, k_resp);

    // Single-use invocation nonce + TTL guard
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

    // ATTACK 1 (MITM pubkey swap): Attacker swaps e2e_pubkey_b64 for their own ML-KEM-768 key
    let mut mitm_pk = mlkem_pk;
    mitm_pk[0] ^= 0xFF;
    let mut mitm_input = input.clone();
    mitm_input.e2e_pubkey_b64 = base64_encode_std(&mitm_pk);
    assert_eq!(
        verify_e2ee_channel(&ch_policy, &mitm_input, &cpu_tee, &[gpu_tee], NOW),
        Err(E2eeChannelError::ReportDataBindingMismatch)
    );

    // ATTACK 2: Missing GPU attestation refused under default policy
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
    // 1. O(|E|) SDD-Laplacian factor witness for 2x2 SDD matrix P = [[2, -1], [-1, 2]] at scale 9:
    //    P = 1 * (e_0 - e_1)(e_0 - e_1)^T + diag(1, 1)
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
    let admission = witness.to_sdd_certificate().expect("SDD cert from O(|E|) factor");
    assert_eq!(admission.exact_entries(), &[2 * s, -s, -s, 2 * s]);
    assert_eq!(admission.row_radii(), &[s, s]);

    // Negative edge weight in SDD factor refused
    let mut bad_edge = witness.clone();
    bad_edge.edges[0].weight = -1;
    assert_eq!(
        verify_sdd_factor_witness(&bad_edge),
        Err(SddFactorError::NegativeEdgeWeight { edge_index: 0 })
    );

    // Non-diagonally-dominant (indefinite) matrix refused by FHSDD001
    assert_eq!(
        ExactSddPsdCertificate::from_exact_matrix(
            2,
            QP_CERT_EXACT_SCALE,
            vec![s, 2 * s, 2 * s, s],
            vec![2 * s, 2 * s]
        ),
        Err(ExactSddPsdCertificateError::NotDiagonallyDominant { row: 0 })
    );

    // 2. Exact-zero KKT QP:
    //    min 1/2 x^T P x + q^T x   s.t.  1 <= x0 + x1 <= 1
    //    P = [[2, -1], [-1, 2]], q = [-1, -1]
    //    At x* = [1/2, 1/2]: Px* = [1/2, 1/2], q = [-1, -1], A = [[1, 1]], y* = [1/2]
    //    Stationarity: Px* + q + A^T y* = [1/2 - 1 + 1/2, 1/2 - 1 + 1/2] = [0, 0]
    //    Primal: Ax* = 1 in [1, 1]; Normal cone: Ax* - clamp(1 + 1/2, 1, 1) = 0!
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
    let bundle = ExactQpCertificateBundle::new(admission.clone(), kkt.clone())
        .expect("valid FHQPB001 bundle");
    let wire = bundle.to_wire_bytes().expect("encode FHQPB001");

    let verified_zero = verify_zero_kkt_certified_qp(&problem, &wire)
        .expect("exact-zero KKT QP verifies");
    assert_eq!(verified_zero.program_digest(), problem.program_digest());
    // 2 * f(x*) = x^T P x + 2 q^T x = (2*(1/4) - 2*(1/4) + 2*(1/4)) + 2*(-1) = 1/2 - 2 = -3/2
    // Scaled by S^3: (-3/2) * S^3 = -15 * 10^(3*9 - 1)
    assert_eq!(
        verified_zero.objective().twice_numerator(),
        -(3 * s * s * (s / 2))
    );

    // ATTACK 1 (tooth_matrix_pin_omitted_unsound): Admission is PSD for I_2, while KKT uses P!
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

    // Wire-level Matrix-Pin attack: splice I_2's FHSDD001 bytes into the FHQPB001 wire envelope
    // and recompute a valid outer SHA-256 checksum; from_wire_bytes MUST still refuse it!
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

    // ATTACK 2 (wrong-sign dual forgery): Box constraint 0 <= x0 <= 2, min x0^2 - 2 x0
    // Optimal is x0 = 1 (y = 0). At suboptimal x0 = 0, Px + q = -2; forging y = +2 gives
    // zero stationarity (-2 + 2 = 0) and zero primal residual (0 in [0, 2]),
    // BUT normal-cone residual |0 - clamp(0 + 2, 0, 2)| = 2 rejects it!
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
    assert!(forged_rep.primal_feasible);
    assert!(forged_rep.dual_feasible);
    assert!(!forged_rep.normal_cone);
    assert!(!forged_rep.valid);

    // ATTACK 3: Public problem binding rejects a certificate for a different linear cost `q`
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

    // ATTACK 4: i128 arithmetic overflow fails closed
    let mut ovf = kkt;
    ovf.x[0] = i128::MAX;
    let ovf_rep = ovf.check();
    assert!(ovf_rep.overflow && !ovf_rep.valid);

    // 3. Attested off-chain solver quote bound to sealed VerifiedTeeEvidence
    let quote_nonce = [0x88u8; 32];
    let mut wire_checksum = [0u8; 32];
    wire_checksum.copy_from_slice(&wire[wire.len() - 32..]);
    let commitment =
        solver_quote_commitment(&problem.program_digest(), &wire_checksum, &quote_nonce);

    let root = ca_cert("CN=AWS-Nitro-Root-G1", "CN=AWS-Nitro-Root-G1", 1, Some(1), false);
    let inter = ca_cert("CN=AWS-Nitro-Regional", "CN=AWS-Nitro-Root-G1", 2, Some(0), false);
    let leaf = leaf_cert("CN=AWS-NSM-Solver", "CN=AWS-Nitro-Regional", 3, None);
    let meas = fold_nitro_pcrs(b"solver-pcr0", b"solver-pcr1", b"solver-pcr2");
    let mut user_data = [0u8; 64];
    user_data[..32].copy_from_slice(&commitment);
    let solver_tee = verify_aws_nitro(
        &AwsNitroPolicy {
            pinned_root_sha256: root.cert_sha256,
            expected_measurement: meas,
            max_age_secs: Some(3600),
        },
        &AwsNitroAttestation {
            cert_chain: vec![root, inter, leaf],
            cose_es384_sig_ok: true,
            doc_timestamp_ms: NOW * 1000,
            pcr0: b"solver-pcr0".to_vec(),
            pcr1: b"solver-pcr1".to_vec(),
            pcr2: b"solver-pcr2".to_vec(),
            user_data,
        },
        NOW,
    )
    .expect("solver TEE");

    let quote = verify_attested_solver_quote(&solver_tee, &problem, &wire, &quote_nonce)
        .expect("attested solver quote passes");
    assert_eq!(quote.quote_commitment(), commitment);

    // Wrong quote nonce rejected
    let bad_nonce = [0x99u8; 32];
    assert_eq!(
        verify_attested_solver_quote(&solver_tee, &problem, &wire, &bad_nonce),
        Err(ExactQpCertificateBundleError::QuoteAttestationMismatch)
    );
}
