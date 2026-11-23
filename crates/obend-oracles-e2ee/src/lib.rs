#![forbid(unsafe_code)]
//! `obend-oracles-e2ee` — Phase-1 hardened multi-vendor TEE/GPU attestation gate (`CAP-24..26`),
//! registry-pinned TLSNotary / `calltree` verifier & E2EE channel binding (`V3`/`V4`), and
//! pure-integer `FHSDD001` / `FHQPB001` KKT oracle verifier (`0` floats, `0` external crates).
//!
//! Quarried and hardened from `breadstuffs/{tee-verify,calltree,dregg-chutes-e2ee,fhir}` and
//! `dregg-oracle` (remediating `CAP-24`, `CAP-25`, `CAP-26`, `V3`, `V4`, opt-in GPU bypass,
//! missing AEAD AAD, and omitted `FHQPB001` matrix-pin).

pub mod bigint;
pub mod chacha20poly1305;
pub mod curves;
pub mod ed25519;
pub mod kkt;
pub mod mlkem768;
pub mod rsa;
pub mod sha256;
pub mod sha512;
pub mod she_ceremony;
pub mod tee;
pub mod tlsn_e2ee;

pub use chacha20poly1305::{
    chacha20_block, chacha20_xor, chacha20poly1305_open, chacha20poly1305_open_combined,
    chacha20poly1305_seal, chacha20poly1305_seal_combined, poly1305_mac, AeadError, Poly1305,
    CHACHA20_KEY_LEN, CHACHA20_NONCE_LEN, POLY1305_TAG_LEN,
};
pub use mlkem768::{
    byte_decode_1, byte_decode_10, byte_decode_12, byte_decode_4, byte_encode_1, byte_encode_10,
    byte_encode_12, byte_encode_4, compress_d, decompress_d, keccak_f1600, ml_kem_768_decaps,
    ml_kem_768_decaps_internal, ml_kem_768_encaps, ml_kem_768_encaps_internal,
    ml_kem_768_keygen_internal, multiply_ntts, ntt, ntt_inv, sample_ntt, sample_poly_cbd2,
    sha3_256, sha3_512, shake256_into, validate_decaps_key, validate_encaps_key, KeccakSponge,
    MlKemError, Poly, Shake128, Shake256, ML_KEM_768_DK_LEN, ML_KEM_768_EK_LEN, ML_KEM_768_K,
    ML_KEM_768_SS_LEN, ML_KEM_N, ML_KEM_Q,
};

pub use curves::{
    encode_ecdsa_der, parse_ecdsa_der, verify_ecdsa_raw, verify_signature, CryptoError,
    FixtureSigner, HashAlg, SignatureAlgorithm, SubjectPublicKey,
};
pub use kkt::{
    verify_attested_solver_quote, verify_certified_qp, verify_sdd_factor_witness,
    verify_zero_kkt_certified_qp, ExactQpCertificateBundle, ExactQpCertificateBundleError,
    ExactQpKktCert, ExactQpObjectiveValue, ExactQpProblem, ExactSddPsdCertificate,
    ExactSddPsdCertificateError, KktResidualReport, QpProblemBindingError, SddFactorEdge,
    SddFactorError, SddFactorWitness, VerifiedExactQpCertificate, VerifiedSolverQuote,
    VerifiedZeroKktQpCertificate, FHQPB001_MAGIC, FHSDD001_MAGIC, MAX_EXACT_SDD_DIMENSION,
    MAX_QP_BUNDLE_DIMENSION, MAX_QP_SCALE, QP_CERT_EXACT_SCALE,
};
pub use sha256::{
    base64_decode_strict, ct_eq, hex_decode_strict, hex_encode_lower, hkdf_sha256_expand,
    hkdf_sha256_extract, hmac_sha256, sha256, Sha256,
};
pub use sha512::{hmac_sha384, hmac_sha512, sha384, sha512, Sha512};
pub use she_ceremony::{
    apply_oracle_attested_actuation, apply_she_turn, encode_she_field, encode_she_fields,
    encode_she_floors, jbr_per_query_milli_bits, legacy_withdrawn_cbr_milli_bits,
    proven_zkml_milli_bits, run_she_trace, she_cshake256_32, she_floors_digest, she_leb128,
    she_payload_digest, she_turn_envelope_digest, she_turn_preimage, udr_per_query_milli_bits,
    ActuationTurnProposal, CandidateComputation, MandateAttenuation, SealedOracleIngress,
    SettledActuationRecord, SheFloor, SheRefusal, SheState, SheTurn, UpgradeAuthorityClaim,
    UpgradeJudgeProposal, ZkmlSoundnessRegime, SHE_MIN_PROVEN_ZKML_MILLI_BITS,
};
pub use tee::{
    aws_nitro_cose_sig_structure, chutes_report_data_binding, encode_der_basic_constraints,
    encode_der_key_usage, extract_der_dice_fwid, fixture_build_amd_snp_report,
    fixture_build_aws_nitro_cose, fixture_build_intel_tdx_quote, fixture_build_nvidia_rim_swid_xml,
    fixture_issue_cert_der, fixture_issue_crl_der, fixture_issue_ocsp_der,
    fixture_sign_spdm_report, fold_nitro_pcrs, fold_tdx_measurement, parse_amd_snp_report,
    parse_der_basic_constraints, parse_der_key_usage, parse_intel_tdx_quote,
    parse_pem_cert_records, parse_spdm_gpu_report, verify_amd_sev_snp, verify_aws_nitro,
    verify_intel_tdx, verify_nvidia_gpu, verify_nvidia_rim_swid, verify_rfc5280_cert_chain,
    AmdSnpAttestation, AmdSnpCrl, AmdSnpPolicy, AmdSnpProduct, AmdSnpTcbVersion,
    AwsNitroAttestation, AwsNitroPolicy, BasicConstraints, CertChainError, CertRecord,
    FixtureCertSpec, FixtureNitroDocFields, FixtureSnpReportFields, FixtureTdxQuoteFields, GpuArch,
    IntelTdxAttestation, IntelTdxMeasurementPin, IntelTdxPolicy, KeyUsage, NvidiaGpuAttestation,
    NvidiaGpuPolicy, NvidiaOcspResponse, NvidiaOcspStatus, NvidiaRimManifest, ParsedAmdSnpReport,
    ParsedIntelTdxQuote, SpdmGpuReport, TcbPosture, TeeError, TeeVendor, VerifiedSwidRim,
    VerifiedTeeEvidence, COSE_PROTECTED_ES384, INTEL_QE_VENDOR_ID, KEY_USAGE_CRL_SIGN,
    KEY_USAGE_DIGITAL_SIGNATURE, KEY_USAGE_KEY_CERT_SIGN, MAX_FUTURE_SKEW_SECS, NO_SERVICE_TD,
    OPAQUE_CHIP_SKU, OPAQUE_FWID, OPAQUE_PROJECT, OPAQUE_PROJECT_SKU, SGX_QE_REPORT_BODY_LEN,
    SNP_REPORT_LEN, SNP_SIGNED_BODY_LEN, SPDM_NONCE_LEN, SPDM_REQUEST_LEN, SPDM_SIGNATURE_LEN,
    TDX_QUOTE_HEADER_LEN, TDX_TD10_BODY_LEN, TDX_TD15_BODY_LEN, TEE_TYPE_TDX,
};
pub use tlsn_e2ee::{
    derive_channel_aad, derive_chutes_session_key, extract_json_field_strict, fixture_notarize,
    notary_key_fingerprint, tlsn_attestation_preimage, verify_calltree_recording,
    verify_e2ee_channel, verify_tlsn_transcript, CallTreeEdge, CallTreeError, CallTreeHop,
    CallTreeRecording, ChannelDirection, E2eeChannelError, E2eeChannelInput, E2eeChannelPolicy,
    E2eeSessionGuard, OracleError, PinnedNotaryEntry, PinnedNotaryRegistry, TlsnTranscriptEnvelope,
    VerificationLeg, VerifiedCallTree, VerifiedE2eeChannel, VerifiedHttpsTranscript,
    CHUTES_NONCE_HEX_LEN, E2EE_INFO_REQ, E2EE_INFO_RESP, E2EE_INFO_STREAM, MAX_JSON_BODY_BYTES,
    MAX_JSON_PATH_DEPTH, ML_KEM_768_CT_LEN, ML_KEM_768_PUBKEY_LEN,
};
