//! `obend-zk-receipt`: Executable finite-law policy and authority verification CLI for `Obend`'s
//! Dual-Track (`Canopy` Track H + `PikkuFold`/`Akita` Track L) + `ZkBiscuit` + `DetCbor` receipts.
//!
//! Subcommands:
//! - `prove --root-secret <file> [--policy <policy.cbor>] [--amendment <exec.cbor>] [--target-organ <name>] [--out <file>] [--nonce <u64>] [--epoch <u64>]`
//! - `verify --root-secret <file> --current-epoch <u64> --in <file> [--policy <policy.cbor>] [--target-organ <name>] [--required-rights <u64>] [--nullifier-log <file>]`
//! - `tamper-test`
//! - `bench [--iters <usize>]`

#![forbid(unsafe_code)]

use std::env;
use std::fs;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use obend_crypto_exec::amend_cli::{
    AmendmentExecution, AmendmentProposal, AmendmentVerifierState, FastReceiptProfile, RefusalCode,
    RevocationSet, SerializedPolicySpec, SignedAmendmentEnvelope, ZkBiscuitChain,
    example_amendment_execution, prove_amendment_envelope,
};
use obend_crypto_exec::goldilocks::Goldilocks;
use obend_crypto_exec::pikkufold::RingElem;
use obend_crypto_exec::transcript::cshake256_32;

const DEFAULT_ROOT_LABEL: &[u8] = b"polis-cathedral-root-authority-v1";
const DEFAULT_POLICY_LABEL: &str = "finite-law16-bedrock";
const DEFAULT_AMENDMENT_LABEL: &str = "recover";
const DEFAULT_TARGET_ORGAN: &str = "Obend.Trailblaze.StageBInstances";

const REPLAY_LOG_MAGIC: &[u8; 8] = b"OBNUL004";
const REPLAY_RECORD_LEN: usize = 176;

fn hex32(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out
}

fn load_policy_spec(
    policy_arg: &str,
    target_organ_override: Option<&str>,
) -> Result<SerializedPolicySpec, String> {
    let mut spec = if policy_arg == DEFAULT_POLICY_LABEL {
        SerializedPolicySpec::default_finite_law16()
    } else {
        let raw = fs::read(policy_arg)
            .map_err(|e| format!("cannot read serialized policy file `{policy_arg}`: {e}"))?;
        SerializedPolicySpec::from_det_cbor_bytes(&raw)
            .map_err(|e| format!("invalid canonical DetCbor policy `{policy_arg}`: {e}"))?
    };
    if let Some(organ) = target_organ_override {
        if organ.is_empty() {
            return Err(String::from("--target-organ cannot be empty"));
        }
        spec.target_organ = String::from(organ);
    }
    spec.validate()
        .map_err(|e| format!("invalid policy specification: {e:?}"))?;
    Ok(spec)
}

fn load_amendment_execution(
    amendment_arg: &str,
    policy_spec: &SerializedPolicySpec,
) -> Result<AmendmentExecution, String> {
    if amendment_arg == DEFAULT_AMENDMENT_LABEL {
        let mut ex = example_amendment_execution();
        ex.bedrock = policy_spec.bedrock;
        ex.bedrock_seed = policy_spec.bedrock_seed;
        ex.old = policy_spec.prior_clauses.clone();
        Ok(ex)
    } else {
        let raw = fs::read(amendment_arg)
            .map_err(|e| format!("cannot read serialized amendment file `{amendment_arg}`: {e}"))?;
        AmendmentExecution::from_det_cbor_bytes(&raw)
            .map_err(|e| format!("invalid canonical DetCbor amendment `{amendment_arg}`: {e}"))
    }
}

fn mint_default_chain(root_secret: [u8; 32], nonce: u64, epoch: u64) -> ZkBiscuitChain {
    let root_max = epoch.saturating_add(1_000);
    let mid_max = epoch.saturating_add(500);
    let leaf_max = epoch.saturating_add(250);
    ZkBiscuitChain::mint_root(
        root_secret,
        101,
        0b1111_1111,
        root_max,
        "genesis:polis-council",
    )
    .attenuate(
        &root_secret,
        202,
        0b0011_1111,
        mid_max,
        "delegate:clustergov-quorum",
    )
    .expect("valid hop 1 attenuation")
    .attenuate(
        &root_secret,
        303,
        0b0000_1111,
        leaf_max,
        &format!("leaf:amendment-prover:{nonce}"),
    )
    .expect("valid hop 2 attenuation")
}

fn build_demo_inputs(
    root_secret: [u8; 32],
    nonce: u64,
    epoch: u64,
) -> (
    [u8; 32],
    [u8; 32],
    AmendmentExecution,
    AmendmentProposal,
    ZkBiscuitChain,
) {
    let exec = example_amendment_execution();
    let policy_digest = exec.bedrock_digest();
    let amendment_digest = exec.turn_digest();
    let chain = mint_default_chain(root_secret, nonce, epoch);
    let proposal = AmendmentProposal {
        policy_digest,
        amendment_digest,
        prior_digest: exec.prior_digest(),
        epoch,
        nonce,
        required_rights: 0b0000_0101,
        target_organ: String::from(DEFAULT_TARGET_ORGAN),
    };
    (root_secret, policy_digest, exec, proposal, chain)
}

fn read_root_secret(path: Option<&str>) -> Result<[u8; 32], String> {
    let path = path.ok_or("--root-secret <32-byte key file> is required")?;
    let bytes = fs::read(path).map_err(|_| String::from("cannot read root-secret file"))?;
    bytes
        .try_into()
        .map_err(|_| String::from("root-secret file must contain exactly 32 bytes"))
}

fn default_nullifier_log() -> PathBuf {
    let base = env::var_os("XDG_STATE_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env::var_os("HOME").unwrap_or_default()).join(".local/state")
        });
    base.join("obend/amendment-nullifiers")
}

struct DurableReplaySnapshot {
    file: fs::File,
    nonces: Vec<u64>,
    nullifiers: Vec<[u8; 32]>,
    cursor: Option<(u64, [u8; 32])>,
}

// Exclusive OS file lock spans read, verify, append, and fsync. A partial record is
// corruption, never an empty replay set. Failed receipts never consume a nonce.
fn open_replay_log(
    path: &std::path::Path,
    root: &[u8; 32],
    policy: &[u8; 32],
    target_organ: &str,
) -> std::io::Result<DurableReplaySnapshot> {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    let mut file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)?;
    file.lock()?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    if bytes.is_empty() {
        file.write_all(REPLAY_LOG_MAGIC)?;
        file.sync_all()?;
        bytes.extend_from_slice(REPLAY_LOG_MAGIC);
    }
    if !bytes.starts_with(REPLAY_LOG_MAGIC)
        || !(bytes.len() - REPLAY_LOG_MAGIC.len()).is_multiple_of(REPLAY_RECORD_LEN)
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "invalid or partial nullifier log",
        ));
    }
    let target = obend_crypto_exec::amend_cli::target_organ_digest(target_organ);
    let records = &bytes[REPLAY_LOG_MAGIC.len()..];
    let mut nonces = Vec::new();
    let mut nullifiers = Vec::new();
    let mut cursor: Option<(u64, [u8; 32])> = None;

    for r in records.as_chunks::<REPLAY_RECORD_LEN>().0 {
        if &r[..32] == root {
            nullifiers.push(r[72..104].try_into().unwrap());
            if &r[32..64] == policy && r[144..176] == target {
                nonces.push(u64::from_be_bytes(r[64..72].try_into().unwrap()));
                let next_epoch = u64::from_be_bytes(r[104..112].try_into().unwrap());
                let next_prior: [u8; 32] = r[112..144].try_into().unwrap();
                cursor = Some((next_epoch, next_prior));
            }
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(DurableReplaySnapshot {
        file,
        nonces,
        nullifiers,
        cursor,
    })
}

#[allow(clippy::too_many_arguments)]
fn append_replay_log(
    file: &mut fs::File,
    root: &[u8; 32],
    policy: &[u8; 32],
    target_organ: &str,
    nonce: u64,
    nullifier: &[u8; 32],
    next_epoch: u64,
    next_prior_digest: &[u8; 32],
) -> std::io::Result<()> {
    let mut record = Vec::with_capacity(REPLAY_RECORD_LEN);
    record.extend_from_slice(root);
    record.extend_from_slice(policy);
    record.extend_from_slice(&nonce.to_be_bytes());
    record.extend_from_slice(nullifier);
    record.extend_from_slice(&next_epoch.to_be_bytes());
    record.extend_from_slice(next_prior_digest);
    record.extend_from_slice(&obend_crypto_exec::amend_cli::target_organ_digest(
        target_organ,
    ));
    file.write_all(&record)?;
    file.sync_all()
}

#[inline]
fn bench_gate_exit_code(sub_5ms_gate: bool) -> ExitCode {
    if sub_5ms_gate {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

fn cmd_prove(args: &[String]) -> ExitCode {
    let mut root_secret_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut policy_arg = String::from(DEFAULT_POLICY_LABEL);
    let mut amendment_arg = String::from(DEFAULT_AMENDMENT_LABEL);
    let mut target_organ_override: Option<String> = None;
    let mut nonce: u64 = 1;
    let mut epoch: u64 = 42;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--root-secret" if i + 1 < args.len() => {
                root_secret_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--out" if i + 1 < args.len() => {
                out_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--policy" if i + 1 < args.len() => {
                policy_arg = args[i + 1].clone();
                i += 2;
            }
            "--amendment" if i + 1 < args.len() => {
                amendment_arg = args[i + 1].clone();
                i += 2;
            }
            "--target-organ" if i + 1 < args.len() => {
                target_organ_override = Some(args[i + 1].clone());
                i += 2;
            }
            "--nonce" if i + 1 < args.len() => {
                match args[i + 1].parse::<u64>() {
                    Ok(v) => nonce = v,
                    Err(_) => {
                        eprintln!("invalid --nonce integer: {}", args[i + 1]);
                        return ExitCode::from(2);
                    }
                }
                i += 2;
            }
            "--epoch" if i + 1 < args.len() => {
                match args[i + 1].parse::<u64>() {
                    Ok(v) => epoch = v,
                    Err(_) => {
                        eprintln!("invalid --epoch integer: {}", args[i + 1]);
                        return ExitCode::from(2);
                    }
                }
                i += 2;
            }
            other => {
                eprintln!("unknown or incomplete flag for `prove`: {other}");
                return ExitCode::from(2);
            }
        }
    }

    let root_secret = match read_root_secret(root_secret_path.as_deref()) {
        Ok(key) => key,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let policy_spec = match load_policy_spec(&policy_arg, target_organ_override.as_deref()) {
        Ok(spec) => spec,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let execution = match load_amendment_execution(&amendment_arg, &policy_spec) {
        Ok(exec) => exec,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    if execution.bedrock_digest() != policy_spec.policy_digest() {
        eprintln!("amendment execution bedrock does not match serialized policy bedrock");
        return ExitCode::from(2);
    }

    let profile = FastReceiptProfile::sub5ms_default();
    let chain = mint_default_chain(root_secret, nonce, epoch);
    let proposal = AmendmentProposal {
        policy_digest: policy_spec.policy_digest(),
        amendment_digest: execution.turn_digest(),
        prior_digest: execution.prior_digest(),
        epoch,
        nonce,
        required_rights: policy_spec.required_rights,
        target_organ: policy_spec.target_organ.clone(),
    };
    let revocations = RevocationSet::new();

    let t_prove = Instant::now();
    let env = match prove_amendment_envelope(
        &profile.canopy_params,
        &profile.lattice_params,
        profile.num_vars,
        &execution,
        proposal,
        chain,
        &revocations,
    ) {
        Ok(e) => e,
        Err(refusal) => {
            println!(
                "{{\"command\":\"prove\",\"status\":\"REFUSED\",\"refusal_code\":\"{}\",\"detail\":\"{}\"}}",
                refusal.code().as_str(),
                json_escape(&format!("{refusal:?}"))
            );
            return ExitCode::from(1);
        }
    };
    let prove_us = t_prove.elapsed().as_micros();

    let t_enc = Instant::now();
    let wire_bytes = env.to_det_cbor_bytes().expect("DetCbor encode succeeds");
    let cbor_encode_us = t_enc.elapsed().as_micros();

    if let Some(ref path) = out_path
        && let Err(e) = fs::write(path, &wire_bytes)
    {
        eprintln!("failed to write receipt to {path}: {e}");
        return ExitCode::from(1);
    }

    let prop_commit = env.proposal.commitment_digest();
    let leaf_null = env
        .biscuit_chain
        .hops
        .last()
        .map(|h| h.hop_nullifier)
        .unwrap_or([0u8; 32]);

    println!(
        "{{\n  \"command\": \"prove\",\n  \"status\": \"OK\",\n  \"num_vars\": {},\n  \"prove_us\": {},\n  \"cbor_encode_us\": {},\n  \"receipt_bytes\": {},\n  \"hop_count\": {},\n  \"nonce\": {},\n  \"epoch\": {},\n  \"target_organ\": \"{}\",\n  \"proposal_commitment_hex\": \"{}\",\n  \"leaf_nullifier_hex\": \"{}\",\n  \"canopy_root_hex\": \"{}\",\n  \"transcript_digest_hex\": \"{}\",\n  \"out_path\": {}\n}}",
        profile.num_vars,
        prove_us,
        cbor_encode_us,
        wire_bytes.len(),
        env.biscuit_chain.hops.len(),
        env.proposal.nonce,
        env.proposal.epoch,
        json_escape(&env.proposal.target_organ),
        hex32(&prop_commit),
        hex32(&leaf_null),
        hex32(&env.dual_receipt.canopy_commitment.root),
        hex32(&env.dual_receipt.final_transcript_digest),
        match out_path {
            Some(ref p) => format!("\"{}\"", json_escape(p)),
            None => String::from("null"),
        }
    );
    ExitCode::SUCCESS
}

fn cmd_verify(args: &[String]) -> ExitCode {
    let mut root_secret_path: Option<String> = None;
    let mut nullifier_log = default_nullifier_log();
    let mut required_rights_override: Option<u64> = None;
    let mut current_epoch: Option<u64> = None;
    let mut in_path: Option<String> = None;
    let mut policy_arg = String::from(DEFAULT_POLICY_LABEL);
    let mut target_organ_override: Option<String> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--root-secret" if i + 1 < args.len() => {
                root_secret_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--nullifier-log" if i + 1 < args.len() => {
                nullifier_log = PathBuf::from(&args[i + 1]);
                i += 2;
            }
            "--required-rights" | "--current-epoch" if i + 1 < args.len() => {
                let value = match args[i + 1].parse::<u64>() {
                    Ok(v) => v,
                    Err(_) => {
                        eprintln!("invalid integer policy flag");
                        return ExitCode::from(2);
                    }
                };
                if args[i] == "--required-rights" {
                    required_rights_override = Some(value);
                } else {
                    current_epoch = Some(value);
                }
                i += 2;
            }
            "--in" if i + 1 < args.len() => {
                in_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--policy" if i + 1 < args.len() => {
                policy_arg = args[i + 1].clone();
                i += 2;
            }
            "--target-organ" if i + 1 < args.len() => {
                target_organ_override = Some(args[i + 1].clone());
                i += 2;
            }
            other => {
                eprintln!("unknown or incomplete flag for `verify`: {other}");
                return ExitCode::from(2);
            }
        }
    }

    let Some(ref receipt_path) = in_path else {
        eprintln!("--in <receipt.cbor> is required for `verify`");
        return ExitCode::from(2);
    };
    let root_secret = match read_root_secret(root_secret_path.as_deref()) {
        Ok(key) => key,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let Some(cli_epoch) = current_epoch else {
        eprintln!("--current-epoch is required from the verifier");
        return ExitCode::from(2);
    };
    let policy_spec = match load_policy_spec(&policy_arg, target_organ_override.as_deref()) {
        Ok(spec) => spec,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let wire_bytes = match fs::read(receipt_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("failed to read {receipt_path}: {e}");
            return ExitCode::from(1);
        }
    };

    let profile = FastReceiptProfile::sub5ms_default();
    let policy_digest = policy_spec.policy_digest();
    let required_rights = required_rights_override.unwrap_or(policy_spec.required_rights);
    let mut verifier = AmendmentVerifierState::new(
        root_secret,
        policy_digest,
        required_rights,
        cli_epoch,
        policy_spec.prior_digest(),
        policy_spec.target_organ.clone(),
    );

    let mut snap = match open_replay_log(
        &nullifier_log,
        &verifier.expected_root_authority,
        &policy_digest,
        &verifier.expected_target_organ,
    ) {
        Ok(log) => log,
        Err(e) => {
            eprintln!("cannot load nullifier log: {e}");
            return ExitCode::from(1);
        }
    };
    verifier.restore_accepted_nonces(&snap.nonces);
    verifier.restore_spent_nullifiers(&snap.nullifiers);
    if let Some((log_epoch, log_prior)) = snap.cursor {
        if cli_epoch != log_epoch {
            eprintln!(
                "--current-epoch {cli_epoch} mismatches durable verifier cursor epoch {log_epoch}"
            );
            return ExitCode::from(1);
        }
        verifier.restore_state_cursor(log_epoch, log_prior);
    }

    let t_dec = Instant::now();
    let decoded = match SignedAmendmentEnvelope::from_det_cbor_bytes(&wire_bytes) {
        Ok(e) => e,
        Err(refusal) => {
            let decode_us = t_dec.elapsed().as_micros();
            println!(
                "{{\n  \"command\": \"verify\",\n  \"status\": \"REFUSED\",\n  \"refusal_code\": \"{}\",\n  \"cbor_decode_us\": {},\n  \"detail\": \"{}\"\n}}",
                refusal.code().as_str(),
                decode_us,
                json_escape(&format!("{refusal:?}"))
            );
            return ExitCode::from(1);
        }
    };
    let cbor_decode_us = t_dec.elapsed().as_micros();

    let t_ver = Instant::now();
    match verifier.verify_and_record_envelope(
        &profile.canopy_params,
        &profile.lattice_params,
        &decoded,
    ) {
        Ok(report) => {
            if let Err(e) = append_replay_log(
                &mut snap.file,
                &verifier.expected_root_authority,
                &policy_digest,
                &verifier.expected_target_organ,
                report.nonce,
                &report.leaf_nullifier,
                verifier.current_epoch,
                &verifier.expected_prior_digest,
            ) {
                eprintln!("cannot persist accepted nonce: {e}");
                return ExitCode::from(1);
            }
            let verify_us = t_ver.elapsed().as_micros();
            println!(
                "{{\n  \"command\": \"verify\",\n  \"status\": \"ACCEPTED\",\n  \"cbor_decode_us\": {},\n  \"verify_us\": {},\n  \"receipt_bytes\": {},\n  \"hop_count\": {},\n  \"effective_rights\": {},\n  \"nonce\": {},\n  \"epoch\": {},\n  \"next_epoch\": {},\n  \"target_organ\": \"{}\",\n  \"canopy_hashes\": {},\n  \"proposal_commitment_hex\": \"{}\",\n  \"leaf_nullifier_hex\": \"{}\",\n  \"next_prior_digest_hex\": \"{}\",\n  \"canopy_root_hex\": \"{}\",\n  \"transcript_digest_hex\": \"{}\"\n}}",
                cbor_decode_us,
                verify_us,
                wire_bytes.len(),
                report.hop_count,
                report.effective_rights,
                report.nonce,
                report.epoch,
                verifier.current_epoch,
                json_escape(&verifier.expected_target_organ),
                report.hash_stats.total_hashes,
                hex32(&report.proposal_commitment),
                hex32(&report.leaf_nullifier),
                hex32(&verifier.expected_prior_digest),
                hex32(&report.canopy_root),
                hex32(&report.final_transcript_digest),
            );
            ExitCode::SUCCESS
        }
        Err(refusal) => {
            let verify_us = t_ver.elapsed().as_micros();
            println!(
                "{{\n  \"command\": \"verify\",\n  \"status\": \"REFUSED\",\n  \"refusal_code\": \"{}\",\n  \"cbor_decode_us\": {},\n  \"verify_us\": {},\n  \"detail\": \"{}\"\n}}",
                refusal.code().as_str(),
                cbor_decode_us,
                verify_us,
                json_escape(&format!("{refusal:?}"))
            );
            ExitCode::from(1)
        }
    }
}

fn cmd_tamper_test() -> ExitCode {
    let profile = FastReceiptProfile::sub5ms_default();
    let (root_auth, policy_digest, exec, proposal, chain) = build_demo_inputs(
        cshake256_32(b"OBEND.CLI.BENCH_KEY/v1", DEFAULT_ROOT_LABEL),
        99,
        42,
    );
    let env = prove_amendment_envelope(
        &profile.canopy_params,
        &profile.lattice_params,
        profile.num_vars,
        &exec,
        proposal,
        chain,
        &RevocationSet::new(),
    )
    .expect("baseline envelope proves cleanly");
    let wire = env.to_det_cbor_bytes().expect("DetCbor encode");

    let make_verifier = || {
        AmendmentVerifierState::new(
            root_auth,
            policy_digest,
            5,
            42,
            exec.prior_digest(),
            DEFAULT_TARGET_ORGAN,
        )
    };
    let mut results: Vec<(&'static str, RefusalCode, u128, bool)> = Vec::new();

    // 1. Non-canonical CBOR map keys ({ "z": 1, "a": 2 })
    {
        let mut st = make_verifier();
        let bad_cbor = [0xa2, 0x61, b'z', 0x01, 0x61, b'a', 0x02];
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &bad_cbor)
            .expect_err("must refuse unsorted CBOR map keys");
        let us = t.elapsed().as_micros();
        results.push((
            "non_canonical_cbor_unsorted_keys",
            err.code(),
            us,
            err.code() == RefusalCode::NonCanonicalCbor,
        ));
    }

    // 2. Replayed nonce
    {
        let mut st = make_verifier();
        st.verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .expect("first nonce accepted");
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .expect_err("must refuse replayed nonce");
        let us = t.elapsed().as_micros();
        results.push((
            "replayed_nonce",
            err.code(),
            us,
            err.code() == RefusalCode::ReplayedNonce,
        ));
    }

    // 3. Forged attenuation hop (rights escalation)
    {
        let mut st = make_verifier();
        let mut forged = env.clone();
        forged.biscuit_chain.hops[2].rights_mask = 0xFF;
        let forged_wire = forged.to_det_cbor_bytes().unwrap();
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(
                &profile.canopy_params,
                &profile.lattice_params,
                &forged_wire,
            )
            .expect_err("must refuse forged attenuation hop");
        let us = t.elapsed().as_micros();
        results.push((
            "forged_attenuation_hop",
            err.code(),
            us,
            err.code() == RefusalCode::ForgedAttenuationHop,
        ));
    }

    // 4. Revoked ancestor hop nullifier (`revoke_ancestor_kills_cone`)
    {
        let mut st = make_verifier();
        st.revocations
            .revoke_nullifier(env.biscuit_chain.hops[1].hop_nullifier);
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &wire)
            .expect_err("must refuse revoked ancestor lineage");
        let us = t.elapsed().as_micros();
        results.push((
            "revoked_ancestor_lineage",
            err.code(),
            us,
            err.code() == RefusalCode::RevokedLineage,
        ));
    }

    // 5. Swapped amendment digest (breaks circuit_desc binding)
    {
        let mut st = make_verifier();
        let mut swapped = env.clone();
        swapped.proposal.amendment_digest[0] ^= 0x80;
        let swapped_wire = swapped.to_det_cbor_bytes().unwrap();
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(
                &profile.canopy_params,
                &profile.lattice_params,
                &swapped_wire,
            )
            .expect_err("must refuse unbound amendment digest swap");
        let us = t.elapsed().as_micros();
        results.push((
            "amendment_digest_swap",
            err.code(),
            us,
            err.code() == RefusalCode::AmendmentBindingMismatch,
        ));
    }

    // 6. Tampered Canopy Track H column evaluation
    {
        let mut st = make_verifier();
        let mut bad_canopy = env.clone();
        bad_canopy.dual_receipt.canopy_proof.opened_columns[0].values[0] += Goldilocks::ONE;
        let bad_wire = bad_canopy.to_det_cbor_bytes().unwrap();
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &bad_wire)
            .expect_err("must refuse tampered Canopy opening");
        let us = t.elapsed().as_micros();
        results.push((
            "tampered_canopy_opening",
            err.code(),
            us,
            err.code() == RefusalCode::TamperedCanopyOpening,
        ));
    }

    // 7. Tampered PikkuFold/Akita Track L witness
    {
        let mut st = make_verifier();
        let mut bad_lat = env.clone();
        let mut coeffs = *bad_lat.dual_receipt.lattice_proof.final_witness.coeffs();
        coeffs[0] += 1;
        bad_lat.dual_receipt.lattice_proof.final_witness = RingElem::from_coeffs(coeffs);
        let bad_wire = bad_lat.to_det_cbor_bytes().unwrap();
        let t = Instant::now();
        let err = st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &bad_wire)
            .expect_err("must refuse tampered PikkuFold opening");
        let us = t.elapsed().as_micros();
        results.push((
            "tampered_pikkufold_opening",
            err.code(),
            us,
            err.code() == RefusalCode::TamperedPikkufoldOpening,
        ));
    }

    let all_passed = results.iter().all(|(_, _, _, ok)| *ok);
    println!("{{");
    println!("  \"command\": \"tamper-test\",");
    println!("  \"all_refusals_exact\": {},", all_passed);
    println!("  \"cases\": [");
    for (idx, (name, code, us, ok)) in results.iter().enumerate() {
        let comma = if idx + 1 == results.len() { "" } else { "," };
        println!(
            "    {{\"case\": \"{}\", \"refusal_code\": \"{}\", \"latency_us\": {}, \"exact_match\": {}}}{}",
            name,
            code.as_str(),
            us,
            ok,
            comma
        );
    }
    println!("  ]");
    println!("}}");

    if all_passed {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

struct ProfileBenchStats {
    label: &'static str,
    num_vars: usize,
    iters: usize,
    avg_prove_us: u128,
    min_prove_us: u128,
    avg_cbor_encode_us: u128,
    avg_cbor_decode_us: u128,
    avg_verify_us: u128,
    min_verify_us: u128,
    wire_bytes: usize,
    canopy_hashes: usize,
}

// Retention is derived from satisfaction in this execution format. Alternate
// incompatible clauses so each real amendment evicts its predecessor in place.
fn benchmark_execution() -> AmendmentExecution {
    let mut exec = example_amendment_execution();
    exec.old = exec.proposed.clone();
    exec.old[0].allowed = 1 << 6;
    exec.proposed[0].allowed = 1 << 7;
    exec
}

fn advance_benchmark_execution(exec: &mut AmendmentExecution) {
    exec.old = exec.revised_clauses();
    exec.selected ^= 1;
    exec.proposed[0].allowed = 1 << exec.selected;
}

fn bench_profile(
    label: &'static str,
    profile: &FastReceiptProfile,
    iters: usize,
) -> ProfileBenchStats {
    let root_auth = cshake256_32(b"OBEND.CLI.BENCH_KEY/v1", DEFAULT_ROOT_LABEL);
    let init_exec = benchmark_execution();
    let policy_digest = init_exec.bedrock_digest();
    let revocations = RevocationSet::new();

    // Warm-up pass
    {
        let (_, _, warm_exec, warm_prop, warm_chain) = build_demo_inputs(root_auth, 1, 42);
        let warm_env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &warm_exec,
            warm_prop,
            warm_chain,
            &revocations,
        )
        .expect("warmup prove");
        let warm_wire = warm_env.to_det_cbor_bytes().expect("warmup encode");
        let mut warm_st = AmendmentVerifierState::new(
            root_auth,
            policy_digest,
            5,
            42,
            warm_exec.prior_digest(),
            DEFAULT_TARGET_ORGAN,
        );
        warm_st
            .verify_and_record_bytes(&profile.canopy_params, &profile.lattice_params, &warm_wire)
            .expect("warmup verify");
    }

    let mut sum_prove_us: u128 = 0;
    let mut min_prove_us: u128 = u128::MAX;
    let mut sum_enc_us: u128 = 0;
    let mut sum_dec_us: u128 = 0;
    let mut sum_ver_us: u128 = 0;
    let mut min_ver_us: u128 = u128::MAX;
    let mut wire_bytes: usize = 0;
    let mut canopy_hashes: usize = 0;

    let mut cur_exec = init_exec.clone();
    let start_epoch: u64 = 42;
    let mut verifier = AmendmentVerifierState::new(
        root_auth,
        policy_digest,
        5,
        start_epoch,
        cur_exec.prior_digest(),
        DEFAULT_TARGET_ORGAN,
    );

    for (cur_epoch_iter, iter) in (start_epoch..).zip(0..iters) {
        let nonce = (iter as u64) + 1;
        let iter_chain = mint_default_chain(root_auth, nonce, cur_epoch_iter);
        let prop = AmendmentProposal {
            policy_digest,
            amendment_digest: cur_exec.turn_digest(),
            prior_digest: cur_exec.prior_digest(),
            epoch: cur_epoch_iter,
            nonce,
            required_rights: 0b0000_0101,
            target_organ: String::from(DEFAULT_TARGET_ORGAN),
        };

        let t_p = Instant::now();
        let env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &cur_exec,
            prop,
            iter_chain,
            &revocations,
        )
        .expect("bench prove");
        let p_us = t_p.elapsed().as_micros();
        sum_prove_us += p_us;
        if p_us < min_prove_us {
            min_prove_us = p_us;
        }

        let t_e = Instant::now();
        let wire = env.to_det_cbor_bytes().expect("bench encode");
        sum_enc_us += t_e.elapsed().as_micros();
        wire_bytes = wire.len();

        let t_d = Instant::now();
        let decoded = SignedAmendmentEnvelope::from_det_cbor_bytes(&wire).expect("bench decode");
        sum_dec_us += t_d.elapsed().as_micros();

        let t_v = Instant::now();
        let rep = verifier
            .verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &decoded)
            .expect("bench verify");
        let v_us = t_v.elapsed().as_micros();
        sum_ver_us += v_us;
        if v_us < min_ver_us {
            min_ver_us = v_us;
        }
        canopy_hashes = rep.hash_stats.total_hashes;

        advance_benchmark_execution(&mut cur_exec);
    }

    let n = iters as u128;
    ProfileBenchStats {
        label,
        num_vars: profile.num_vars,
        iters,
        avg_prove_us: sum_prove_us / n,
        min_prove_us,
        avg_cbor_encode_us: sum_enc_us / n,
        avg_cbor_decode_us: sum_dec_us / n,
        avg_verify_us: sum_ver_us / n,
        min_verify_us: min_ver_us,
        wire_bytes,
        canopy_hashes,
    }
}

fn cmd_bench(args: &[String]) -> ExitCode {
    let mut iters: usize = 20;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--iters" if i + 1 < args.len() => {
                match args[i + 1].parse::<usize>() {
                    Ok(v) if v > 0 => iters = v,
                    _ => {
                        eprintln!("invalid --iters value: {}", args[i + 1]);
                        return ExitCode::from(2);
                    }
                }
                i += 2;
            }
            other => {
                eprintln!("unknown or incomplete flag for `bench`: {other}");
                return ExitCode::from(2);
            }
        }
    }

    let p_fast = FastReceiptProfile::sub5ms_default();
    let p_v10 = FastReceiptProfile::query_128bit_v10();

    let s_fast = bench_profile("sub5ms_default_v8", &p_fast, iters);
    let s_v10 = bench_profile("query_128bit_v10", &p_v10, iters);
    let sub_5ms_gate = s_fast.avg_prove_us < 5_000 && s_fast.avg_verify_us < 5_000;

    println!("{{");
    println!("  \"command\": \"bench\",");
    println!("  \"sub_5ms_gate_passed\": {},", sub_5ms_gate);
    println!("  \"profiles\": [");
    for (idx, s) in [&s_fast, &s_v10].iter().enumerate() {
        let comma = if idx == 0 { "," } else { "" };
        println!(
            "    {{\n      \"profile\": \"{}\",\n      \"num_vars\": {},\n      \"iters\": {},\n      \"avg_prove_us\": {},\n      \"min_prove_us\": {},\n      \"avg_cbor_encode_us\": {},\n      \"avg_cbor_decode_us\": {},\n      \"avg_verify_us\": {},\n      \"min_verify_us\": {},\n      \"wire_bytes\": {},\n      \"canopy_hashes\": {}\n    }}{}",
            s.label,
            s.num_vars,
            s.iters,
            s.avg_prove_us,
            s.min_prove_us,
            s.avg_cbor_encode_us,
            s.avg_cbor_decode_us,
            s.avg_verify_us,
            s.min_verify_us,
            s.wire_bytes,
            s.canopy_hashes,
            comma
        );
    }
    println!("  ]");
    println!("}}");

    bench_gate_exit_code(sub_5ms_gate)
}

fn print_usage() {
    eprintln!(
        "Usage: obend-zk-receipt <prove|verify|tamper-test|bench> [options]\n\
         Commands:\n  \
           prove --root-secret <32-byte file> [--policy <policy.cbor>] [--amendment <exec.cbor>] [--target-organ <name>] [--out <path>] [--nonce <u64>] [--epoch <u64>]\n  \
           verify --root-secret <32-byte file> --current-epoch <u64> --in <path> [--policy <policy.cbor>] [--target-organ <name>] [--required-rights <u64>] [--nullifier-log <path>]\n  \
           tamper-test\n  \
           bench [--iters <usize>]"
    );
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    let Some(cmd) = args.first().map(String::as_str) else {
        print_usage();
        return ExitCode::from(2);
    };
    let rest = &args[1..];
    match cmd {
        "prove" => cmd_prove(rest),
        "verify" => cmd_verify(rest),
        "tamper-test" => cmd_tamper_test(),
        "bench" => cmd_bench(rest),
        "--help" | "-h" | "help" => {
            print_usage();
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("unknown subcommand: {other}");
            print_usage();
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod replay_tests {
    use super::*;
    use obend_crypto_exec::amend_cli::LawClause;

    #[test]
    fn organs_advance_independent_durable_cursors() {
        let path = env::temp_dir().join(format!(
            "organ-cursors-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let root = [1; 32];
        let policy = [2; 32];
        {
            let mut a = open_replay_log(&path, &root, &policy, "a").unwrap();
            append_replay_log(&mut a.file, &root, &policy, "a", 1, &[3; 32], 7, &[4; 32]).unwrap();
        }
        {
            let mut b = open_replay_log(&path, &root, &policy, "b").unwrap();
            assert_eq!(b.cursor, None);
            assert!(b.nonces.is_empty());
            append_replay_log(&mut b.file, &root, &policy, "b", 1, &[5; 32], 11, &[6; 32]).unwrap();
        }
        assert_eq!(
            open_replay_log(&path, &root, &policy, "a").unwrap().cursor,
            Some((7, [4; 32]))
        );
        assert_eq!(
            open_replay_log(&path, &root, &policy, "b").unwrap().cursor,
            Some((11, [6; 32]))
        );
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn benchmark_turns_keep_constant_clause_count_and_exact_cursor() {
        let mut exec = benchmark_execution();
        let size = exec.revised_clauses().len();
        for _ in 0..1000 {
            let expected_prior = exec.next_prior_digest();
            advance_benchmark_execution(&mut exec);
            assert_eq!(exec.prior_digest(), expected_prior);
            assert_eq!(exec.revised_clauses().len(), size);
            assert_eq!(exec.proposed.len(), 1);
            assert!(exec.retained_clauses().is_empty());
        }
        let stats = bench_profile("regression", &FastReceiptProfile::sub5ms_default(), 3);
        assert_eq!(stats.iters, 3);
    }

    #[test]
    fn hvm_argument_validation_and_final_mismatch_status() {
        let script = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../hardware/hvm/verify_hvm.sh"
        );
        let status = std::process::Command::new("bash")
            .args([script, "--stage", "99"])
            .env("OBEND_EMIT_HVM", "/nonexistent")
            .env("HVM_BIN", "/nonexistent")
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(2));
        let source = fs::read_to_string(script).unwrap();
        let compare = source
            .split("compare() {")
            .nth(1)
            .unwrap()
            .split("\n}")
            .next()
            .unwrap();
        let dir = env::temp_dir().join(format!("hvm-compare-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        fs::write(
            dir.join("expected.tsv"),
            "a.hvm\tmember\targs\texpected\tmodel\n",
        )
        .unwrap();
        let code = format!(
            "set -eu; TIMEOUT=env; HVM=false; compare() {{{compare}\n}}; compare 1 \"$1\" run; test \"$MISMATCHES\" = 1"
        );
        let status = std::process::Command::new("bash")
            .args(["-c", &code, "test"])
            .arg(&dir)
            .status()
            .unwrap();
        fs::remove_dir_all(dir).unwrap();
        assert!(status.success());
    }

    #[test]
    fn durable_log_rejects_replay_after_reopening() {
        let path = env::temp_dir().join(format!(
            "obend-replay-{}-{}.log",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let (secret, policy, exec, prop, chain) = build_demo_inputs([17; 32], 7, 42);
        let profile = FastReceiptProfile::sub5ms_default();
        let env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            8,
            &exec,
            prop,
            chain,
            &RevocationSet::new(),
        )
        .unwrap();
        {
            let mut verifier = AmendmentVerifierState::new(
                secret,
                policy,
                5,
                42,
                exec.prior_digest(),
                DEFAULT_TARGET_ORGAN,
            );
            let mut snap = open_replay_log(
                &path,
                &verifier.expected_root_authority,
                &policy,
                &verifier.expected_target_organ,
            )
            .unwrap();
            verifier.restore_accepted_nonces(&snap.nonces);
            verifier.restore_spent_nullifiers(&snap.nullifiers);
            let report = verifier
                .verify_and_record_envelope(&profile.canopy_params, &profile.lattice_params, &env)
                .unwrap();
            append_replay_log(
                &mut snap.file,
                &verifier.expected_root_authority,
                &policy,
                &verifier.expected_target_organ,
                7,
                &report.leaf_nullifier,
                verifier.current_epoch,
                &verifier.expected_prior_digest,
            )
            .unwrap();
        }
        {
            let mut verifier = AmendmentVerifierState::new(
                secret,
                policy,
                5,
                42,
                exec.prior_digest(),
                DEFAULT_TARGET_ORGAN,
            );
            let snap = open_replay_log(
                &path,
                &verifier.expected_root_authority,
                &policy,
                &verifier.expected_target_organ,
            )
            .unwrap();
            verifier.restore_accepted_nonces(&snap.nonces);
            verifier.restore_spent_nullifiers(&snap.nullifiers);
            if let Some((ep, pr)) = snap.cursor {
                verifier.restore_state_cursor(ep, pr);
            }
            assert_eq!(
                verifier
                    .verify_and_record_envelope(
                        &profile.canopy_params,
                        &profile.lattice_params,
                        &env
                    )
                    .unwrap_err()
                    .code(),
                RefusalCode::ReplayedNonce
            );
            let mut next_proposal = env.proposal.clone();
            next_proposal.nonce = 8;
            let next = prove_amendment_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                8,
                &env.execution,
                next_proposal,
                env.biscuit_chain.clone(),
                &RevocationSet::new(),
            )
            .unwrap();
            assert_eq!(
                verifier
                    .verify_and_record_envelope(
                        &profile.canopy_params,
                        &profile.lattice_params,
                        &next
                    )
                    .unwrap_err()
                    .code(),
                RefusalCode::RevokedLineage
            );
        }
        let _ = fs::remove_file(path);
    }

    #[test]
    fn cli_verify_requires_in_flag_supports_serialized_policy_and_gates_bench() {
        let dir = env::temp_dir().join(format!(
            "obend-cli-p204-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&dir).unwrap();
        let key_path = dir.join("root.key");
        let policy_path = dir.join("custom_policy.cbor");
        let exec1_path = dir.join("exec1.cbor");
        let exec2_path = dir.join("exec2.cbor");
        let rcpt1_path = dir.join("rcpt1.cbor");
        let rcpt2_path = dir.join("rcpt2.cbor");
        let log_path = dir.join("nullifiers.log");

        fs::write(&key_path, [0x42u8; 32]).unwrap();

        // 1. `verify` WITHOUT `--in` MUST fail with ExitCode(2) and NEVER self-manufacture a receipt!
        let missing_in_rc = cmd_verify(&[
            String::from("--root-secret"),
            key_path.to_string_lossy().into_owned(),
            String::from("--current-epoch"),
            String::from("10"),
            String::from("--nullifier-log"),
            log_path.to_string_lossy().into_owned(),
        ]);
        assert_eq!(missing_in_rc, ExitCode::from(2));
        assert!(!log_path.exists(), "missing --in must not touch replay log");

        // 2. Real serialized CBOR policy + multi-turn serialized executions prove & verify cleanly!
        let custom_policy = SerializedPolicySpec {
            bedrock: 0x00c0,
            bedrock_seed: 6,
            prior_clauses: vec![LawClause {
                name: String::from("baseline-safety"),
                priority: 5,
                allowed: 0x00c0,
            }],
            required_rights: 0b0000_0011,
            target_organ: String::from("Obend.Hardware.SafePhysicalShield"),
        };
        fs::write(&policy_path, custom_policy.to_det_cbor_bytes().unwrap()).unwrap();

        let exec1 = AmendmentExecution {
            slot: 1,
            old: custom_policy.prior_clauses.clone(),
            proposed: vec![LawClause {
                name: String::from("clamp-fence"),
                priority: 2,
                allowed: 0x0080,
            }],
            bedrock: custom_policy.bedrock,
            bedrock_seed: custom_policy.bedrock_seed,
            selected: 7,
        };
        fs::write(&exec1_path, exec1.to_det_cbor_bytes().unwrap()).unwrap();

        assert_eq!(
            cmd_prove(&[
                String::from("--root-secret"),
                key_path.to_string_lossy().into_owned(),
                String::from("--policy"),
                policy_path.to_string_lossy().into_owned(),
                String::from("--amendment"),
                exec1_path.to_string_lossy().into_owned(),
                String::from("--nonce"),
                String::from("101"),
                String::from("--epoch"),
                String::from("10"),
                String::from("--out"),
                rcpt1_path.to_string_lossy().into_owned(),
            ]),
            ExitCode::SUCCESS
        );

        // Wrong `--target-organ` MUST fail verification!
        assert_eq!(
            cmd_verify(&[
                String::from("--root-secret"),
                key_path.to_string_lossy().into_owned(),
                String::from("--policy"),
                policy_path.to_string_lossy().into_owned(),
                String::from("--target-organ"),
                String::from("Obend.Wrong.Organ"),
                String::from("--current-epoch"),
                String::from("10"),
                String::from("--in"),
                rcpt1_path.to_string_lossy().into_owned(),
                String::from("--nullifier-log"),
                log_path.to_string_lossy().into_owned(),
            ]),
            ExitCode::from(1)
        );

        // Matching policy & target organ accepts Turn 1 and advances durable cursor to epoch 11!
        assert_eq!(
            cmd_verify(&[
                String::from("--root-secret"),
                key_path.to_string_lossy().into_owned(),
                String::from("--policy"),
                policy_path.to_string_lossy().into_owned(),
                String::from("--current-epoch"),
                String::from("10"),
                String::from("--in"),
                rcpt1_path.to_string_lossy().into_owned(),
                String::from("--nullifier-log"),
                log_path.to_string_lossy().into_owned(),
            ]),
            ExitCode::SUCCESS
        );

        // Turn 2 advancing from `exec1.revised_clauses()` at epoch 11 succeeds!
        let exec2 = AmendmentExecution {
            slot: 1,
            old: exec1.revised_clauses(),
            proposed: vec![LawClause {
                name: String::from("telemetry"),
                priority: 1,
                allowed: 0x0080,
            }],
            bedrock: custom_policy.bedrock,
            bedrock_seed: custom_policy.bedrock_seed,
            selected: 7,
        };
        fs::write(&exec2_path, exec2.to_det_cbor_bytes().unwrap()).unwrap();

        assert_eq!(
            cmd_prove(&[
                String::from("--root-secret"),
                key_path.to_string_lossy().into_owned(),
                String::from("--policy"),
                policy_path.to_string_lossy().into_owned(),
                String::from("--amendment"),
                exec2_path.to_string_lossy().into_owned(),
                String::from("--nonce"),
                String::from("102"),
                String::from("--epoch"),
                String::from("11"),
                String::from("--out"),
                rcpt2_path.to_string_lossy().into_owned(),
            ]),
            ExitCode::SUCCESS
        );
        assert_eq!(
            cmd_verify(&[
                String::from("--root-secret"),
                key_path.to_string_lossy().into_owned(),
                String::from("--policy"),
                policy_path.to_string_lossy().into_owned(),
                String::from("--current-epoch"),
                String::from("11"),
                String::from("--in"),
                rcpt2_path.to_string_lossy().into_owned(),
                String::from("--nullifier-log"),
                log_path.to_string_lossy().into_owned(),
            ]),
            ExitCode::SUCCESS
        );

        // 3. `bench_gate_exit_code` returns non-zero when `sub_5ms_gate` fails!
        assert_eq!(bench_gate_exit_code(true), ExitCode::SUCCESS);
        assert_eq!(bench_gate_exit_code(false), ExitCode::from(1));

        let _ = fs::remove_dir_all(&dir);
    }
}
