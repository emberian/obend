//! `obend-zk-receipt`: Fast executable CLI & stranger verification harness for `Obend`'s
//! Dual-Track (`Canopy` Track H + `PikkuFold`/`Akita` Track L) + `ZkBiscuit` + `DetCbor` receipts.
//!
//! Subcommands:
//! - `prove [--out <file>] [--policy <label>] [--amendment <label>] [--nonce <u64>] [--epoch <u64>]`
//! - `verify [--in <file>] [--policy <label>]`
//! - `tamper-test`
//! - `bench [--iters <usize>]`

#![forbid(unsafe_code)]

use std::env;
use std::fs;
use std::process::ExitCode;
use std::time::Instant;

use obend_crypto_exec::amend_cli::{
    AmendmentProposal, AmendmentVerifierState, FastReceiptProfile, RefusalCode, RevocationSet,
    SignedAmendmentEnvelope, ZkBiscuitChain, prove_amendment_envelope,
};
use obend_crypto_exec::goldilocks::Goldilocks;
use obend_crypto_exec::pikkufold::RingElem;
use obend_crypto_exec::transcript::cshake256_32;

const DEFAULT_ROOT_LABEL: &[u8] = b"polis-cathedral-root-authority-v1";
const DEFAULT_POLICY_LABEL: &str = "cathedral-seven-organ-policy-v5";
const DEFAULT_AMENDMENT_LABEL: &str = "promote-trailblaze-stageb-unconditional-seal";
const DEFAULT_WITNESS_SECRET: [u8; 32] = *b"OBEND.CLI.DEMO.WITNESS.SECRET/01";

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

fn build_demo_inputs(
    policy_label: &str,
    amendment_label: &str,
    nonce: u64,
    epoch: u64,
) -> ([u8; 32], [u8; 32], AmendmentProposal, ZkBiscuitChain) {
    let root_authority_id = cshake256_32(b"OBEND.CLI.ROOT_AUTH/v1", DEFAULT_ROOT_LABEL);
    let policy_digest =
        cshake256_32(b"OBEND.CLI.POLICY/v1", policy_label.as_bytes());
    let amendment_digest =
        cshake256_32(b"OBEND.CLI.AMENDMENT/v1", amendment_label.as_bytes());

    let chain = ZkBiscuitChain::mint_root(
        root_authority_id,
        101,
        0b1111_1111,
        1_000,
        "genesis:polis-council",
    )
    .attenuate(202, 0b0011_1111, 500, "delegate:clustergov-quorum")
    .expect("valid hop 1 attenuation")
    .attenuate(303, 0b0000_1111, 250, "leaf:amendment-prover")
    .expect("valid hop 2 attenuation");

    let proposal = AmendmentProposal {
        policy_digest,
        amendment_digest,
        epoch,
        nonce,
        required_rights: 0b0000_0101,
        target_organ: String::from("Obend.Trailblaze.StageBInstances"),
    };

    (root_authority_id, policy_digest, proposal, chain)
}

fn cmd_prove(args: &[String]) -> ExitCode {
    let mut out_path: Option<String> = None;
    let mut policy_label = String::from(DEFAULT_POLICY_LABEL);
    let mut amendment_label = String::from(DEFAULT_AMENDMENT_LABEL);
    let mut nonce: u64 = 1;
    let mut epoch: u64 = 42;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--out" if i + 1 < args.len() => {
                out_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--policy" if i + 1 < args.len() => {
                policy_label = args[i + 1].clone();
                i += 2;
            }
            "--amendment" if i + 1 < args.len() => {
                amendment_label = args[i + 1].clone();
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

    let profile = FastReceiptProfile::sub5ms_default();
    let (_, _, proposal, chain) = build_demo_inputs(&policy_label, &amendment_label, nonce, epoch);
    let revocations = RevocationSet::new();

    let t_prove = Instant::now();
    let env = match prove_amendment_envelope(
        &profile.canopy_params,
        &profile.lattice_params,
        profile.num_vars,
        &DEFAULT_WITNESS_SECRET,
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
        "{{\n  \"command\": \"prove\",\n  \"status\": \"OK\",\n  \"num_vars\": {},\n  \"prove_us\": {},\n  \"cbor_encode_us\": {},\n  \"receipt_bytes\": {},\n  \"hop_count\": {},\n  \"nonce\": {},\n  \"epoch\": {},\n  \"proposal_commitment_hex\": \"{}\",\n  \"leaf_nullifier_hex\": \"{}\",\n  \"canopy_root_hex\": \"{}\",\n  \"transcript_digest_hex\": \"{}\",\n  \"out_path\": {}\n}}",
        profile.num_vars,
        prove_us,
        cbor_encode_us,
        wire_bytes.len(),
        env.biscuit_chain.hops.len(),
        env.proposal.nonce,
        env.proposal.epoch,
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
    let mut in_path: Option<String> = None;
    let mut policy_label = String::from(DEFAULT_POLICY_LABEL);

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--in" if i + 1 < args.len() => {
                in_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--policy" if i + 1 < args.len() => {
                policy_label = args[i + 1].clone();
                i += 2;
            }
            other => {
                eprintln!("unknown or incomplete flag for `verify`: {other}");
                return ExitCode::from(2);
            }
        }
    }

    let profile = FastReceiptProfile::sub5ms_default();
    let (root_authority_id, policy_digest, demo_prop, demo_chain) =
        build_demo_inputs(&policy_label, DEFAULT_AMENDMENT_LABEL, 1, 42);

    let wire_bytes = match in_path {
        Some(ref path) => match fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("failed to read {path}: {e}");
                return ExitCode::from(1);
            }
        },
        None => {
            let env = prove_amendment_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                profile.num_vars,
                &DEFAULT_WITNESS_SECRET,
                demo_prop,
                demo_chain,
                &RevocationSet::new(),
            )
            .expect("self-contained demo prove succeeds");
            env.to_det_cbor_bytes().expect("DetCbor encode succeeds")
        }
    };

    let mut verifier = AmendmentVerifierState::new(root_authority_id, policy_digest);
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
            let verify_us = t_ver.elapsed().as_micros();
            println!(
                "{{\n  \"command\": \"verify\",\n  \"status\": \"ACCEPTED\",\n  \"cbor_decode_us\": {},\n  \"verify_us\": {},\n  \"receipt_bytes\": {},\n  \"hop_count\": {},\n  \"effective_rights\": {},\n  \"nonce\": {},\n  \"epoch\": {},\n  \"canopy_hashes\": {},\n  \"proposal_commitment_hex\": \"{}\",\n  \"leaf_nullifier_hex\": \"{}\",\n  \"canopy_root_hex\": \"{}\",\n  \"transcript_digest_hex\": \"{}\"\n}}",
                cbor_decode_us,
                verify_us,
                wire_bytes.len(),
                report.hop_count,
                report.effective_rights,
                report.nonce,
                report.epoch,
                report.hash_stats.total_hashes,
                hex32(&report.proposal_commitment),
                hex32(&report.leaf_nullifier),
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
    let (root_auth, policy_digest, proposal, chain) =
        build_demo_inputs(DEFAULT_POLICY_LABEL, DEFAULT_AMENDMENT_LABEL, 99, 42);
    let env = prove_amendment_envelope(
        &profile.canopy_params,
        &profile.lattice_params,
        profile.num_vars,
        &DEFAULT_WITNESS_SECRET,
        proposal,
        chain,
        &RevocationSet::new(),
    )
    .expect("baseline envelope proves cleanly");
    let wire = env.to_det_cbor_bytes().expect("DetCbor encode");

    let mut results: Vec<(&'static str, RefusalCode, u128, bool)> = Vec::new();

    // 1. Non-canonical CBOR map keys ({ "z": 1, "a": 2 })
    {
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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
        let mut st = AmendmentVerifierState::new(root_auth, policy_digest);
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

fn bench_profile(
    label: &'static str,
    profile: &FastReceiptProfile,
    iters: usize,
) -> ProfileBenchStats {
    let (root_auth, policy_digest, base_prop, chain) =
        build_demo_inputs(DEFAULT_POLICY_LABEL, DEFAULT_AMENDMENT_LABEL, 1, 42);
    let revocations = RevocationSet::new();

    // Warm-up pass
    {
        let warm_env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &DEFAULT_WITNESS_SECRET,
            base_prop.clone(),
            chain.clone(),
            &revocations,
        )
        .expect("warmup prove");
        let warm_wire = warm_env.to_det_cbor_bytes().expect("warmup encode");
        let mut warm_st = AmendmentVerifierState::new(root_auth, policy_digest);
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

    let mut verifier = AmendmentVerifierState::new(root_auth, policy_digest);

    for iter in 0..iters {
        let mut prop = base_prop.clone();
        prop.nonce = (iter as u64) + 1;

        let t_p = Instant::now();
        let env = prove_amendment_envelope(
            &profile.canopy_params,
            &profile.lattice_params,
            profile.num_vars,
            &DEFAULT_WITNESS_SECRET,
            prop,
            chain.clone(),
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
            .verify_and_record_envelope(
                &profile.canopy_params,
                &profile.lattice_params,
                &decoded,
            )
            .expect("bench verify");
        let v_us = t_v.elapsed().as_micros();
        sum_ver_us += v_us;
        if v_us < min_ver_us {
            min_ver_us = v_us;
        }
        canopy_hashes = rep.hash_stats.total_hashes;
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
    let p_v10 = FastReceiptProfile::full_128bit_v10();

    let s_fast = bench_profile("sub5ms_default_v8", &p_fast, iters);
    let s_v10 = bench_profile("full_128bit_v10", &p_v10, iters);
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

    ExitCode::SUCCESS
}

fn print_usage() {
    eprintln!(
        "Usage: obend-zk-receipt <prove|verify|tamper-test|bench> [options]\n\
         Commands:\n  \
           prove [--out <path>] [--policy <str>] [--amendment <str>] [--nonce <u64>] [--epoch <u64>]\n  \
           verify [--in <path>] [--policy <str>]\n  \
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
