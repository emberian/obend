//! Adversarial Confinement & `G11` Conformance Suite (`CAP-17`, `CAP-23`, `.spk` `verify_strict`,
//! `manifest.rs:287` role confinement, `LineChannel` flood cap, and slot-path AAD secret sealing).

use obend_sandbox::bwrap::{
    BubblewrapRunner, DEFAULT_MAX_PROCESS_OUTPUT_BYTES, SandboxBackend, SandboxConfig, SandboxError,
};
use obend_sandbox::capnp_wire::{
    self, WireBridgeConfig, WirePermissionDef, WireRoleDef, write_bridge_config,
    write_manifest_capnp,
};
use obend_sandbox::gate::{GateStatus, LaunchGate};
use obend_sandbox::line_channel::{
    BodyChannel, BodyMsg, ConfinedAction, ConfinedBrain, DoneNote, LineChannel, Proposal, Verdict,
};
use obend_sandbox::meter::CpuMeter;
use obend_sandbox::policy::{
    AddFdError, CheckedAddFdSpec, ConfinementPolicy, ConnectFilterError, DoorMode,
    EnvAllowlistPolicy, LINUX_AF_INET, LINUX_AF_UNIX, LINUX_SOCK_STREAM, SECCOMP_RET_ALLOW,
    SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_KILL_PROCESS, SECCOMP_RET_USER_NOTIF, SeccompProfileSpec,
    build_hardened_seccomp_bpf, check_addfd_ioctl_result, eval_seccomp_bpf,
    validate_connect_sockaddr,
};
use obend_sandbox::secret_seal::{
    SecretSealError, SecretSlotId, SlotBoundSecretStore, seal_secret_for_slot,
    unseal_secret_for_slot,
};
use obend_sandbox::spk::{
    AppId, Ed25519SigningKey, MANIFEST_PATH, ManifestError, SPK_MAGIC, Spk, SpkArchive, SpkBuilder,
    SpkError, SpkFile, SpkManifest, decode_bridge_config_capnp, sandstorm_base32_encode,
    xz_compress, xz_decompress_bounded,
};
use obend_sandbox::wasm_budget::{
    WasmCapTier, WasmExecutionBudget, WasmRunError, WasmVal, run_wasm_metered,
};
use sha2::{Digest, Sha512};
use std::fs::{self, File};
use std::io::{Cursor, Write};
use std::path::PathBuf;

// Exact captured upstream GitWeb `sandstorm-http-bridge-config` Cap'n Proto fixture
// (`minidregg/native/spk-rpc/tests/fixtures/gitweb-signed-bridge-config.capnp`,
// SHA-256 `49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2`).
const GITWEB_BRIDGE_CONFIG_HEX: &str = concat!(
    "0000000047000000000000000100030000000000000000000800000000000800",
    "050100005a00000000000000000000001d000000470000008500000057000000",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000008000000010003000000000000000000",
    "18000000000002002000000000000200310000002a0000000000000000000000",
    "2c0000000000020034000000000002004500000032000000050000002a000000",
    "00000000000000007265616400000000050000009a0000000000000000000000",
    "616c6c6f77732060676974206665746368600000000000007265616400000000",
    "0500000032000000000000000000000077726974650000000500000092000000",
    "0000000000000000616c6c6f7773206067697420707573686000000000000000",
    "7772697465000000080000000100040000000000000000002000000000000200",
    "2800000000000200000000000000000031000000110000000200000000000000",
    "2c00000000000200380000000000020000000000000000004500000011000000",
    "050000003200000000000000000000006775657374000000050000004a000000",
    "000000000000000063616e207265616400000000000000000100000000000000",
    "05000000520000000000000000000000646576656c6f70657200000000000000",
    "050000009a000000000000000000000063616e207265616420616e6420777269",
    "746500000000000003000000000000002f7265706f2e6769742f000000000000",
);

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        let s = std::str::from_utf8(&bytes[i..i + 2]).unwrap();
        out.push(u8::from_str_radix(s, 16).unwrap());
        i += 2;
    }
    out
}

#[test]
fn test_adversarial_bwrap_strict_isolation_flags() {
    let config = SandboxConfig {
        allow_network: false,
        scratch_mib: Some(512),
        workspace_dir: PathBuf::from("/srv/obend/workspace"),
        runtime_root: PathBuf::from("/srv/obend/runtime"),
        ..SandboxConfig::default()
    };

    let flags = BubblewrapRunner::build_flags(&config);

    assert!(flags.contains(&"--die-with-parent".to_string()));
    assert!(flags.contains(&"--new-session".to_string()));
    assert!(flags.contains(&"--unshare-user".to_string()));
    assert!(flags.contains(&"--disable-userns".to_string()));
    assert!(flags.contains(&"--unshare-pid".to_string()));
    assert!(flags.contains(&"--unshare-ipc".to_string()));
    assert!(flags.contains(&"--unshare-uts".to_string()));
    assert!(flags.contains(&"--unshare-cgroup".to_string()));
    assert!(flags.contains(&"--unshare-net".to_string()));
    assert!(!flags.contains(&"--share-net".to_string()));

    let cap_idx = flags
        .iter()
        .position(|f| f == "--cap-drop")
        .expect("cap-drop present");
    assert_eq!(flags[cap_idx + 1], "ALL");
    assert!(flags.contains(&"--clearenv".to_string()));
    assert!(flags.contains(&"/usr".to_string()));
    assert!(flags.contains(&"/workspace".to_string()));
    assert!(flags.contains(&"/agent".to_string()));

    let expected_scratch_bytes = (512u64 * 1024 * 1024).to_string();
    assert!(flags.contains(&expected_scratch_bytes));
}

#[test]
fn test_adversarial_bwrap_network_isolation_toggle() {
    let no_net = SandboxConfig {
        allow_network: false,
        ..SandboxConfig::default()
    };
    let flags_no_net = BubblewrapRunner::build_flags(&no_net);
    assert!(flags_no_net.contains(&"--unshare-net".to_string()));
    assert!(!flags_no_net.contains(&"--share-net".to_string()));

    let with_net = SandboxConfig {
        allow_network: true,
        ..SandboxConfig::default()
    };
    let flags_with_net = BubblewrapRunner::build_flags(&with_net);
    assert!(flags_with_net.contains(&"--share-net".to_string()));
    assert!(!flags_with_net.contains(&"--unshare-net".to_string()));
}

#[test]
fn test_adversarial_cap17_env_leak_seatbelt_seccomp_addfd_and_pdeathsig() {
    let runner = BubblewrapRunner::new();

    // 1. CAP-17 Parent Env Secret Leak Refusal (live child execution + real bwrap when available)
    std::env::set_var("OBEND_CAP17_LIVE_SECRET", "DO_NOT_LEAK_TO_SANDBOX_42");
    std::env::set_var("OBEND_CAP17_EXPLICIT_ALLOW", "ALLOWED_PUBLIC_TAG");

    let tmp = std::env::temp_dir().join(format!("obend_g11_cap17_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    let ws = tmp.join("ws");
    let rt = tmp.join("rt");
    fs::create_dir_all(&ws).unwrap();
    fs::create_dir_all(&rt).unwrap();

    // 1a. Verify `SandboxBackend::Bubblewrap` spawn path scrubs host env BEFORE exec'ing `bwrap`
    //     and passes `--clearenv` + exact `--setenv` pairs (deterministic even under Ubuntu 24.04
    //     `apparmor_restrict_unprivileged_userns = 1`).
    let bwrap_probe = tmp.join("probe_bwrap.sh");
    fs::write(
        &bwrap_probe,
        "#!/bin/sh\n/usr/bin/env\necho '---ARGS---'\nprintf '%s\\n' \"$@\"\n",
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&bwrap_probe, fs::Permissions::from_mode(0o755)).unwrap();
    }

    let bwrap_cfg = SandboxConfig {
        bwrap_binary: bwrap_probe,
        workspace_dir: ws.clone(),
        runtime_root: rt.clone(),
        allow_unsandboxed_fallback: false,
        env_policy: EnvAllowlistPolicy::strict()
            .with_passthrough_key("OBEND_CAP17_EXPLICIT_ALLOW")
            .with_explicit_var("OBEND_FIXED_MODE", "confined"),
        ..SandboxConfig::default()
    };
    #[cfg(target_os = "linux")]
    {
        let bwrap_receipt = runner
            .execute_sandboxed_with_config(
                &bwrap_cfg,
                "/usr/bin/env",
                &[],
                5000,
                DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            )
            .expect("Bubblewrap backend env probe");
        assert!(bwrap_receipt.success);
        assert_eq!(bwrap_receipt.backend, SandboxBackend::Bubblewrap);
        assert!(!bwrap_receipt.is_fallback);
        let probe_out = String::from_utf8_lossy(&bwrap_receipt.stdout);
        assert!(
            !probe_out.contains("OBEND_CAP17_LIVE_SECRET")
                && !probe_out.contains("DO_NOT_LEAK_TO_SANDBOX_42"),
            "CAP-17 env leak on Bubblewrap spawn path MUST be scrubbed: {probe_out}"
        );
        assert!(probe_out.contains("OBEND_CAP17_EXPLICIT_ALLOW=ALLOWED_PUBLIC_TAG"));
        assert!(probe_out.contains("OBEND_FIXED_MODE=confined"));
        assert!(probe_out.contains("--clearenv"));
    }

    // 1b. Also verify real `/usr/bin/bwrap` when permitted by host AppArmor, or verify it fails
    //     closed without unsandboxed fallback when `apparmor_restrict_unprivileged_userns = 1` blocks netns.
    let real_bwrap_cfg = SandboxConfig {
        workspace_dir: ws.clone(),
        runtime_root: rt.clone(),
        allow_unsandboxed_fallback: true,
        env_policy: bwrap_cfg.env_policy.clone(),
        ..SandboxConfig::default()
    };
    let real_receipt = runner
        .execute_sandboxed_with_config(
            &real_bwrap_cfg,
            "/usr/bin/env",
            &[],
            5000,
            DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
        )
        .expect("real sandboxed /usr/bin/env invocation");
    if real_receipt.success {
        let real_out = String::from_utf8_lossy(&real_receipt.stdout);
        assert!(
            !real_out.contains("OBEND_CAP17_LIVE_SECRET")
                && !real_out.contains("DO_NOT_LEAK_TO_SANDBOX_42")
        );
        assert!(real_out.contains("OBEND_CAP17_EXPLICIT_ALLOW=ALLOWED_PUBLIC_TAG"));
    } else {
        // Host AppArmor blocked unprivileged `bwrap` userns/netns — MUST NOT fall back to host!
        assert_eq!(real_receipt.backend, SandboxBackend::Bubblewrap);
        assert!(!real_receipt.is_fallback);
    }

    // 1c. Verify `MeteredProcessFallback` backend ALSO enforces `CAP-17` strict env allowlist.
    let cfg = SandboxConfig {
        bwrap_binary: PathBuf::from("/nonexistent/bwrap"),
        workspace_dir: ws,
        runtime_root: rt,
        allow_unsandboxed_fallback: true,
        env_policy: bwrap_cfg.env_policy.clone(),
        ..SandboxConfig::default()
    };

    #[cfg(target_os = "linux")]
    {
        let receipt = runner
            .execute_sandboxed_with_config(
                &cfg,
                "/usr/bin/env",
                &[],
                5000,
                DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            )
            .expect("confined /usr/bin/env execution");
        assert!(receipt.success);
        let out_str = String::from_utf8_lossy(&receipt.stdout);
        assert!(
            !out_str.contains("OBEND_CAP17_LIVE_SECRET")
                && !out_str.contains("DO_NOT_LEAK_TO_SANDBOX_42"),
            "CAP-17 env leak MUST be scrubbed: {out_str}"
        );
        assert!(out_str.contains("OBEND_CAP17_EXPLICIT_ALLOW=ALLOWED_PUBLIC_TAG"));
        assert!(out_str.contains("OBEND_FIXED_MODE=confined"));
    }

    // Forbidden loader injection keys (`LD_PRELOAD`, `DYLD_INSERT_LIBRARIES`, `BASH_ENV`) are refused!
    for bad_key in ["LD_PRELOAD", "DYLD_INSERT_LIBRARIES", "BASH_ENV"] {
        let mut bad_cfg = cfg.clone();
        bad_cfg.env_policy = EnvAllowlistPolicy::strict().with_passthrough_key(bad_key);
        assert!(
            matches!(
                runner.execute_sandboxed_with_config(
                    &bad_cfg,
                    "/usr/bin/env",
                    &[],
                    2000,
                    DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
                ),
                Err(SandboxError::InvalidCommand(_))
            ),
            "forbidden env key {bad_key} must fail closed"
        );
    }

    // 2. Default-Deny Seatbelt Profile: zero `(allow process*)`, zero blanket `mach-lookup`,
    //    zero `/tmp` write, and non-loopback egress refused!
    let sb = BubblewrapRunner::try_build_seatbelt_profile(&cfg).unwrap();
    assert!(!sb.contains("(allow process*)"));
    assert!(!sb.contains("(allow mach-lookup)"));
    assert!(!sb.contains("(subpath \"/tmp\")"));
    assert!(!sb.contains("(subpath \"/etc\")"));
    let mut non_loopback = cfg.clone();
    non_loopback.egress_endpoints = vec!["10.20.30.40:443".into()];
    assert!(BubblewrapRunner::try_build_seatbelt_profile(&non_loopback).is_err());

    // 3. Seccomp `AF_UNIX` socket/connect/sendto filter + `ADDFD` bounds
    let spec = SeccompProfileSpec::linux_x86_64();
    let bpf = build_hardened_seccomp_bpf(&spec, DoorMode::ProviderNotify, true);
    assert_eq!(
        eval_seccomp_bpf(
            &bpf,
            spec.arch,
            spec.socket_nr,
            [LINUX_AF_UNIX as u64, LINUX_SOCK_STREAM as u64, 0, 0, 0, 0]
        ),
        SECCOMP_RET_ERRNO_EPERM
    );
    assert_eq!(
        eval_seccomp_bpf(
            &bpf,
            spec.arch,
            spec.socket_nr,
            [LINUX_AF_INET as u64, LINUX_SOCK_STREAM as u64, 0, 0, 0, 0]
        ),
        SECCOMP_RET_ALLOW
    );
    assert_eq!(
        eval_seccomp_bpf(&bpf, spec.arch, spec.connect_nr, [4, 0x1000, 16, 0, 0, 0]),
        SECCOMP_RET_USER_NOTIF
    );
    assert_eq!(
        eval_seccomp_bpf(&bpf, 0x4000_0003 /* i386 */, 0, [0; 6]),
        SECCOMP_RET_KILL_PROCESS
    );

    let mut af_unix_sa = [0u8; 20];
    af_unix_sa[0..2].copy_from_slice(&(LINUX_AF_UNIX as u16).to_ne_bytes());
    assert_eq!(
        validate_connect_sockaddr(&af_unix_sa, 20, &[([127, 0, 0, 1], 8080)]),
        Err(ConnectFilterError::AfUnixForbidden)
    );
    assert_eq!(
        CheckedAddFdSpec::validate(0, 8, &[3], 1024),
        Err(AddFdError::ReservedStdStreamFd(0))
    );
    assert_eq!(
        CheckedAddFdSpec::validate(3, 8, &[3], 1024),
        Err(AddFdError::ProtectedEndpointFdCollision(3))
    );
    assert_eq!(check_addfd_ioctl_result(-1, Some(libc::EPERM)), Err(-libc::EPERM));

    // 4. Linux `PR_SET_PDEATHSIG(SIGKILL)` supervisor-death grandchild reap verification
    #[cfg(target_os = "linux")]
    {
        use std::time::{Duration, Instant};
        // Fork a middle "supervisor" process that spawns a grandchild with `install_pdeathsig_sigkill`,
        // reports the grandchild PID over a pipe, and is then SIGKILLed; the grandchild MUST die immediately!
        let mut pipe_fds = [0i32; 2];
        assert_eq!(unsafe { libc::pipe(pipe_fds.as_mut_ptr()) }, 0);
        let sup_pid = unsafe { libc::fork() };
        assert!(sup_pid >= 0);
        if sup_pid == 0 {
            unsafe {
                libc::close(pipe_fds[0]);
                let my_pid = libc::getpid();
                let gc_pid = libc::fork();
                if gc_pid == 0 {
                    let _ = obend_sandbox::install_pdeathsig_sigkill(my_pid);
                    libc::close(pipe_fds[1]);
                    loop {
                        libc::pause();
                    }
                }
                let bytes = gc_pid.to_le_bytes();
                let _ = libc::write(pipe_fds[1], bytes.as_ptr() as *const libc::c_void, 4);
                libc::close(pipe_fds[1]);
                loop {
                    libc::pause();
                }
            }
        }
        unsafe {
            libc::close(pipe_fds[1]);
        }
        let mut pid_bytes = [0u8; 4];
        let n = unsafe {
            libc::read(pipe_fds[0], pid_bytes.as_mut_ptr() as *mut libc::c_void, 4)
        };
        unsafe {
            libc::close(pipe_fds[0]);
        }
        assert_eq!(n, 4);
        let grandchild_pid = i32::from_le_bytes(pid_bytes);
        assert!(grandchild_pid > 0);

        // Kill ONLY `sup_pid` (NOT `grandchild_pid`!): `PR_SET_PDEATHSIG(SIGKILL)` must reap the grandchild!
        unsafe {
            libc::kill(sup_pid, libc::SIGKILL);
            let mut st = 0;
            libc::waitpid(sup_pid, &mut st, 0);
        }
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let alive = unsafe { libc::kill(grandchild_pid, 0) == 0 };
            let zombie = fs::read_to_string(format!("/proc/{grandchild_pid}/stat"))
                .ok()
                .and_then(|s| s.split_once(") ").map(|(_, t)| t.starts_with('Z')))
                .unwrap_or(true);
            if !alive || zombie {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "CAP-17 orphan grandchild {grandchild_pid} survived supervisor SIGKILL!"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    let _ = fs::remove_dir_all(&tmp);
}

#[test]
fn test_adversarial_spk_verify_strict_forgeries_and_system_xz_interop() {
    let key = Ed25519SigningKey::from_bytes(&[0x33u8; 32]);
    let manifest_json = r#"{
      "app_id": "forged-manifest-self-claim",
      "app_title": "Etherpad",
      "app_version": 33,
      "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
      "bridge_config": {
        "api_port": 8000,
        "permissions": ["view", "edit"],
        "roles": [
          { "title": "editor", "permissions": ["view", "edit"], "default": true },
          { "title": "viewer", "permissions": ["view"] }
        ]
      }
    }"#;

    let valid_spk = SpkBuilder::new()
        .manifest_json(manifest_json)
        .file(SpkFile::executable("start.sh", b"#!/bin/sh\nexec /app\n".to_vec()))
        .pack(&key);

    let parsed = Spk::verify_strict(&valid_spk).expect("valid .spk must verify");
    assert_eq!(
        parsed.app_id(),
        AppId(sandstorm_base32_encode(&key.verifying_key_bytes()))
    );
    let m = SpkManifest::from_spk(&parsed).unwrap();
    // Intrinsic AppId overrides manifest's self-claimed `app_id`!
    assert_eq!(m.app_id, parsed.app_id());
    assert_eq!(m.resolve_role_permissions("viewer").unwrap(), vec!["view"]);
    assert_eq!(
        m.resolve_role_permissions("editor").unwrap(),
        vec!["view", "edit"]
    );

    // Attack 1: Bad magic rejected
    let mut bad_magic = valid_spk.clone();
    bad_magic[0] ^= 0x01;
    assert_eq!(Spk::verify_strict(&bad_magic).unwrap_err(), SpkError::BadMagic);

    // Attack 2: Corrupted archive byte inside valid XZ container -> BadSignature!
    let archive_msg = SpkArchive {
        files: vec![SpkFile::regular(MANIFEST_PATH, b"{}".to_vec())],
    }
    .to_capnp_bytes();
    let hash: [u8; 64] = Sha512::digest(&archive_msg).into();
    let sig = key.sign(&hash);
    let mut tampered_archive = archive_msg.clone();
    let last = tampered_archive.len() - 1;
    tampered_archive[last] ^= 0xFF;
    let mut sig_field = sig.to_vec();
    sig_field.extend_from_slice(&hash);
    let mut plain_tampered =
        capnp_wire::write_signature(&key.verifying_key_bytes(), &sig_field);
    plain_tampered.extend_from_slice(&tampered_archive);
    let mut spk_tampered = SPK_MAGIC.to_vec();
    spk_tampered.extend_from_slice(&xz_compress(&plain_tampered));
    assert_eq!(
        Spk::verify_strict(&spk_tampered).unwrap_err(),
        SpkError::BadSignature
    );

    // Attack 3: Non-canonical `s + L` signature malleability -> BadSignature!
    const ELL: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
        0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
    ];
    let mut malleable_sig = sig;
    let mut carry = 0u16;
    for (b, l) in malleable_sig[32..].iter_mut().zip(ELL) {
        let sum = u16::from(*b) + u16::from(l) + carry;
        *b = sum as u8;
        carry = sum >> 8;
    }
    let mut mal_field = malleable_sig.to_vec();
    mal_field.extend_from_slice(&hash);
    let mut plain_mal = capnp_wire::write_signature(&key.verifying_key_bytes(), &mal_field);
    plain_mal.extend_from_slice(&archive_msg);
    let mut spk_mal = SPK_MAGIC.to_vec();
    spk_mal.extend_from_slice(&xz_compress(&plain_mal));
    assert_eq!(
        Spk::verify_strict(&spk_mal).unwrap_err(),
        SpkError::BadSignature
    );

    // Attack 4: Small-order weak public key (`[1, 0, ..., 0]`) universal forgery -> BadSignature!
    let mut weak_pk = [0u8; 32];
    weak_pk[0] = 1;
    let mut weak_sig_field = vec![0u8; 64];
    weak_sig_field[0] = 1;
    weak_sig_field.extend_from_slice(&hash);
    let mut plain_weak = capnp_wire::write_signature(&weak_pk, &weak_sig_field);
    plain_weak.extend_from_slice(&archive_msg);
    let mut spk_weak = SPK_MAGIC.to_vec();
    spk_weak.extend_from_slice(&xz_compress(&plain_weak));
    assert_eq!(
        Spk::verify_strict(&spk_weak).unwrap_err(),
        SpkError::BadSignature
    );

    // Attack 5: Signed trailing bytes after `Archive` message -> TrailingBytes!
    let mut arch_plus_tail = archive_msg.clone();
    arch_plus_tail.extend_from_slice(&[0xAA; 8]);
    let tail_hash: [u8; 64] = Sha512::digest(&arch_plus_tail).into();
    let mut tail_sig_field = key.sign(&tail_hash).to_vec();
    tail_sig_field.extend_from_slice(&tail_hash);
    let mut plain_tail =
        capnp_wire::write_signature(&key.verifying_key_bytes(), &tail_sig_field);
    plain_tail.extend_from_slice(&arch_plus_tail);
    let mut spk_tail = SPK_MAGIC.to_vec();
    spk_tail.extend_from_slice(&xz_compress(&plain_tail));
    assert_eq!(
        Spk::verify_strict(&spk_tail).unwrap_err(),
        SpkError::TrailingBytes { count: 8 }
    );

    // Attack 6: Unsigned trailing bytes after XZ footer -> Decompress error!
    let mut trailing_xz = valid_spk.clone();
    trailing_xz.extend_from_slice(b"EXTRA");
    assert!(matches!(
        Spk::verify_strict(&trailing_xz),
        Err(SpkError::Decompress(_))
    ));

    // Attack 7: Symlink escape (`../../etc/shadow`) and XZ decompression bomb -> refused!
    let escaping = SpkBuilder::new()
        .file(SpkFile::symlink("escape", "../../etc/shadow"))
        .pack(&key);
    assert!(matches!(
        Spk::verify_strict(&escaping),
        Err(SpkError::SymlinkEscape { .. })
    ));
    let big = SpkBuilder::new()
        .file(SpkFile::regular("big", vec![0x41u8; 128 * 1024]))
        .pack(&key);
    assert_eq!(
        Spk::verify_strict_with_limit(&big, 32 * 1024).unwrap_err(),
        SpkError::TooLarge
    );

    // Bidirectional interop with upstream `/usr/bin/xz` (LZMA2 range-coded stream!) when present on host
    if std::path::Path::new("/usr/bin/xz").exists() {
        use std::process::{Command, Stdio};
        // (a) `/usr/bin/xz -dc` decodes our `xz_compress` container
        let mut dec = Command::new("/usr/bin/xz")
            .arg("-dc")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        dec.stdin
            .take()
            .unwrap()
            .write_all(&valid_spk[SPK_MAGIC.len()..])
            .unwrap();
        let dec_out = dec.wait_with_output().unwrap();
        assert!(dec_out.status.success(), "system xz -dc accepted our container");

        // (b) `/usr/bin/xz -6 -c` compresses `dec_out.stdout` with real LZMA2 range-coding,
        //     and our `Spk::verify_strict` decodes and verifies it!
        let mut enc = Command::new("/usr/bin/xz")
            .args(["-6", "-c"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        enc.stdin.take().unwrap().write_all(&dec_out.stdout).unwrap();
        let enc_out = enc.wait_with_output().unwrap();
        assert!(enc_out.status.success());
        let _ = xz_decompress_bounded(&enc_out.stdout, 1024 * 1024).unwrap();
        let mut real_lzma2_spk = SPK_MAGIC.to_vec();
        real_lzma2_spk.extend_from_slice(&enc_out.stdout);
        let reparsed = Spk::verify_strict(&real_lzma2_spk).expect("LZMA2-compressed .spk verifies");
        assert_eq!(reparsed.app_id(), parsed.app_id());
    }
}

#[test]
fn test_adversarial_manifest_rs_287_gitweb_fixture_and_role_escalation_refusal() {
    // 1. Decode exact captured upstream GitWeb `sandstorm-http-bridge-config` Cap'n Proto bytes!
    let gitweb_bytes = hex_to_bytes(GITWEB_BRIDGE_CONFIG_HEX);
    let bc = decode_bridge_config_capnp(&gitweb_bytes, Some(8000)).unwrap();
    assert_eq!(bc.api_port, Some(8000));
    assert_eq!(bc.api_path.as_deref(), Some("/repo.git/"));
    assert_eq!(bc.permissions, vec!["read", "write"]);
    assert_eq!(bc.roles.len(), 2);
    assert_eq!(bc.roles[0].title, "guest");
    assert_eq!(bc.roles[0].permissions, vec!["read"]);
    assert!(!bc.roles[0].default);
    assert_eq!(bc.roles[1].title, "developer");
    assert_eq!(bc.roles[1].permissions, vec!["read", "write"]);
    assert!(bc.roles[1].default);

    // Pack into a full signed Cap'n Proto `.spk` and verify `SpkManifest::from_spk` recovers roles!
    let key = Ed25519SigningKey::from_bytes(&[0x55u8; 32]);
    let manifest_capnp = write_manifest_capnp(
        "GitWeb",
        19,
        "2.43.0",
        &["/sandstorm-http-bridge", "8000", "--", "/opt/app/start.sh"],
    );
    let gitweb_spk_bytes = SpkBuilder::new()
        .manifest_capnp(manifest_capnp.clone())
        .bridge_config_capnp(gitweb_bytes.clone())
        .pack(&key);
    let spk = Spk::verify_strict(&gitweb_spk_bytes).unwrap();
    let manifest = SpkManifest::from_spk(&spk).unwrap();
    assert_eq!(manifest.declared_permissions(), vec!["read", "write"]);
    assert_eq!(manifest.resolve_role_permissions("guest").unwrap(), vec!["read"]);
    assert_eq!(
        manifest.resolve_role_permissions("developer").unwrap(),
        vec!["read", "write"]
    );
    assert!(matches!(
        manifest.resolve_role_permissions("nonexistent_admin"),
        Err(ManifestError::UnknownRole(_))
    ));

    // 2. Role escalation attempts (undeclared permissions, ambiguous defaults, header-injection names, path traversal apiPath)
    let ambig_bc = write_bridge_config(&WireBridgeConfig {
        app_title: "BadApp",
        permissions: &[WirePermissionDef {
            name: "read",
            title: "Read",
            obsolete: false,
        }],
        roles: &[
            WireRoleDef {
                title: "r1",
                verb_phrase: "v1",
                permissions: &[true],
                obsolete: false,
                default: true,
            },
            WireRoleDef {
                title: "r2",
                verb_phrase: "v2",
                permissions: &[true],
                obsolete: false,
                default: true,
            },
        ],
        denied_permissions: &[],
        api_path: None,
        save_identity_caps: false,
        expect_app_hooks: false,
    });
    assert_eq!(
        SpkManifest::from_capnp_with_bridge_config(&manifest_capnp, Some(&ambig_bc)).unwrap_err(),
        ManifestError::AmbiguousDefaultRole
    );

    let header_inject_bc = write_bridge_config(&WireBridgeConfig {
        app_title: "Inject",
        permissions: &[WirePermissionDef {
            name: "read,admin\r\nX-Evil: 1",
            title: "Inject",
            obsolete: false,
        }],
        roles: &[],
        denied_permissions: &[],
        api_path: None,
        save_identity_caps: false,
        expect_app_hooks: false,
    });
    assert!(matches!(
        SpkManifest::from_capnp_with_bridge_config(&manifest_capnp, Some(&header_inject_bc)),
        Err(ManifestError::InvalidPermissionName(_))
    ));

    let bad_api_path_bc = write_bridge_config(&WireBridgeConfig {
        app_title: "Traversal",
        permissions: &[],
        roles: &[],
        denied_permissions: &[],
        api_path: Some("/../escape/"),
        save_identity_caps: false,
        expect_app_hooks: false,
    });
    assert!(matches!(
        SpkManifest::from_capnp_with_bridge_config(&manifest_capnp, Some(&bad_api_path_bc)),
        Err(ManifestError::InvalidApiPath(_))
    ));
}

#[test]
fn test_adversarial_line_channel_oversized_frame_wasm_fuel_and_wrong_slot_aad() {
    // 1. Oversized `LineChannel` frame refused & channel poisoned (both newline-free flood and newline-terminated oversize)
    let smuggled_tail = serde_json::to_string(&BodyMsg::Propose(Proposal::invoke("escalate"))).unwrap();
    let flood_payload = format!("{}{}\n", "Z".repeat(512), smuggled_tail);
    let mut ch = LineChannel::new(Cursor::new(flood_payload.into_bytes()), Vec::new())
        .with_max_line_bytes(128);
    assert!(ch.recv().is_err(), "oversized LineChannel frame must be refused");
    assert!(ch.is_poisoned());
    assert!(
        ch.recv().is_err(),
        "poisoned LineChannel must never parse trailing smuggled JSON"
    );

    // Valid bounded session still works cleanly
    let ok_wire = format!(
        "{}\n{}\n",
        serde_json::to_string(&BodyMsg::Propose(Proposal::invoke("ping"))).unwrap(),
        serde_json::to_string(&BodyMsg::Done(DoneNote::default())).unwrap()
    );
    let mut brain = ConfinedBrain::new(
        LineChannel::new(Cursor::new(ok_wire.into_bytes()), Vec::new()).with_max_line_bytes(256),
    );
    assert_eq!(
        brain.next_action(),
        Some(ConfinedAction::Invoke {
            service: "ping".into()
        })
    );
    brain.observe(&Verdict::admit(true, Some("pong".into())));
    assert_eq!(brain.next_action(), None);

    // 2. Fuel-metered Wasm execution budget (`CAP-23` infinite loop & memory bomb refused)
    let wasm_loop: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
        0x03, 0x02, 0x01, 0x00,
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
        0x0a, 0x09, 0x01, 0x07, 0x00, 0x03, 0x40, 0x0c, 0x00, 0x0b, 0x0b,
    ];
    assert_eq!(
        run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_loop,
            "run",
            &[],
            &WasmExecutionBudget::new(100, 65_536)
        ),
        Err(WasmRunError::OutOfFuel {
            max_fuel: 100,
            consumed: 100
        })
    );
    let wasm_huge_mem: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
        0x03, 0x02, 0x01, 0x00,
        0x05, 0x03, 0x01, 0x00, 0x20, // 32 initial pages = 2 MiB
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
        0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x07, 0x0b,
    ];
    assert_eq!(
        run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_huge_mem,
            "run",
            &[],
            &WasmExecutionBudget::new(1000, 65_536) // 64 KiB cap
        ),
        Err(WasmRunError::MemoryLimitExceeded {
            requested_bytes: 32 * 65_536,
            max_bytes: 65_536
        })
    );
    let ok_wasm_rec = run_wasm_metered(
        WasmCapTier::Sandboxed,
        wasm_huge_mem,
        "run",
        &[],
        &WasmExecutionBudget::new(1000, 4 * 1024 * 1024),
    )
    .unwrap();
    assert_eq!(ok_wasm_rec.results, vec![WasmVal::I32(7)]);

    // 3. Wrong-slot AAD secret unseal refused (both direct envelope & on-disk file swap)
    let master_key = [0x9Au8; 32];
    let slot_origin = SecretSlotId::new("grain-7", "oauth_refresh_token");
    let slot_wrong_key = SecretSlotId::new("grain-7", "public_webhook_secret");
    let slot_wrong_ns = SecretSlotId::new("grain-8", "oauth_refresh_token");

    let sealed = seal_secret_for_slot(&master_key, &slot_origin, b"v1", b"rt_super_secret").unwrap();
    assert_eq!(
        unseal_secret_for_slot(&master_key, &slot_origin, b"v1", &sealed)
            .unwrap()
            .as_bytes(),
        b"rt_super_secret"
    );
    assert!(matches!(
        unseal_secret_for_slot(&master_key, &slot_wrong_key, b"v1", &sealed),
        Err(SecretSealError::AuthenticationFailed)
    ));
    assert!(matches!(
        unseal_secret_for_slot(&master_key, &slot_wrong_ns, b"v1", &sealed),
        Err(SecretSealError::AuthenticationFailed)
    ));
    assert!(matches!(
        unseal_secret_for_slot(&master_key, &slot_origin, b"v2-wrong-ctx", &sealed),
        Err(SecretSealError::AuthenticationFailed)
    ));

    let dir = std::env::temp_dir().join(format!("obend_adv_secrets_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    let store = SlotBoundSecretStore::new(&dir, master_key).with_context_aad(b"prod-host");
    store.put(&slot_origin, b"secret-alpha").unwrap();
    store.put(&slot_wrong_key, b"secret-beta").unwrap();
    fs::copy(
        store.secret_file_path(&slot_origin),
        store.secret_file_path(&slot_wrong_key),
    )
    .unwrap();
    assert!(matches!(
        store.get(&slot_wrong_key),
        Err(SecretSealError::AuthenticationFailed)
    ));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn test_adversarial_launch_gate_lifecycle_state_machine() {
    let tmp = std::env::temp_dir().join(format!("obend-test-gate-{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    fs::create_dir_all(&tmp).expect("create test tmpdir");

    let gate = LaunchGate::new(&tmp, "obend-grain-t1-o1");

    assert!(gate.status().is_err());
    gate.init().expect("gate init");
    assert_eq!(gate.status().expect("status"), GateStatus::Armed);
    assert!(gate.init().is_err(), "double init must fail");

    gate.transition_to_started().expect("transition to started");
    assert_eq!(gate.status().expect("status"), GateStatus::Started);
    assert!(
        gate.transition_to_started().is_err(),
        "second transition to started must fail"
    );

    gate.fence().expect("fence");
    assert_eq!(gate.status().expect("status"), GateStatus::Fenced);
    assert!(
        gate.transition_to_started().is_err(),
        "transition to started from fenced must fail"
    );

    let path = gate.gate_path();
    let mut file = File::create(&path).expect("truncate gate");
    file.write_all(b"malformed_bogus_state\n")
        .expect("write corrupt");
    drop(file);
    assert!(gate.status().is_err(), "corrupted gate must fail status parse");
    assert!(
        gate.transition_to_started().is_err(),
        "transition on corrupted gate must fail"
    );

    let _ = fs::remove_dir_all(&tmp);
}

#[test]
fn test_adversarial_cgroup_cpu_meter_parsing() {
    let sample = r#"usage_usec 987654321
user_usec 500000000
system_usec 487654321
core_sched.force_idle_usec 0
nr_periods 1234
nr_throttled 56
throttled_usec 78900
"#;
    let rec = CpuMeter::parse_cpu_stat(sample);
    assert_eq!(rec, Some(987654321));

    let partial = "user_usec 500\nusage_usec 1000\n";
    let rec_part = CpuMeter::parse_cpu_stat(partial);
    assert_eq!(rec_part, Some(1000));

    let corrupt = "usage_usec not_a_number\nunknown_key 99999\n\n\n";
    let rec_corrupt = CpuMeter::parse_cpu_stat(corrupt);
    assert_eq!(rec_corrupt, None);

    let empty = "";
    assert_eq!(CpuMeter::parse_cpu_stat(empty), None);
}

#[test]
fn test_adversarial_confinement_policy_strict_and_seccomp() {
    let mut policy = ConfinementPolicy::strict();
    policy.seccomp_filter = Some(PathBuf::from("/etc/seccomp/resident.bpf"));

    let flags = policy.to_bwrap_flags();
    assert!(flags.contains(&"--die-with-parent".to_string()));
    assert!(flags.contains(&"--unshare-net".to_string()));
    assert!(flags.contains(&"--cap-drop".to_string()));
    assert!(flags.contains(&"--disable-userns".to_string()));
    assert!(flags.contains(&"--clearenv".to_string()));

    let sec_idx = flags
        .iter()
        .position(|f| f == "--seccomp")
        .expect("seccomp present");
    assert_eq!(flags[sec_idx + 1], "/etc/seccomp/resident.bpf");
}
