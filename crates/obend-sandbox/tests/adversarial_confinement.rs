use obend_sandbox::bwrap::{BubblewrapRunner, SandboxConfig};
use obend_sandbox::gate::{GateStatus, LaunchGate};
use obend_sandbox::meter::CpuMeter;
use obend_sandbox::policy::ConfinementPolicy;
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

#[test]
fn test_adversarial_bwrap_strict_isolation_flags() {
    let mut config = SandboxConfig::default();
    config.allow_network = false;
    config.scratch_mib = Some(512);
    config.workspace_dir = PathBuf::from("/srv/obend/workspace");
    config.runtime_root = PathBuf::from("/srv/obend/runtime");

    let flags = BubblewrapRunner::build_flags(&config);

    // 1. Mandatory namespace isolation flags
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

    // 2. Capability drop
    let cap_idx = flags.iter().position(|f| f == "--cap-drop").expect("cap-drop present");
    assert_eq!(flags[cap_idx + 1], "ALL");

    // 3. Environment cleansing
    assert!(flags.contains(&"--clearenv".to_string()));

    // 4. Root mounts and read-only containment
    assert!(flags.contains(&"/usr".to_string()));
    assert!(flags.contains(&"/workspace".to_string()));
    assert!(flags.contains(&"/agent".to_string()));

    // 5. Scratch memory quota
    let expected_scratch_bytes = (512u64 * 1024 * 1024).to_string();
    assert!(flags.contains(&expected_scratch_bytes));
}

#[test]
fn test_adversarial_bwrap_network_isolation_toggle() {
    let mut no_net = SandboxConfig::default();
    no_net.allow_network = false;
    let flags_no_net = BubblewrapRunner::build_flags(&no_net);
    assert!(flags_no_net.contains(&"--unshare-net".to_string()));
    assert!(!flags_no_net.contains(&"--share-net".to_string()));

    let mut with_net = SandboxConfig::default();
    with_net.allow_network = true;
    let flags_with_net = BubblewrapRunner::build_flags(&with_net);
    assert!(flags_with_net.contains(&"--share-net".to_string()));
    assert!(!flags_with_net.contains(&"--unshare-net".to_string()));
}

#[test]
fn test_adversarial_launch_gate_lifecycle_state_machine() {
    let tmp = std::env::temp_dir().join(format!("obend-test-gate-{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    fs::create_dir_all(&tmp).expect("create test tmpdir");

    let gate = LaunchGate::new(&tmp, "obend-grain-t1-o1");

    // 1. Initial status before creation should fail
    assert!(gate.status().is_err());

    // 2. Init creates armed state
    gate.init().expect("gate init");
    assert_eq!(gate.status().expect("status"), GateStatus::Armed);

    // 3. Double init attack must be rejected
    assert!(gate.init().is_err(), "double init must fail");

    // 4. Transition to started
    gate.transition_to_started().expect("transition to started");
    assert_eq!(gate.status().expect("status"), GateStatus::Started);

    // 5. Double transition to started (replay attack) must fail
    assert!(
        gate.transition_to_started().is_err(),
        "second transition to started must fail"
    );

    // 6. Fence transition
    gate.fence().expect("fence");
    assert_eq!(gate.status().expect("status"), GateStatus::Fenced);

    // 7. Transition from fenced to started must fail
    assert!(
        gate.transition_to_started().is_err(),
        "transition to started from fenced must fail"
    );

    // 8. Corrupted gate content test
    let path = gate.gate_path();
    let mut file = File::create(&path).expect("truncate gate");
    file.write_all(b"malformed_bogus_state\n").expect("write corrupt");
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
    // 1. Valid full cpu.stat
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

    // 2. Partial cpu.stat
    let partial = "user_usec 500\nusage_usec 1000\n";
    let rec_part = CpuMeter::parse_cpu_stat(partial);
    assert_eq!(rec_part, Some(1000));

    // 3. Corrupted lines and missing usage_usec return None
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

    let sec_idx = flags.iter().position(|f| f == "--seccomp").expect("seccomp present");
    assert_eq!(flags[sec_idx + 1], "/etc/seccomp/resident.bpf");
}
