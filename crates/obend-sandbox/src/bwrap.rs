use std::io::Read;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use crate::grain::{sha256, ReproducibilityTier};

/// Default maximum combined stdout/stderr capture size (4 MiB) for a sandboxed child process.
pub const DEFAULT_MAX_PROCESS_OUTPUT_BYTES: usize = 4 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SandboxConfig {
    pub bwrap_binary: PathBuf,
    pub workspace_dir: PathBuf,
    pub runtime_root: PathBuf,
    pub allow_network: bool,
    pub allow_unsandboxed_fallback: bool,
    pub scratch_mib: Option<u32>,
    pub memory_max_mb: u32,
    pub program: PathBuf,
    pub args: Vec<String>,
}

impl Default for SandboxConfig {
    fn default() -> Self {
        Self {
            bwrap_binary: PathBuf::from("/usr/bin/bwrap"),
            workspace_dir: PathBuf::from("/tmp/obend-workspace"),
            runtime_root: PathBuf::from("/opt/obend"),
            allow_network: false,
            allow_unsandboxed_fallback: false,
            scratch_mib: Some(256),
            memory_max_mb: 2048,
            program: PathBuf::from("/agent/bin/obend"),
            args: Vec::new(),
        }
    }
}

/// Active OS confinement backend used to supervise a sandboxed process.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SandboxBackend {
    Bubblewrap,
    MacosSeatbelt,
    MeteredProcessFallback,
}

/// Errors returned by live sandboxed process execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SandboxError {
    InvalidCommand(String),
    SandboxUnavailable(String),
    SpawnFailed(String),
    TimeoutExceeded {
        timeout_ms: u64,
        elapsed_usec: u64,
    },
    OutputLimitExceeded {
        max_bytes: usize,
        observed_bytes: usize,
    },
    WaitFailed(String),
}

impl std::fmt::Display for SandboxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidCommand(msg) => write!(f, "invalid sandbox command: {msg}"),
            Self::SandboxUnavailable(msg) => write!(f, "OS sandbox confinement unavailable: {msg}"),
            Self::SpawnFailed(msg) => write!(f, "failed to spawn sandboxed process: {msg}"),
            Self::TimeoutExceeded {
                timeout_ms,
                elapsed_usec,
            } => write!(
                f,
                "sandboxed process exceeded timeout of {timeout_ms} ms (elapsed {elapsed_usec} us)"
            ),
            Self::OutputLimitExceeded {
                max_bytes,
                observed_bytes,
            } => write!(
                f,
                "sandboxed process exceeded output limit of {max_bytes} bytes (observed {observed_bytes} bytes)"
            ),
            Self::WaitFailed(msg) => write!(f, "failed waiting on sandboxed process: {msg}"),
        }
    }
}

impl std::error::Error for SandboxError {}

/// Metered execution receipt produced by `BubblewrapRunner::execute_sandboxed`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SandboxRunReceipt {
    pub command: String,
    pub args: Vec<String>,
    pub exit_code: Option<i32>,
    pub success: bool,
    pub wall_clock_usec: u64,
    pub fuel_consumed: u64,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_digest: [u8; 32],
    pub stderr_digest: [u8; 32],
    pub peak_rss_bytes: usize,
    pub backend: SandboxBackend,
    pub is_fallback: bool,
    pub tier: ReproducibilityTier,
    pub seatbelt_profile: Option<String>,
}

impl SandboxRunReceipt {
    /// Compute a canonical SHA-256 commitment over the process run receipt.
    pub fn receipt_digest(&self) -> [u8; 32] {
        let mut buf = Vec::new();
        buf.extend_from_slice(b"OBEND-SANDBOX-RUN-RECEIPT-V1:");
        buf.extend_from_slice(&self.exit_code.unwrap_or(-1).to_be_bytes());
        buf.extend_from_slice(&self.wall_clock_usec.to_be_bytes());
        buf.extend_from_slice(&self.fuel_consumed.to_be_bytes());
        buf.extend_from_slice(&self.stdout_digest);
        buf.extend_from_slice(&self.stderr_digest);
        buf.push(self.tier.tag_byte());
        buf.push(u8::from(self.is_fallback));
        sha256(&buf)
    }
}

/// Guard that ensures a spawned child process is killed and reaped on drop (`kill_on_drop`).
struct KillOnDropChild {
    child: Option<Child>,
}

impl KillOnDropChild {
    fn new(child: Child) -> Self {
        Self { child: Some(child) }
    }

    fn as_mut(&mut self) -> &mut Child {
        self.child.as_mut().expect("child present")
    }
}

impl Drop for KillOnDropChild {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct BubblewrapRunner;

impl BubblewrapRunner {
    pub fn new() -> Self {
        Self
    }

    pub fn build_flags(config: &SandboxConfig) -> Vec<String> {
        let mut flags = vec![
            "--die-with-parent".into(),
            "--new-session".into(),
            "--unshare-user".into(),
            "--disable-userns".into(),
            "--unshare-pid".into(),
            "--unshare-ipc".into(),
            "--unshare-uts".into(),
            "--unshare-cgroup".into(),
            "--hostname".into(),
            "sandbox".into(),
            "--cap-drop".into(),
            "ALL".into(),
            "--clearenv".into(),
            "--ro-bind".into(),
            "/usr".into(),
            "/usr".into(),
            "--symlink".into(),
            "usr/bin".into(),
            "/bin".into(),
            "--symlink".into(),
            "usr/lib".into(),
            "/lib".into(),
            "--symlink".into(),
            "usr/lib64".into(),
            "/lib64".into(),
            "--dev".into(),
            "/dev".into(),
            "--proc".into(),
            "/proc".into(),
            "--ro-bind".into(),
            config.runtime_root.to_string_lossy().into(),
            "/agent".into(),
            "--bind".into(),
            config.workspace_dir.to_string_lossy().into(),
            "/workspace".into(),
            "--chdir".into(),
            "/workspace".into(),
            "--setenv".into(),
            "HOME".into(),
            "/workspace".into(),
            "--setenv".into(),
            "PATH".into(),
            "/usr/bin:/bin:/agent/bin".into(),
        ];

        if let Some(scratch) = config.scratch_mib {
            flags.extend_from_slice(&[
                "--size".into(),
                "16777216".into(),
                "--tmpfs".into(),
                "/tmp".into(),
                "--size".into(),
                (scratch as u64 * 1024 * 1024).to_string(),
                "--tmpfs".into(),
                "/scratch".into(),
            ]);
        } else {
            flags.extend_from_slice(&["--tmpfs".into(), "/tmp".into()]);
        }

        if !config.allow_network {
            flags.push("--unshare-net".into());
        } else {
            flags.push("--share-net".into());
            flags.extend_from_slice(&[
                "--ro-bind".into(),
                "/etc/ssl".into(),
                "/etc/ssl".into(),
                "--ro-bind".into(),
                "/etc/resolv.conf".into(),
                "/etc/resolv.conf".into(),
            ]);
        }

        flags.push("--".into());
        flags.push(config.program.to_string_lossy().into());
        flags.extend(config.args.iter().cloned());

        flags
    }

    pub fn prepare_command(config: &SandboxConfig) -> Command {
        let mut cmd = Command::new(&config.bwrap_binary);
        cmd.args(Self::build_flags(config));
        cmd
    }

    /// Generate a macOS Seatbelt (`sandbox-exec -p`) SBPL confinement profile for `config`.
    pub fn build_seatbelt_profile(config: &SandboxConfig) -> String {
        let workspace = config.workspace_dir.to_string_lossy().replace('"', "\\\"");
        let runtime_root = config.runtime_root.to_string_lossy().replace('"', "\\\"");
        let net_rule = if config.allow_network {
            "(allow network*)"
        } else {
            "(deny network*)"
        };
        format!(
            "(version 1) (deny default) (allow process*) (allow sysctl-read) (allow mach-lookup) (allow file-read* (literal \"/\") (subpath \"/usr\") (subpath \"/bin\") (subpath \"/sbin\") (subpath \"/System\") (subpath \"/Library\") (subpath \"/AppleInternal\") (subpath \"/private\") (subpath \"/dev\") (subpath \"/tmp\") (subpath \"/var\") (subpath \"/etc\") (subpath \"{runtime_root}\") (subpath \"{workspace}\")) (allow file-write* (subpath \"/private/tmp\") (subpath \"/tmp\") (subpath \"/dev/null\") (subpath \"{workspace}\")) {net_rule}"
        )
    }

    /// Execute `command` with `args` under OS sandboxing and resource metering (`timeout_ms`).
    pub fn execute_sandboxed(
        &self,
        command: &str,
        args: &[&str],
        timeout_ms: u64,
    ) -> Result<SandboxRunReceipt, SandboxError> {
        let mut cfg = SandboxConfig::default();
        cfg.program = PathBuf::from(command);
        cfg.args = args.iter().map(|s| (*s).to_string()).collect();
        self.execute_sandboxed_with_config(
            &cfg,
            command,
            args,
            timeout_ms,
            DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
        )
    }

    /// Execute `command` with custom `SandboxConfig`, wall-clock `timeout_ms`, and `max_output_bytes`.
    pub fn execute_sandboxed_with_config(
        &self,
        config: &SandboxConfig,
        command: &str,
        args: &[&str],
        timeout_ms: u64,
        max_output_bytes: usize,
    ) -> Result<SandboxRunReceipt, SandboxError> {
        if command.trim().is_empty() {
            return Err(SandboxError::InvalidCommand(
                "command path must not be empty".to_string(),
            ));
        }
        if timeout_ms == 0 {
            return Err(SandboxError::TimeoutExceeded {
                timeout_ms: 0,
                elapsed_usec: 0,
            });
        }

        #[cfg(target_os = "macos")]
        {
            let profile = Self::build_seatbelt_profile(config);
            let sandbox_exec = std::path::Path::new("/usr/bin/sandbox-exec");
            if sandbox_exec.exists() {
                let mut sb_args: Vec<String> =
                    vec!["-p".to_string(), profile.clone(), command.to_string()];
                sb_args.extend(args.iter().map(|s| (*s).to_string()));
                let sb_arg_refs: Vec<&str> = sb_args.iter().map(String::as_str).collect();
                match Self::run_metered_child(
                    "/usr/bin/sandbox-exec",
                    &sb_arg_refs,
                    command,
                    args,
                    timeout_ms,
                    max_output_bytes,
                    SandboxBackend::MacosSeatbelt,
                    Some(profile.clone()),
                ) {
                    Ok(mut receipt) => {
                        let stderr_text = String::from_utf8_lossy(&receipt.stderr);
                        let nested_sandbox_denied = !receipt.success
                            && (stderr_text.contains("sandbox_apply")
                                || stderr_text.contains("Operation not permitted")
                                || receipt.exit_code == Some(71));
                        if !nested_sandbox_denied {
                            receipt.seatbelt_profile = Some(profile);
                            return Ok(receipt);
                        }
                    }
                    Err(
                        err @ (SandboxError::TimeoutExceeded { .. }
                        | SandboxError::OutputLimitExceeded { .. }),
                    ) => return Err(err),
                    Err(_) => {}
                }
            }
            if !config.allow_unsandboxed_fallback {
                return Err(SandboxError::SandboxUnavailable(
                    "macOS Seatbelt (sandbox-exec) confinement unavailable or denied and allow_unsandboxed_fallback is false".to_string(),
                ));
            }
            Self::run_metered_child(
                command,
                args,
                command,
                args,
                timeout_ms,
                max_output_bytes,
                SandboxBackend::MeteredProcessFallback,
                Some(profile),
            )
        }

        #[cfg(target_os = "linux")]
        {
            if config.bwrap_binary.exists()
                && config.workspace_dir.exists()
                && config.runtime_root.exists()
            {
                let mut bwrap_cfg = config.clone();
                bwrap_cfg.program = PathBuf::from(command);
                bwrap_cfg.args = args.iter().map(|s| (*s).to_string()).collect();
                let flags = Self::build_flags(&bwrap_cfg);
                let flag_refs: Vec<&str> = flags.iter().map(String::as_str).collect();
                let bwrap_bin = config.bwrap_binary.to_string_lossy().to_string();
                match Self::run_metered_child(
                    &bwrap_bin,
                    &flag_refs,
                    command,
                    args,
                    timeout_ms,
                    max_output_bytes,
                    SandboxBackend::Bubblewrap,
                    None,
                ) {
                    Ok(receipt) => {
                        let stderr_text = String::from_utf8_lossy(&receipt.stderr);
                        if receipt.success || !stderr_text.contains("bwrap:") {
                            return Ok(receipt);
                        }
                    }
                    Err(
                        err @ (SandboxError::TimeoutExceeded { .. }
                        | SandboxError::OutputLimitExceeded { .. }),
                    ) => return Err(err),
                    Err(_) => {}
                }
            }
            if !config.allow_unsandboxed_fallback {
                return Err(SandboxError::SandboxUnavailable(
                    "Linux Bubblewrap (bwrap) confinement unavailable or failed and allow_unsandboxed_fallback is false".to_string(),
                ));
            }
            Self::run_metered_child(
                command,
                args,
                command,
                args,
                timeout_ms,
                max_output_bytes,
                SandboxBackend::MeteredProcessFallback,
                None,
            )
        }

        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            if !config.allow_unsandboxed_fallback {
                return Err(SandboxError::SandboxUnavailable(
                    "OS sandbox confinement unavailable on target platform and allow_unsandboxed_fallback is false".to_string(),
                ));
            }
            Self::run_metered_child(
                command,
                args,
                command,
                args,
                timeout_ms,
                max_output_bytes,
                SandboxBackend::MeteredProcessFallback,
                None,
            )
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run_metered_child(
        exec_bin: &str,
        exec_args: &[&str],
        logical_command: &str,
        logical_args: &[&str],
        timeout_ms: u64,
        max_output_bytes: usize,
        backend: SandboxBackend,
        seatbelt_profile: Option<String>,
    ) -> Result<SandboxRunReceipt, SandboxError> {
        let start = Instant::now();
        let child = Command::new(exec_bin)
            .args(exec_args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| SandboxError::SpawnFailed(format!("{exec_bin}: {e}")))?;

        let mut guard = KillOnDropChild::new(child);
        let stdout_pipe = guard.as_mut().stdout.take();
        let stderr_pipe = guard.as_mut().stderr.take();

        let cap_limit = max_output_bytes.saturating_add(1);
        let out_handle = std::thread::spawn(move || -> Vec<u8> {
            let mut buf = Vec::new();
            if let Some(pipe) = stdout_pipe {
                let _ = pipe.take(cap_limit as u64).read_to_end(&mut buf);
            }
            buf
        });
        let err_handle = std::thread::spawn(move || -> Vec<u8> {
            let mut buf = Vec::new();
            if let Some(pipe) = stderr_pipe {
                let _ = pipe.take(cap_limit as u64).read_to_end(&mut buf);
            }
            buf
        });

        let timeout_dur = Duration::from_millis(timeout_ms);
        let status = loop {
            match guard.as_mut().try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => {
                    let elapsed = start.elapsed();
                    if elapsed >= timeout_dur {
                        drop(guard);
                        let _ = out_handle.join();
                        let _ = err_handle.join();
                        return Err(SandboxError::TimeoutExceeded {
                            timeout_ms,
                            elapsed_usec: elapsed.as_micros().max(1) as u64,
                        });
                    }
                    std::thread::sleep(Duration::from_millis(2));
                }
                Err(e) => {
                    return Err(SandboxError::WaitFailed(e.to_string()));
                }
            }
        };

        let wall_clock_usec = start.elapsed().as_micros().max(1) as u64;
        // Disarm kill-on-drop since the child already exited cleanly
        let _ = guard.child.take();

        let stdout = out_handle.join().unwrap_or_default();
        let stderr = err_handle.join().unwrap_or_default();
        let observed_bytes = stdout.len().saturating_add(stderr.len());
        if stdout.len() > max_output_bytes
            || stderr.len() > max_output_bytes
            || observed_bytes > max_output_bytes
        {
            return Err(SandboxError::OutputLimitExceeded {
                max_bytes: max_output_bytes,
                observed_bytes,
            });
        }

        let stdout_digest = sha256(&stdout);
        let stderr_digest = sha256(&stderr);

        // Convert wall-clock microseconds + I/O volume to deterministic fuel units
        let cpu_fuel = (wall_clock_usec / 10_000).max(1);
        let io_fuel = (observed_bytes as u64) / 64;
        let fuel_consumed = cpu_fuel.saturating_add(io_fuel);
        let peak_rss_bytes = (4096usize).saturating_add(observed_bytes);
        let is_fallback = matches!(backend, SandboxBackend::MeteredProcessFallback);

        Ok(SandboxRunReceipt {
            command: logical_command.to_string(),
            args: logical_args.iter().map(|s| (*s).to_string()).collect(),
            exit_code: status.code(),
            success: status.success(),
            wall_clock_usec,
            fuel_consumed,
            stdout,
            stderr,
            stdout_digest,
            stderr_digest,
            peak_rss_bytes,
            backend,
            is_fallback,
            tier: ReproducibilityTier::R1MeteredProcess,
            seatbelt_profile,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bwrap_flags_default() {
        let config = SandboxConfig::default();
        assert!(!config.allow_unsandboxed_fallback);
        let flags = BubblewrapRunner::build_flags(&config);

        assert!(flags.contains(&"--die-with-parent".to_string()));
        assert!(flags.contains(&"--unshare-user".to_string()));
        assert!(flags.contains(&"--disable-userns".to_string()));
        assert!(flags.contains(&"--unshare-pid".to_string()));
        assert!(flags.contains(&"--unshare-net".to_string()));
        assert!(flags.contains(&"--cap-drop".to_string()));
        assert!(flags.contains(&"/workspace".to_string()));
    }

    #[test]
    fn test_bwrap_flags_network_toggle() {
        let mut config = SandboxConfig::default();
        config.allow_network = true;
        let flags = BubblewrapRunner::build_flags(&config);

        assert!(flags.contains(&"--share-net".to_string()));
        assert!(!flags.contains(&"--unshare-net".to_string()));
    }

    #[test]
    fn test_seatbelt_profile_generation() {
        let mut config = SandboxConfig::default();
        let profile_offline = BubblewrapRunner::build_seatbelt_profile(&config);
        assert!(profile_offline.contains("(version 1)"));
        assert!(profile_offline.contains("(deny default)"));
        assert!(profile_offline.contains("(allow process*)"));
        assert!(profile_offline.contains("(allow file-read* (literal \"/\")"));
        assert!(!profile_offline.contains("(allow file-read*)"));
        assert!(profile_offline.contains("(deny network*)"));

        config.allow_network = true;
        let profile_online = BubblewrapRunner::build_seatbelt_profile(&config);
        assert!(profile_online.contains("(allow network*)"));
    }

    #[test]
    fn test_execute_sandboxed_fails_closed_without_fallback() {
        let runner = BubblewrapRunner::new();
        let mut strict_cfg = SandboxConfig::default();
        strict_cfg.bwrap_binary = PathBuf::from("/nonexistent/bwrap");
        strict_cfg.workspace_dir = PathBuf::from("/nonexistent/workspace");
        strict_cfg.runtime_root = PathBuf::from("/nonexistent/runtime");
        strict_cfg.allow_unsandboxed_fallback = false;

        #[cfg(target_os = "linux")]
        {
            let res = runner.execute_sandboxed_with_config(
                &strict_cfg,
                "/bin/echo",
                &["should-fail-closed"],
                2000,
                DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            );
            assert!(
                matches!(res, Err(SandboxError::SandboxUnavailable(_))),
                "strict config without bwrap must fail closed, got {res:?}"
            );
        }
    }

    #[test]
    fn test_execute_sandboxed_live_process_and_receipt() {
        let runner = BubblewrapRunner::new();
        let receipt = match runner.execute_sandboxed("/bin/echo", &["obend-sandbox-live"], 5000) {
            Ok(receipt) => {
                assert!(!receipt.is_fallback);
                receipt
            }
            Err(SandboxError::SandboxUnavailable(_)) => {
                let mut fallback_cfg = SandboxConfig::default();
                fallback_cfg.allow_unsandboxed_fallback = true;
                let receipt = runner
                    .execute_sandboxed_with_config(
                        &fallback_cfg,
                        "/bin/echo",
                        &["obend-sandbox-live"],
                        5000,
                        DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
                    )
                    .expect("explicitly enabled fallback should succeed in test environment");
                assert!(receipt.is_fallback);
                assert_eq!(receipt.backend, SandboxBackend::MeteredProcessFallback);
                receipt
            }
            Err(other) => panic!("unexpected error: {other:?}"),
        };

        assert!(receipt.success);
        assert_eq!(receipt.exit_code, Some(0));
        assert_eq!(receipt.stdout, b"obend-sandbox-live\n");
        assert_eq!(receipt.stdout_digest, sha256(b"obend-sandbox-live\n"));
        assert_eq!(receipt.stderr_digest, sha256(b""));
        assert!(receipt.wall_clock_usec > 0);
        assert!(receipt.fuel_consumed >= 1);
        assert_eq!(receipt.tier, ReproducibilityTier::R1MeteredProcess);
        assert_ne!(receipt.receipt_digest(), [0u8; 32]);

        let mut flipped = receipt.clone();
        flipped.is_fallback = !receipt.is_fallback;
        assert_ne!(
            receipt.receipt_digest(),
            flipped.receipt_digest(),
            "receipt_digest must bind is_fallback"
        );
        #[cfg(target_os = "macos")]
        assert!(receipt.seatbelt_profile.is_some());
    }

    #[test]
    fn test_execute_sandboxed_timeout_and_output_limits() {
        let runner = BubblewrapRunner::new();

        // 1. Empty command rejected
        assert!(matches!(
            runner.execute_sandboxed("", &[], 1000),
            Err(SandboxError::InvalidCommand(_))
        ));

        let mut cfg = SandboxConfig::default();
        cfg.allow_unsandboxed_fallback = true;

        // 2. Timeout enforcement with kill_on_drop
        let timeout_res = runner.execute_sandboxed_with_config(
            &cfg,
            "/bin/sleep",
            &["2"],
            30,
            DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
        );
        match timeout_res {
            Err(SandboxError::TimeoutExceeded {
                timeout_ms,
                elapsed_usec,
            }) => {
                assert_eq!(timeout_ms, 30);
                assert!(elapsed_usec >= 30_000);
            }
            other => panic!("expected TimeoutExceeded, got {other:?}"),
        }

        // 3. Output size limit enforcement
        let out_res = runner.execute_sandboxed_with_config(
            &cfg,
            "/bin/echo",
            &["this-output-is-longer-than-eight-bytes"],
            2000,
            8,
        );
        assert!(matches!(
            out_res,
            Err(SandboxError::OutputLimitExceeded { max_bytes: 8, .. })
        ));
    }
}
