use std::io::Read;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{Receiver, sync_channel};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::grain::{ReproducibilityTier, sha256};

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

impl SandboxBackend {
    pub fn tag_byte(&self) -> u8 {
        match self {
            Self::Bubblewrap => 1,
            Self::MacosSeatbelt => 2,
            Self::MeteredProcessFallback => 3,
        }
    }
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
    /// Compute a canonical length-framed SHA-256 commitment over the full process run receipt,
    /// including `command`, `args`, `backend`, `seatbelt_profile`, exit status, RSS, and I/O digests.
    pub fn receipt_digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(256);
        buf.extend_from_slice(b"OBEND-SANDBOX-RUN-RECEIPT-V2:");
        buf.extend_from_slice(&(self.command.len() as u64).to_be_bytes());
        buf.extend_from_slice(self.command.as_bytes());
        buf.extend_from_slice(&(self.args.len() as u64).to_be_bytes());
        for arg in &self.args {
            buf.extend_from_slice(&(arg.len() as u64).to_be_bytes());
            buf.extend_from_slice(arg.as_bytes());
        }
        buf.push(self.backend.tag_byte());
        match &self.seatbelt_profile {
            None => buf.push(0x00),
            Some(prof) => {
                buf.push(0x01);
                buf.extend_from_slice(&(prof.len() as u64).to_be_bytes());
                buf.extend_from_slice(prof.as_bytes());
            }
        }
        buf.push(u8::from(self.success));
        match self.exit_code {
            None => buf.push(0x00),
            Some(code) => {
                buf.push(0x01);
                buf.extend_from_slice(&code.to_be_bytes());
            }
        }
        buf.extend_from_slice(&self.wall_clock_usec.to_be_bytes());
        buf.extend_from_slice(&self.fuel_consumed.to_be_bytes());
        buf.extend_from_slice(&(self.peak_rss_bytes as u64).to_be_bytes());
        buf.extend_from_slice(&self.stdout_digest);
        buf.extend_from_slice(&self.stderr_digest);
        buf.push(self.tier.tag_byte());
        buf.push(u8::from(self.is_fallback));
        sha256(&buf)
    }
}

/// Guard that ensures a spawned child process (and its process group) is killed and reaped
/// exactly once if dropped before `wait4` reaps it.
struct KillOnDropChild {
    pid: libc::pid_t,
    reaped: bool,
    child: Child,
}

impl KillOnDropChild {
    fn new(child: Child) -> Self {
        let pid = child.id() as libc::pid_t;
        Self {
            pid,
            reaped: false,
            child,
        }
    }
}

impl Drop for KillOnDropChild {
    fn drop(&mut self) {
        if !self.reaped && self.pid > 0 {
            unsafe {
                let _ = libc::kill(-self.pid, libc::SIGKILL);
                let _ = libc::kill(self.pid, libc::SIGKILL);
                let mut status: libc::c_int = 0;
                let mut usage: libc::rusage = std::mem::zeroed();
                loop {
                    let rc = libc::wait4(self.pid, &mut status, 0, &mut usage);
                    if rc >= 0 {
                        break;
                    }
                    if std::io::Error::last_os_error().raw_os_error() != Some(libc::EINTR) {
                        break;
                    }
                }
            }
            self.reaped = true;
        }
    }
}

fn escape_sbpl_string(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 8);
    for ch in raw.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\0' => {}
            other => out.push(other),
        }
    }
    out
}

// A single deadline bounds both readers after the entire process group is killed.
fn drain_pipe_readers(
    out_done: &Receiver<()>,
    err_done: &Receiver<()>,
    deadline: Instant,
) -> Result<(), SandboxError> {
    for done in [out_done, err_done] {
        match done.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
            Ok(()) | Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {}
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                return Err(SandboxError::WaitFailed(
                    "output reader did not close after reap".into(),
                ));
            }
        }
    }

    Ok(())
}

fn spawn_bounded_pipe_reader<R: Read + Send + 'static>(
    pipe: Option<R>,
    cap_limit: usize,
) -> (Arc<Mutex<Vec<u8>>>, Receiver<()>) {
    let sink = Arc::new(Mutex::new(Vec::new()));
    let sink_clone = Arc::clone(&sink);
    let (done_tx, done_rx) = sync_channel(1);
    std::thread::spawn(move || {
        if let Some(mut reader) = pipe {
            let mut chunk = [0u8; 8192];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(n) => {
                        let mut guard = sink_clone
                            .lock()
                            .unwrap_or_else(|poisoned| poisoned.into_inner());
                        let rem = cap_limit.saturating_sub(guard.len());
                        let take_n = n.min(rem);
                        guard.extend_from_slice(&chunk[..take_n]);
                        if guard.len() >= cap_limit {
                            break;
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(_) => break,
                }
            }
        }
        let _ = done_tx.send(());
    });
    (sink, done_rx)
}

#[cfg(target_os = "linux")]
fn rusage_maxrss_to_bytes(ru_maxrss: libc::c_long) -> usize {
    (ru_maxrss.max(0) as usize).saturating_mul(1024)
}

#[cfg(target_os = "macos")]
fn rusage_maxrss_to_bytes(ru_maxrss: libc::c_long) -> usize {
    ru_maxrss.max(0) as usize
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn rusage_maxrss_to_bytes(ru_maxrss: libc::c_long) -> usize {
    (ru_maxrss.max(0) as usize).saturating_mul(1024)
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
    /// Escapes `\` before `"` so crafted workspace/runtime paths cannot break out of SBPL string literals.
    pub fn build_seatbelt_profile(config: &SandboxConfig) -> String {
        let workspace = escape_sbpl_string(&config.workspace_dir.to_string_lossy());
        let runtime_root = escape_sbpl_string(&config.runtime_root.to_string_lossy());
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
        let cfg = SandboxConfig {
            program: PathBuf::from(command),
            args: args.iter().map(|s| (*s).to_string()).collect(),
            ..SandboxConfig::default()
        };
        self.execute_sandboxed_with_config(
            &cfg,
            command,
            args,
            timeout_ms,
            DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
        )
    }

    /// Execute `command` with custom `SandboxConfig`, wall-clock `timeout_ms`, and `max_output_bytes`.
    ///
    /// Security invariant: once a sandboxed child (`sandbox-exec` or `bwrap`) has been invoked,
    /// its `stderr` content or exit code (`71`, `"Operation not permitted"`, `"bwrap:"`, etc.)
    /// MUST NEVER trigger a second unsandboxed execution on the host.
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
                let mut receipt = Self::run_metered_child(
                    "/usr/bin/sandbox-exec",
                    &sb_arg_refs,
                    command,
                    args,
                    timeout_ms,
                    max_output_bytes,
                    config.memory_max_mb,
                    SandboxBackend::MacosSeatbelt,
                    Some(profile.clone()),
                )?;
                receipt.seatbelt_profile = Some(profile);
                return Ok(receipt);
            }
            if !config.allow_unsandboxed_fallback {
                return Err(SandboxError::SandboxUnavailable(
                    "macOS Seatbelt (sandbox-exec) binary missing and allow_unsandboxed_fallback is false".to_string(),
                ));
            }
            Self::run_metered_child(
                command,
                args,
                command,
                args,
                timeout_ms,
                max_output_bytes,
                config.memory_max_mb,
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
                return Self::run_metered_child(
                    &bwrap_bin,
                    &flag_refs,
                    command,
                    args,
                    timeout_ms,
                    max_output_bytes,
                    config.memory_max_mb,
                    SandboxBackend::Bubblewrap,
                    None,
                );
            }
            if !config.allow_unsandboxed_fallback {
                return Err(SandboxError::SandboxUnavailable(
                    "Linux Bubblewrap (bwrap) confinement unavailable and allow_unsandboxed_fallback is false".to_string(),
                ));
            }
            Self::run_metered_child(
                command,
                args,
                command,
                args,
                timeout_ms,
                max_output_bytes,
                config.memory_max_mb,
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
                config.memory_max_mb,
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
        memory_max_mb: u32,
        backend: SandboxBackend,
        seatbelt_profile: Option<String>,
    ) -> Result<SandboxRunReceipt, SandboxError> {
        let start = Instant::now();
        let mem_limit_bytes = (memory_max_mb as u64).saturating_mul(1024 * 1024);

        let mut cmd = Command::new(exec_bin);
        cmd.args(exec_args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .process_group(0);

        if mem_limit_bytes > 0 {
            unsafe {
                cmd.pre_exec(move || {
                    let mut cur: libc::rlimit = std::mem::zeroed();
                    let limit_result = libc::getrlimit(libc::RLIMIT_AS, &mut cur);
                    #[cfg(target_os = "linux")]
                    if limit_result != 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    if limit_result == 0 {
                        let req = mem_limit_bytes as libc::rlim_t;
                        let capped = if cur.rlim_max == libc::RLIM_INFINITY {
                            req
                        } else {
                            req.min(cur.rlim_max)
                        };
                        let rlim = libc::rlimit {
                            rlim_cur: capped,
                            rlim_max: capped,
                        };
                        #[cfg(target_os = "linux")]
                        if libc::setrlimit(libc::RLIMIT_AS, &rlim) != 0 {
                            return Err(std::io::Error::last_os_error());
                        }
                        #[cfg(not(target_os = "linux"))]
                        {
                            let _ = libc::setrlimit(libc::RLIMIT_AS, &rlim);
                        }
                    }
                    Ok(())
                });
            }
        }

        let child = cmd
            .spawn()
            .map_err(|e| SandboxError::SpawnFailed(format!("{exec_bin}: {e}")))?;

        let mut guard = KillOnDropChild::new(child);
        let pid = guard.pid;
        let stdout_pipe = guard.child.stdout.take();
        let stderr_pipe = guard.child.stderr.take();

        let cap_limit = max_output_bytes.saturating_add(1);
        let (out_buf, out_done) = spawn_bounded_pipe_reader(stdout_pipe, cap_limit);
        let (err_buf, err_done) = spawn_bounded_pipe_reader(stderr_pipe, cap_limit);

        let timeout_dur = Duration::from_millis(timeout_ms);
        let (status, rusage): (std::process::ExitStatus, libc::rusage) = loop {
            let mut raw_status: libc::c_int = 0;
            let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
            let rc = unsafe { libc::wait4(pid, &mut raw_status, libc::WNOHANG, &mut usage) };
            if rc == pid {
                guard.reaped = true;
                unsafe {
                    libc::kill(-pid, libc::SIGKILL);
                }
                break (std::process::ExitStatus::from_raw(raw_status), usage);
            } else if rc == 0 {
                let elapsed = start.elapsed();
                if elapsed >= timeout_dur {
                    drop(guard);
                    return Err(SandboxError::TimeoutExceeded {
                        timeout_ms,
                        elapsed_usec: elapsed.as_micros().max(1) as u64,
                    });
                }
                std::thread::sleep(Duration::from_millis(2));
            } else {
                let err = std::io::Error::last_os_error();
                if err.raw_os_error() == Some(libc::EINTR) {
                    continue;
                }
                return Err(SandboxError::WaitFailed(err.to_string()));
            }
        };

        drain_pipe_readers(
            &out_done,
            &err_done,
            Instant::now() + Duration::from_secs(1),
        )?;

        let wall_clock_usec = start.elapsed().as_micros().max(1) as u64;

        let stdout = out_buf
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone();
        let stderr = err_buf
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone();
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
        let peak_rss_bytes = rusage_maxrss_to_bytes(rusage.ru_maxrss);
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
    fn post_reap_reader_timeout_fails_closed() {
        for stuck_stdout in [false, true] {
            let (out_tx, out_rx) = sync_channel(1);
            let (err_tx, err_rx) = sync_channel(1);
            if stuck_stdout {
                err_tx.send(()).unwrap();
            } else {
                out_tx.send(()).unwrap();
            }
            assert!(matches!(
                drain_pipe_readers(&out_rx, &err_rx, Instant::now() + Duration::from_millis(10)),
                Err(SandboxError::WaitFailed(_))
            ));
            drop((out_tx, err_tx));
            assert!(drain_pipe_readers(&out_rx, &err_rx, Instant::now()).is_ok());
        }
    }

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
        let config = SandboxConfig {
            allow_network: true,
            ..SandboxConfig::default()
        };
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
        let strict_cfg = SandboxConfig {
            bwrap_binary: PathBuf::from("/nonexistent/bwrap"),
            workspace_dir: PathBuf::from("/nonexistent/workspace"),
            runtime_root: PathBuf::from("/nonexistent/runtime"),
            allow_unsandboxed_fallback: false,
            ..SandboxConfig::default()
        };

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
        #[cfg(not(target_os = "linux"))]
        let _ = (&runner, &strict_cfg);
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
                let fallback_cfg = SandboxConfig {
                    allow_unsandboxed_fallback: true,
                    ..SandboxConfig::default()
                };
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

        let mut cmd_mutated = receipt.clone();
        cmd_mutated.command = "/bin/true".to_string();
        assert_ne!(
            receipt.receipt_digest(),
            cmd_mutated.receipt_digest(),
            "receipt_digest must bind command"
        );

        let mut args_mutated = receipt.clone();
        args_mutated.args.push("--extra".to_string());
        assert_ne!(
            receipt.receipt_digest(),
            args_mutated.receipt_digest(),
            "receipt_digest must bind args"
        );

        let mut backend_mutated = receipt.clone();
        backend_mutated.backend = if receipt.backend == SandboxBackend::Bubblewrap {
            SandboxBackend::MacosSeatbelt
        } else {
            SandboxBackend::Bubblewrap
        };
        assert_ne!(
            receipt.receipt_digest(),
            backend_mutated.receipt_digest(),
            "receipt_digest must bind backend"
        );
        assert!(
            receipt.peak_rss_bytes >= 64 * 1024,
            "peak_rss_bytes must reflect real kernel ru_maxrss, got {}",
            receipt.peak_rss_bytes
        );
        #[cfg(target_os = "macos")]
        assert!(receipt.seatbelt_profile.is_some());
    }

    #[test]
    fn test_sbpl_backslash_quote_injection_escaped() {
        let cfg = SandboxConfig {
            workspace_dir: PathBuf::from("/tmp/ws\\\") (allow file-write* (subpath \"/\")) ; "),
            ..SandboxConfig::default()
        };
        let profile = BubblewrapRunner::build_seatbelt_profile(&cfg);
        assert!(
            profile.contains("\\\\\\\")"),
            "backslash must be escaped before double-quote in SBPL: {profile}"
        );
        assert!(!profile.contains("(subpath \"/tmp/ws\\\")"));
    }

    #[test]
    fn test_stderr_spoofing_never_triggers_second_unsandboxed_run() {
        let runner = BubblewrapRunner::new();
        let tmp = std::env::temp_dir().join(format!("obend_stderr_spoof_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).unwrap();
        let marker = tmp.join("invocations.log");
        let fake_bwrap = tmp.join("fake_bwrap.sh");
        let ws = tmp.join("ws");
        let rt = tmp.join("rt");
        std::fs::create_dir_all(&ws).unwrap();
        std::fs::create_dir_all(&rt).unwrap();

        // Fake bwrap wrapper records each invocation and prints attacker-controlled stderr + exits 71
        let script = format!(
            "#!/bin/sh\necho invoked >> '{}'\necho 'bwrap: Operation not permitted sandbox_apply' >&2\nexit 71\n",
            marker.display()
        );
        std::fs::write(&fake_bwrap, script).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&fake_bwrap, std::fs::Permissions::from_mode(0o755)).unwrap();
        }

        let cfg = SandboxConfig {
            bwrap_binary: fake_bwrap,
            workspace_dir: ws,
            runtime_root: rt,
            allow_unsandboxed_fallback: true,
            ..SandboxConfig::default()
        };

        #[cfg(target_os = "linux")]
        {
            let receipt = runner
                .execute_sandboxed_with_config(
                    &cfg,
                    "/bin/sh",
                    &[
                        "-c",
                        &format!("echo HOST_FALLBACK >> '{}'", marker.display()),
                    ],
                    3000,
                    DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
                )
                .expect("sandbox wrapper ran once");
            assert_eq!(receipt.exit_code, Some(71));
            assert_eq!(receipt.backend, SandboxBackend::Bubblewrap);
            assert!(!receipt.is_fallback);
            let log = std::fs::read_to_string(&marker).unwrap_or_default();
            assert_eq!(
                log.lines().count(),
                1,
                "child stderr/exit-71 must NEVER trigger a second unsandboxed execution: {log}"
            );
            assert!(!log.contains("HOST_FALLBACK"));
        }
        #[cfg(not(target_os = "linux"))]
        let _ = (&runner, &cfg);
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_rlimit_as_enforced_and_background_pipe_descendant_bounded() {
        let runner = BubblewrapRunner::new();
        let cfg = SandboxConfig {
            allow_unsandboxed_fallback: true,
            ..SandboxConfig::default()
        };

        // 1. Background grandchild holding stdout pipe open must NOT hang past drain grace
        let t0 = Instant::now();
        let bg_receipt = runner
            .execute_sandboxed_with_config(
                &cfg,
                "/bin/sh",
                &["-c", "sleep 15 & echo parent-done"],
                2000,
                DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            )
            .expect("parent exits quickly while background sleep holds stdout");
        let bg_ms = t0.elapsed().as_millis();
        assert!(bg_receipt.success);
        assert_eq!(bg_receipt.stdout, b"parent-done\n");
        assert!(
            bg_ms < 1000,
            "bounded pipe reader must not wait 15s on background grandchild, took {bg_ms}ms"
        );

        // Descendants closing both pipes still belong to the killed process group.
        let detached = BubblewrapRunner::run_metered_child(
            "/bin/sh",
            &["-c", "sleep 3600 >/dev/null 2>&1 & echo $!"],
            "/bin/sh",
            &[],
            2000,
            DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            0,
            SandboxBackend::MeteredProcessFallback,
            None,
        )
        .unwrap();
        let child_pid: i32 = String::from_utf8(detached.stdout)
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        #[cfg(target_os = "linux")]
        {
            let deadline = Instant::now() + Duration::from_secs(1);
            loop {
                let stat = std::fs::read_to_string(format!("/proc/{child_pid}/stat"));
                if stat.as_ref().map_or(true, |s| {
                    s.split_once(") ")
                        .is_some_and(|(_, tail)| tail.starts_with('Z'))
                }) {
                    break;
                }
                assert!(
                    Instant::now() < deadline,
                    "background descendant survived reap"
                );
                std::thread::sleep(Duration::from_millis(10));
            }
        }
        #[cfg(not(target_os = "linux"))]
        let _ = child_pid;

        // 2. RLIMIT_AS enforcement on Linux: 32 MiB cap rejects 128 MiB allocation
        #[cfg(target_os = "linux")]
        if std::path::Path::new("/usr/bin/python3").exists() {
            let mut mem_cfg = cfg.clone();
            mem_cfg.memory_max_mb = 32;
            let oom_res = runner.execute_sandboxed_with_config(
                &mem_cfg,
                "/usr/bin/python3",
                &["-c", "x = bytearray(128 * 1024 * 1024)"],
                5000,
                DEFAULT_MAX_PROCESS_OUTPUT_BYTES,
            );
            if let Ok(r) = oom_res {
                assert!(
                    !r.success,
                    "128 MiB allocation under 32 MiB RLIMIT_AS must fail"
                );
            }
        }
    }

    #[test]
    fn test_execute_sandboxed_timeout_and_output_limits() {
        let runner = BubblewrapRunner::new();

        // 1. Empty command rejected
        assert!(matches!(
            runner.execute_sandboxed("", &[], 1000),
            Err(SandboxError::InvalidCommand(_))
        ));

        let cfg = SandboxConfig {
            allow_unsandboxed_fallback: true,
            ..SandboxConfig::default()
        };

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
