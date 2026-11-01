use std::path::PathBuf;
use std::process::Command;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SandboxConfig {
    pub bwrap_binary: PathBuf,
    pub workspace_dir: PathBuf,
    pub runtime_root: PathBuf,
    pub allow_network: bool,
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
            scratch_mib: Some(256),
            memory_max_mb: 2048,
            program: PathBuf::from("/agent/bin/obend"),
            args: Vec::new(),
        }
    }
}

pub struct BubblewrapRunner;

impl BubblewrapRunner {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bwrap_flags_default() {
        let config = SandboxConfig::default();
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
}
