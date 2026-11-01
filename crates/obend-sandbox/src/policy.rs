use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfinementPolicy {
    pub unshare_user: bool,
    pub unshare_pid: bool,
    pub unshare_ipc: bool,
    pub unshare_uts: bool,
    pub unshare_cgroup: bool,
    pub unshare_net: bool,
    pub drop_all_caps: bool,
    pub disable_userns: bool,
    pub die_with_parent: bool,
    pub new_session: bool,
    pub clearenv: bool,
    pub seccomp_filter: Option<PathBuf>,
}

impl ConfinementPolicy {
    pub fn strict() -> Self {
        Self {
            unshare_user: true,
            unshare_pid: true,
            unshare_ipc: true,
            unshare_uts: true,
            unshare_cgroup: true,
            unshare_net: true,
            drop_all_caps: true,
            disable_userns: true,
            die_with_parent: true,
            new_session: true,
            clearenv: true,
            seccomp_filter: None,
        }
    }

    pub fn to_bwrap_flags(&self) -> Vec<String> {
        let mut flags = Vec::new();
        if self.die_with_parent {
            flags.push("--die-with-parent".into());
        }
        if self.new_session {
            flags.push("--new-session".into());
        }
        if self.unshare_user {
            flags.push("--unshare-user".into());
        }
        if self.disable_userns {
            flags.push("--disable-userns".into());
        }
        if self.unshare_pid {
            flags.push("--unshare-pid".into());
        }
        if self.unshare_ipc {
            flags.push("--unshare-ipc".into());
        }
        if self.unshare_uts {
            flags.push("--unshare-uts".into());
        }
        if self.unshare_cgroup {
            flags.push("--unshare-cgroup".into());
        }
        if self.unshare_net {
            flags.push("--unshare-net".into());
        } else {
            flags.push("--share-net".into());
        }
        if self.drop_all_caps {
            flags.extend_from_slice(&["--cap-drop".into(), "ALL".into()]);
        }
        if self.clearenv {
            flags.push("--clearenv".into());
        }
        if let Some(ref sec) = self.seccomp_filter {
            flags.extend_from_slice(&["--seccomp".into(), sec.to_string_lossy().into()]);
        }
        flags
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strict_policy_flags() {
        let policy = ConfinementPolicy::strict();
        let flags = policy.to_bwrap_flags();

        assert!(flags.contains(&"--die-with-parent".to_string()));
        assert!(flags.contains(&"--unshare-net".to_string()));
        assert!(flags.contains(&"--cap-drop".to_string()));
        assert!(flags.contains(&"--disable-userns".to_string()));
    }
}
