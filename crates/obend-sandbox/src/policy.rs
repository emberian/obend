//! OS Confinement Policies: Bubblewrap namespace flags, strict explicit environment-variable
//! allowlists (`CAP-17`), default-deny seccomp-cBPF (`AF_UNIX` socket/connect filter), and
//! checked `SECCOMP_IOCTL_NOTIF_ADDFD` descriptor bounds.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

use crate::grain::sha256;

/// Environment variables that MUST NEVER be passed into or inherited by a confined child,
/// even if a caller attempts to list them in an allowlist (`CAP-17` dynamic-linker / shell startup defense).
pub const FORBIDDEN_ENV_KEYS: &[&str] = &[
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "LD_AUDIT",
    "LD_DEBUG",
    "LD_PROFILE",
    "LD_ORIGIN_PATH",
    "LD_USE_LOAD_BIAS",
    "LD_DYNAMIC_WEAK",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_LIBRARY_PATH",
    "DYLD_FRAMEWORK_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH",
    "DYLD_FALLBACK_FRAMEWORK_PATH",
    "DYLD_IMAGE_SUFFIX",
    "BASH_ENV",
    "ENV",
    "CDPATH",
    "IFS",
    "PROMPT_COMMAND",
    "PYTHONPATH",
    "PYTHONSTARTUP",
    "NODE_OPTIONS",
    "RUBYOPT",
    "PERL5OPT",
    "JAVA_TOOL_OPTIONS",
];

/// Errors raised when validating or resolving a sandbox environment allowlist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnvPolicyError {
    EmptyKey,
    MalformedKey(String),
    NulInValue { key: String },
    ForbiddenKey(String),
}

impl fmt::Display for EnvPolicyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyKey => write!(f, "environment variable key must not be empty"),
            Self::MalformedKey(k) => write!(
                f,
                "environment variable key '{k}' must match [A-Za-z_][A-Za-z0-9_]* without '=' or NUL"
            ),
            Self::NulInValue { key } => {
                write!(f, "environment variable '{key}' value contains forbidden NUL byte")
            }
            Self::ForbiddenKey(k) => {
                write!(f, "environment variable '{k}' is forbidden by confinement policy")
            }
        }
    }
}

impl std::error::Error for EnvPolicyError {}

fn validate_env_key(key: &str) -> Result<(), EnvPolicyError> {
    if key.is_empty() {
        return Err(EnvPolicyError::EmptyKey);
    }
    let mut chars = key.chars();
    let first = chars.next().unwrap();
    if !(first.is_ascii_alphabetic() || first == '_')
        || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err(EnvPolicyError::MalformedKey(key.to_string()));
    }
    if FORBIDDEN_ENV_KEYS
        .iter()
        .any(|bad| bad.eq_ignore_ascii_case(key))
        || key.to_ascii_uppercase().starts_with("LD_")
        || key.to_ascii_uppercase().starts_with("DYLD_")
    {
        return Err(EnvPolicyError::ForbiddenKey(key.to_string()));
    }
    Ok(())
}

/// Strict explicit environment-variable allowlist policy (`CAP-17` remediation).
///
/// By default (`EnvAllowlistPolicy::strict()`), **zero** parent environment variables are
/// inherited; the child receives only deterministic baseline variables (`HOME`, `PATH`, `LC_ALL`)
/// plus any validated `explicit_vars` and values of explicitly named `passthrough_keys`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvAllowlistPolicy {
    /// Deterministic `(key, value)` pairs injected into the child environment.
    pub explicit_vars: Vec<(String, String)>,
    /// Parent environment variable names explicitly permitted to pass through if set in the host.
    /// Empty by default so host credentials (`AWS_*`, `OPENAI_*`, `GITHUB_TOKEN`, etc.) never leak.
    pub passthrough_keys: Vec<String>,
}

impl Default for EnvAllowlistPolicy {
    fn default() -> Self {
        Self::strict()
    }
}

impl EnvAllowlistPolicy {
    /// Default-deny parent environment policy: scrubs 100% of host environment variables and sets
    /// only fixed confined `HOME`, `PATH`, and `LC_ALL`.
    pub fn strict() -> Self {
        Self {
            explicit_vars: vec![
                ("HOME".into(), "/workspace".into()),
                ("PATH".into(), "/usr/bin:/bin:/agent/bin".into()),
                ("LC_ALL".into(), "C".into()),
            ],
            passthrough_keys: Vec::new(),
        }
    }

    /// Add an explicit `(key, value)` environment variable to the child allowlist.
    pub fn with_explicit_var(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.explicit_vars.push((key.into(), value.into()));
        self
    }

    /// Explicitly allow a named parent environment variable to pass into the sandbox if present.
    pub fn with_passthrough_key(mut self, key: impl Into<String>) -> Self {
        self.passthrough_keys.push(key.into());
        self
    }

    /// Validate all configured keys/values and scrub `parent_env` down to the exact allowed map.
    /// Explicit variables override passthrough variables of the same name.
    pub fn validate_and_resolve<I>(&self, parent_env: I) -> Result<BTreeMap<String, String>, EnvPolicyError>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let mut allowed_passthrough = BTreeSet::new();
        for key in &self.passthrough_keys {
            validate_env_key(key)?;
            allowed_passthrough.insert(key.as_str());
        }
        for (key, val) in &self.explicit_vars {
            validate_env_key(key)?;
            if val.contains('\0') {
                return Err(EnvPolicyError::NulInValue { key: key.clone() });
            }
        }

        let mut out = BTreeMap::new();
        for (k, v) in parent_env {
            if allowed_passthrough.contains(k.as_str()) {
                if v.contains('\0') {
                    return Err(EnvPolicyError::NulInValue { key: k });
                }
                out.insert(k, v);
            }
        }
        for (k, v) in &self.explicit_vars {
            out.insert(k.clone(), v.clone());
        }
        Ok(out)
    }

    /// Compute a canonical length-framed SHA-256 commitment over a resolved environment map.
    pub fn digest_resolved(env: &BTreeMap<String, String>) -> [u8; 32] {
        let mut buf = Vec::with_capacity(128);
        buf.extend_from_slice(b"OBEND-SANDBOX-ENV-V1:");
        buf.extend_from_slice(&(env.len() as u64).to_be_bytes());
        for (k, v) in env {
            buf.extend_from_slice(&(k.len() as u64).to_be_bytes());
            buf.extend_from_slice(k.as_bytes());
            buf.extend_from_slice(&(v.len() as u64).to_be_bytes());
            buf.extend_from_slice(v.as_bytes());
        }
        sha256(&buf)
    }
}

// =========================================================================
// Seccomp-cBPF Default-Deny & `AF_UNIX` Socket/Connect Filter (`CAP-17`)
// =========================================================================

pub const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;
pub const AUDIT_ARCH_AARCH64: u32 = 0xC000_00B7;

/// Linux `AF_UNIX` (`AF_LOCAL`) address family constant (`1`).
pub const LINUX_AF_UNIX: u32 = 1;
/// Linux `AF_INET` address family constant (`2`).
pub const LINUX_AF_INET: u32 = 2;
/// Linux `SOCK_STREAM` socket type (`1`), plus `SOCK_NONBLOCK` (`0o4000`) / `SOCK_CLOEXEC` (`0o2000000`).
pub const LINUX_SOCK_STREAM: u32 = 1;
pub const LINUX_SOCK_NONBLOCK: u32 = 0x800;
pub const LINUX_SOCK_CLOEXEC: u32 = 0x80000;

/// Seccomp cBPF return action constants.
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
pub const SECCOMP_RET_ERRNO_EPERM: u32 = 0x0005_0000 | 1;
pub const SECCOMP_RET_USER_NOTIF: u32 = 0x7fc0_0000;
pub const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;

/// Egress door mode selected from the granted outbound endpoint list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DoorMode {
    /// Zero network grants: empty network namespace + seccomp denies `socket` and `connect`.
    Sealed,
    /// Supervised outbound connect-notify door: allows `socket(AF_INET, ...)` only (blocking
    /// `AF_UNIX`, `AF_INET6`, `AF_NETLINK`, `AF_PACKET`), traps `connect` to `USER_NOTIF`,
    /// and restricts `sendto` to `NULL` `dest_addr` (`args[4] == 0`).
    ProviderNotify,
}

pub fn door_mode(egress_endpoints: &[String]) -> DoorMode {
    if egress_endpoints.is_empty() {
        DoorMode::Sealed
    } else {
        DoorMode::ProviderNotify
    }
}

/// Parsed outbound endpoint grant (`"host:port"`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllowedEndpoint {
    V4([u8; 4], u16),
    Host(String, u16),
}

fn parse_ipv4(host: &str) -> Option<[u8; 4]> {
    let mut out = [0u8; 4];
    let mut count = 0usize;
    for (idx, part) in host.split('.').enumerate() {
        if idx >= 4 || part.is_empty() {
            return None;
        }
        out[idx] = part.parse::<u8>().ok()?;
        count += 1;
    }
    (count == 4).then_some(out)
}

/// Parse a `"host:port"` grant into an [`AllowedEndpoint`]. Malformed strings return `None`
/// (never a wildcard).
pub fn parse_egress_grant(raw: &str) -> Option<AllowedEndpoint> {
    let (host, port_str) = raw.rsplit_once(':')?;
    if host.is_empty() || host.contains(['\0', ' ', '\t', '\r', '\n', '/']) {
        return None;
    }
    let port = port_str.parse::<u16>().ok()?;
    if port == 0 {
        return None;
    }
    if host == "localhost" {
        return Some(AllowedEndpoint::V4([127, 0, 0, 1], port));
    }
    if let Some(v4) = parse_ipv4(host) {
        return Some(AllowedEndpoint::V4(v4, port));
    }
    Some(AllowedEndpoint::Host(host.to_string(), port))
}

pub fn expand_static_grants(grants: &[String]) -> Vec<AllowedEndpoint> {
    grants.iter().filter_map(|s| parse_egress_grant(s)).collect()
}

/// Exact-match admission check for a supervised `AF_INET` `connect(2)` target.
pub fn admits_ipv4_endpoint(allowed_v4: &[([u8; 4], u16)], ip: [u8; 4], port: u16) -> bool {
    allowed_v4.iter().any(|&(a_ip, a_port)| a_ip == ip && a_port == port)
}

/// Reason a trapped `connect(2)` `sockaddr` buffer was rejected by the supervisor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConnectFilterError {
    TruncatedSockaddr { len: usize },
    AfUnixForbidden,
    UnsupportedAddressFamily(u16),
    EndpointNotGranted { ip: [u8; 4], port: u16 },
}

impl fmt::Display for ConnectFilterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TruncatedSockaddr { len } => {
                write!(f, "sockaddr length {len} shorter than sockaddr_in (16 bytes)")
            }
            Self::AfUnixForbidden => {
                write!(f, "AF_UNIX connect is strictly forbidden by confinement policy")
            }
            Self::UnsupportedAddressFamily(fam) => {
                write!(f, "connect address family {fam} not permitted (only AF_INET allowed)")
            }
            Self::EndpointNotGranted { ip, port } => write!(
                f,
                "connect target {}.{}.{}.{}:{port} is not in granted egress allowlist",
                ip[0], ip[1], ip[2], ip[3]
            ),
        }
    }
}

impl std::error::Error for ConnectFilterError {}

/// Validate a raw `sockaddr` buffer read from a trapped `connect(2)` call.
/// Explicitly rejects `AF_UNIX` (`1`) even if shorter or padded, any non-`AF_INET` family,
/// and any `(ip, port)` outside `allowed_v4`.
pub fn validate_connect_sockaddr(
    sockaddr_bytes: &[u8],
    declared_addrlen: usize,
    allowed_v4: &[([u8; 4], u16)],
) -> Result<([u8; 4], u16), ConnectFilterError> {
    if sockaddr_bytes.len() >= 2 && declared_addrlen >= 2 {
        let family = u16::from_ne_bytes([sockaddr_bytes[0], sockaddr_bytes[1]]);
        if family == LINUX_AF_UNIX as u16 {
            return Err(ConnectFilterError::AfUnixForbidden);
        }
        if family != LINUX_AF_INET as u16 {
            return Err(ConnectFilterError::UnsupportedAddressFamily(family));
        }
    }
    if declared_addrlen < 16 || sockaddr_bytes.len() < 16 {
        return Err(ConnectFilterError::TruncatedSockaddr {
            len: declared_addrlen.min(sockaddr_bytes.len()),
        });
    }
    let port = u16::from_be_bytes([sockaddr_bytes[2], sockaddr_bytes[3]]);
    let ip = [
        sockaddr_bytes[4],
        sockaddr_bytes[5],
        sockaddr_bytes[6],
        sockaddr_bytes[7],
    ];
    if !admits_ipv4_endpoint(allowed_v4, ip, port) {
        return Err(ConnectFilterError::EndpointNotGranted { ip, port });
    }
    Ok((ip, port))
}

/// Classic BPF instruction (`struct sock_filter`, 8 bytes little-endian).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BpfInsn {
    pub code: u16,
    pub jt: u8,
    pub jf: u8,
    pub k: u32,
}

impl BpfInsn {
    pub fn to_le_bytes(self) -> [u8; 8] {
        let mut out = [0u8; 8];
        out[0..2].copy_from_slice(&self.code.to_le_bytes());
        out[2] = self.jt;
        out[3] = self.jf;
        out[4..8].copy_from_slice(&self.k.to_le_bytes());
        out
    }
}

/// Serialize a cBPF instruction slice into raw `struct sock_filter[]` bytes suitable for
/// `bwrap --seccomp <fd>`.
pub fn serialize_bpf_program(prog: &[BpfInsn]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(prog.len() * 8);
    for insn in prog {
        bytes.extend_from_slice(&insn.to_le_bytes());
    }
    bytes
}

const BPF_LD_W_ABS: u16 = 0x20;
const BPF_ALU_AND_K: u16 = 0x54;
const BPF_JMP_JEQ_K: u16 = 0x15;
const BPF_RET_K: u16 = 0x06;
const OFF_NR: u32 = 0;
const OFF_ARCH: u32 = 4;

const fn arg_lo(i: u32) -> u32 {
    16 + 8 * i
}
const fn arg_hi(i: u32) -> u32 {
    20 + 8 * i
}

/// Exact 64-bit syscall argument allow rule (`args[arg] == value`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArgAllow {
    pub nr: i64,
    pub arg: u32,
    pub value: u64,
}

/// Architecture-specific Linux syscall numbers used to synthesize the default-deny cBPF filter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeccompProfileSpec {
    pub arch: u32,
    pub unconditional_allows: Vec<i64>,
    pub socket_nr: i64,
    pub connect_nr: i64,
    pub sendto_nr: i64,
    pub ioctl_nr: i64,
    pub fionbio_req: u64,
}

impl SeccompProfileSpec {
    /// Canonical Linux `x86_64` minimal compute + supervised-egress syscall numbers.
    pub fn linux_x86_64() -> Self {
        Self {
            arch: AUDIT_ARCH_X86_64,
            unconditional_allows: vec![
                0,   // read
                1,   // write
                3,   // close
                9,   // mmap
                10,  // mprotect
                11,  // munmap
                12,  // brk
                13,  // rt_sigaction
                14,  // rt_sigprocmask
                15,  // rt_sigreturn
                24,  // sched_yield
                28,  // madvise
                35,  // nanosleep
                39,  // getpid
                45,  // recvfrom
                47,  // recvmsg
                48,  // shutdown
                51,  // getsockname
                52,  // getpeername
                54,  // setsockopt
                55,  // getsockopt
                60,  // exit
                72,  // fcntl
                131, // sigaltstack
                186, // gettid
                202, // futex
                230, // clock_nanosleep
                231, // exit_group
                232, // epoll_wait
                233, // epoll_ctl
                270, // pselect6
                271, // ppoll
                291, // epoll_create1
                318, // getrandom
            ],
            socket_nr: 41,
            connect_nr: 42,
            sendto_nr: 44,
            ioctl_nr: 16,
            fionbio_req: 0x5421,
        }
    }

    /// Canonical Linux `aarch64` minimal compute + supervised-egress syscall numbers.
    pub fn linux_aarch64() -> Self {
        Self {
            arch: AUDIT_ARCH_AARCH64,
            unconditional_allows: vec![
                63,  // read
                64,  // write
                57,  // close
                222, // mmap
                226, // mprotect
                215, // munmap
                214, // brk
                134, // rt_sigaction
                135, // rt_sigprocmask
                139, // rt_sigreturn
                124, // sched_yield
                233, // madvise
                101, // nanosleep
                172, // getpid
                207, // recvfrom
                212, // recvmsg
                210, // shutdown
                204, // getsockname
                205, // getpeername
                208, // setsockopt
                209, // getsockopt
                93,  // exit
                25,  // fcntl
                132, // sigaltstack
                178, // gettid
                98,  // futex
                115, // clock_nanosleep
                94,  // exit_group
                22,  // epoll_pwait
                21,  // epoll_ctl
                72,  // pselect6
                73,  // ppoll
                20,  // epoll_create1
                278, // getrandom
            ],
            socket_nr: 198,
            connect_nr: 203,
            sendto_nr: 206,
            ioctl_nr: 29,
            fionbio_req: 0x5421,
        }
    }
}

fn bpf_jump(from: usize, to: usize) -> u8 {
    u8::try_from(to - from - 1).expect("seccomp cBPF jump offset exceeds 255 instructions")
}

/// Build the hardened default-deny seccomp-cBPF filter (`CAP-17` fix):
/// - Kills the process on any foreign `AUDIT_ARCH` (`SECCOMP_RET_KILL_PROCESS`).
/// - Allows `sendto` ONLY when `args[4] == 0` (64-bit `NULL` `dest_addr`, permitting `send()` on
///   pre-connected sockets while blocking unconnected `AF_UNIX` datagram `sendto` exfiltration!).
/// - In `DoorMode::Sealed`: denies `socket`, `connect`, `sendmsg`, `openat`, `execve`, etc. with `EPERM`.
/// - In `DoorMode::ProviderNotify`:
///   - Admits `socket` ONLY when `args[0] == AF_INET` (`2`, full 64-bit check) AND
///     `(args[1] & !(SOCK_NONBLOCK | SOCK_CLOEXEC)) == SOCK_STREAM` (`1`) — blocking `AF_UNIX` (`1`),
///     `AF_INET6`, `AF_NETLINK`, `AF_PACKET`, `SOCK_DGRAM`, and `SOCK_RAW` directly in kernel BPF!
///   - Routes `connect` to `SECCOMP_RET_USER_NOTIF` (or `SECCOMP_RET_ERRNO_EPERM` when `notify_connect` is `false`).
///   - Admits `ioctl` ONLY for `args[1] == FIONBIO` (full 64-bit check).
pub fn build_hardened_seccomp_bpf(
    spec: &SeccompProfileSpec,
    mode: DoorMode,
    notify_connect: bool,
) -> Vec<BpfInsn> {
    let ld = |k: u32| BpfInsn {
        code: BPF_LD_W_ABS,
        jt: 0,
        jf: 0,
        k,
    };
    let and_k = |k: u32| BpfInsn {
        code: BPF_ALU_AND_K,
        jt: 0,
        jf: 0,
        k,
    };
    let jeq = |k: u32, jt: u8, jf: u8| BpfInsn {
        code: BPF_JMP_JEQ_K,
        jt,
        jf,
        k,
    };
    let ret = |k: u32| BpfInsn {
        code: BPF_RET_K,
        jt: 0,
        jf: 0,
        k,
    };

    // Symbolic builder: emit placeholder jumps to terminal labels, then patch exact offsets.
    #[derive(Clone, Copy)]
    enum Op {
        Raw(BpfInsn),
        JeqAllow(u32),
        JeqNotify(u32),
        JeqDeny(u32),
        JneKill(u32),
    }

    let mut ops: Vec<Op> = Vec::with_capacity(64);
    // [0..1] Arch pin
    ops.push(Op::Raw(ld(OFF_ARCH)));
    ops.push(Op::JneKill(spec.arch));
    // [2] Load syscall number
    ops.push(Op::Raw(ld(OFF_NR)));

    for &nr in &spec.unconditional_allows {
        ops.push(Op::JeqAllow(nr as u32));
    }

    // `sendto`: admit ONLY when `args[4]` (`dest_addr`) == 0 (full 64-bit NULL check).
    //   +0: jeq(sendto_nr, jt=0 (-> +1), jf=5 (-> +6, where A still holds `nr`))
    //   +1: ld(arg_lo(4))
    //   +2: jeq(0, jt=0 (-> +3), jf=2 (-> +5: EPERM))
    //   +3: ld(arg_hi(4))
    //   +4: JeqAllow(0) (jt -> ALLOW, jf=0 -> +5: EPERM)
    //   +5: ret(SECCOMP_RET_ERRNO_EPERM)
    ops.push(Op::Raw(jeq(spec.sendto_nr as u32, 0, 5)));
    ops.push(Op::Raw(ld(arg_lo(4))));
    ops.push(Op::Raw(jeq(0, 0, 2)));
    ops.push(Op::Raw(ld(arg_hi(4))));
    ops.push(Op::JeqAllow(0));
    ops.push(Op::Raw(ret(SECCOMP_RET_ERRNO_EPERM)));

    if mode == DoorMode::ProviderNotify {
        // `socket(domain, type, protocol)`:
        // Require `domain == AF_INET (2)` (64-bit) AND `(type & !(SOCK_NONBLOCK | SOCK_CLOEXEC)) == SOCK_STREAM (1)` (64-bit).
        // `AF_UNIX (1)`, `AF_INET6 (10)`, `SOCK_DGRAM (2)`, `SOCK_RAW (3)` all hit `+9: ret(EPERM)`!
        // Verify offsets:
        //   +0: jeq(socket_nr, jt=0 (-> +1), jf=9 (-> +10, A is still `nr`!))
        //   +1: ld(arg_lo(0))
        //   +2: jeq(LINUX_AF_INET, jt=0 (-> +3), jf=6 (-> +9))
        //   +3: ld(arg_hi(0))
        //   +4: jeq(0, jt=0 (-> +5), jf=4 (-> +9))
        //   +5: ld(arg_hi(1))
        //   +6: jeq(0, jt=0 (-> +7), jf=2 (-> +9))
        //   +7: ld(arg_lo(1))
        //   +8: and_k(!(LINUX_SOCK_NONBLOCK | LINUX_SOCK_CLOEXEC))
        //   +9: JeqAllow(LINUX_SOCK_STREAM) (jt -> ALLOW, jf=0 -> +10: ret(EPERM))
        //   +10: ret(SECCOMP_RET_ERRNO_EPERM)
        // Wait: if +10 is `ret(EPERM)`, then `+0`'s `jf` must jump OVER `+10` to `+11`, so `jf = 10` (`11 - 0 - 1 = 10`),
        // and `+2`'s `jf` to `+10` is `10 - 2 - 1 = 7`, `+4`'s `jf` is `10 - 4 - 1 = 5`, `+6`'s `jf` is `10 - 6 - 1 = 3`!
        let type_mask = !(LINUX_SOCK_NONBLOCK | LINUX_SOCK_CLOEXEC);
        ops.push(Op::Raw(jeq(spec.socket_nr as u32, 0, 10))); // +0 -> jf lands at +11
        ops.push(Op::Raw(ld(arg_lo(0)))); // +1
        ops.push(Op::Raw(jeq(LINUX_AF_INET, 0, 7))); // +2 -> jf lands at +10
        ops.push(Op::Raw(ld(arg_hi(0)))); // +3
        ops.push(Op::Raw(jeq(0, 0, 5))); // +4 -> jf lands at +10
        ops.push(Op::Raw(ld(arg_hi(1)))); // +5
        ops.push(Op::Raw(jeq(0, 0, 3))); // +6 -> jf lands at +10
        ops.push(Op::Raw(ld(arg_lo(1)))); // +7
        ops.push(Op::Raw(and_k(type_mask))); // +8
        ops.push(Op::JeqAllow(LINUX_SOCK_STREAM)); // +9 -> jf=0 lands at +10
        ops.push(Op::Raw(ret(SECCOMP_RET_ERRNO_EPERM))); // +10

        // `connect`: trap to supervisor `USER_NOTIF` (or `EPERM` if unsupervised).
        if notify_connect {
            ops.push(Op::JeqNotify(spec.connect_nr as u32));
        } else {
            ops.push(Op::JeqDeny(spec.connect_nr as u32));
        }

        // `ioctl`: admit ONLY `args[1] == FIONBIO` (full 64-bit check).
        //   +0: jeq(ioctl_nr, jt=0 (-> +1), jf=5 (-> +6))
        //   +1: ld(arg_lo(1))
        //   +2: jeq(fionbio_lo, jt=0 (-> +3), jf=2 (-> +5))
        //   +3: ld(arg_hi(1))
        //   +4: JeqAllow(fionbio_hi) (jt -> ALLOW, jf=0 -> +5)
        //   +5: ret(EPERM)
        ops.push(Op::Raw(jeq(spec.ioctl_nr as u32, 0, 5)));
        ops.push(Op::Raw(ld(arg_lo(1))));
        ops.push(Op::Raw(jeq(spec.fionbio_req as u32, 0, 2)));
        ops.push(Op::Raw(ld(arg_hi(1))));
        ops.push(Op::JeqAllow((spec.fionbio_req >> 32) as u32));
        ops.push(Op::Raw(ret(SECCOMP_RET_ERRNO_EPERM)));
    }

    let deny_idx = ops.len();
    let allow_idx = deny_idx + 1;
    let notify_idx = allow_idx + 1;
    let kill_idx = notify_idx + 1;

    let mut prog = Vec::with_capacity(kill_idx + 1);
    for (idx, op) in ops.into_iter().enumerate() {
        let insn = match op {
            Op::Raw(i) => i,
            Op::JeqAllow(k) => jeq(k, bpf_jump(idx, allow_idx), 0),
            Op::JeqNotify(k) => jeq(k, bpf_jump(idx, notify_idx), 0),
            Op::JeqDeny(k) => jeq(k, bpf_jump(idx, deny_idx), 0),
            Op::JneKill(k) => jeq(k, 0, bpf_jump(idx, kill_idx)),
        };
        prog.push(insn);
    }
    prog.push(ret(SECCOMP_RET_ERRNO_EPERM));
    prog.push(ret(SECCOMP_RET_ALLOW));
    prog.push(ret(SECCOMP_RET_USER_NOTIF));
    prog.push(ret(SECCOMP_RET_KILL_PROCESS));
    debug_assert_eq!(prog.len(), kill_idx + 1);
    prog
}

/// Pure-Rust cBPF evaluator over `seccomp_data` `(nr, arch, args)` for deterministic verification
/// of generated seccomp profiles on any host architecture.
pub fn eval_seccomp_bpf(prog: &[BpfInsn], arch: u32, nr: i64, args: [u64; 6]) -> u32 {
    let load_word = |off: u32| -> u32 {
        match off {
            0 => nr as u32,
            4 => arch,
            o if (16..64).contains(&o) && o.is_multiple_of(4) => {
                let arg = args[((o - 16) / 8) as usize];
                if (o - 16).is_multiple_of(8) {
                    arg as u32
                } else {
                    (arg >> 32) as u32
                }
            }
            other => panic!("invalid seccomp_data load offset {other}"),
        }
    };
    let mut pc = 0usize;
    let mut acc = 0u32;
    let mut steps = 0usize;
    while pc < prog.len() && steps <= 4096 {
        steps += 1;
        let insn = prog[pc];
        match insn.code {
            BPF_LD_W_ABS => {
                acc = load_word(insn.k);
                pc += 1;
            }
            BPF_ALU_AND_K => {
                acc &= insn.k;
                pc += 1;
            }
            BPF_JMP_JEQ_K => {
                let hop = if acc == insn.k { insn.jt } else { insn.jf } as usize;
                pc += 1 + hop;
            }
            BPF_RET_K => return insn.k,
            other => panic!("unsupported seccomp cBPF opcode {other:#x}"),
        }
    }
    SECCOMP_RET_KILL_PROCESS
}

// =========================================================================
// Checked `SECCOMP_IOCTL_NOTIF_ADDFD` Bounds (`CAP-17`)
// =========================================================================

/// Default maximum target descriptor index a seccomp supervisor may inject via `ADDFD`.
pub const DEFAULT_MAX_ADDFD_TARGET: u32 = 1024;

/// Validated `SECCOMP_IOCTL_NOTIF_ADDFD` injection specification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedAddFdSpec {
    pub src_fd: u32,
    pub target_fd: u32,
    pub newfd_flags: u32,
}

/// Refusal reasons when validating a `SECCOMP_IOCTL_NOTIF_ADDFD` descriptor injection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AddFdError {
    InvalidSourceFd(i32),
    ReservedStdStreamFd(u64),
    TargetFdOutOfBounds { requested: u64, max_bound: u32 },
    ProtectedEndpointFdCollision(i32),
}

impl fmt::Display for AddFdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSourceFd(fd) => write!(f, "invalid supervisor source fd {fd}"),
            Self::ReservedStdStreamFd(fd) => {
                write!(f, "refusing ADDFD overwrite of reserved std stream fd {fd}")
            }
            Self::TargetFdOutOfBounds {
                requested,
                max_bound,
            } => write!(
                f,
                "ADDFD target fd {requested} exceeds allowed descriptor bound {max_bound}"
            ),
            Self::ProtectedEndpointFdCollision(fd) => {
                write!(f, "refusing ADDFD overwrite of protected IPC endpoint fd {fd}")
            }
        }
    }
}

impl std::error::Error for AddFdError {}

impl CheckedAddFdSpec {
    /// Validate `notif.data.args[0]` (`raw_target_fd`) and `src_fd` BEFORE issuing
    /// `SECCOMP_IOCTL_NOTIF_ADDFD`:
    /// - Rejects negative `src_fd`.
    /// - Rejects `0..=2` (`stdin`/`stdout`/`stderr`).
    /// - Rejects 64-bit high-word smuggling (`raw_target_fd > max_fd_bound` or `> i32::MAX`).
    /// - Rejects collisions with `protected_fds` (e.g., the grain's `LineChannel` control socket).
    /// - Always stamps `O_CLOEXEC` on the injected descriptor.
    pub fn validate(
        raw_target_fd: u64,
        src_fd: i32,
        protected_fds: &[i32],
        max_fd_bound: u32,
    ) -> Result<Self, AddFdError> {
        if src_fd < 0 {
            return Err(AddFdError::InvalidSourceFd(src_fd));
        }
        if raw_target_fd < 3 {
            return Err(AddFdError::ReservedStdStreamFd(raw_target_fd));
        }
        let capped_max = max_fd_bound.min(i32::MAX as u32);
        if raw_target_fd > u64::from(capped_max) {
            return Err(AddFdError::TargetFdOutOfBounds {
                requested: raw_target_fd,
                max_bound: capped_max,
            });
        }
        let target_i32 = raw_target_fd as i32;
        if protected_fds.contains(&target_i32) {
            return Err(AddFdError::ProtectedEndpointFdCollision(target_i32));
        }
        Ok(Self {
            src_fd: src_fd as u32,
            target_fd: raw_target_fd as u32,
            newfd_flags: libc::O_CLOEXEC as u32,
        })
    }
}

/// Convert the return code of `ioctl(listener, SECCOMP_IOCTL_NOTIF_ADDFD, ...)` into either the
/// injected descriptor (`Ok(fd)`) or a fail-closed negative errno (`Err(-errno)`), closing the
/// `sandbox.rs:1467` bug where `let _ = ioctl(...)` silently reported `error = 0` on failure.
pub fn check_addfd_ioctl_result(ioctl_rc: i32, raw_os_errno: Option<i32>) -> Result<i32, i32> {
    if ioctl_rc >= 0 {
        Ok(ioctl_rc)
    } else {
        let e = raw_os_errno.unwrap_or(libc::EPERM);
        Err(if e > 0 { -e } else { -libc::EPERM })
    }
}

// =========================================================================
// Bubblewrap & OS Confinement Policy
// =========================================================================

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
    pub pdeathsig_sigkill: bool,
    pub deny_af_unix_connect: bool,
    pub max_addfd_target: u32,
    pub env_allowlist: EnvAllowlistPolicy,
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
            pdeathsig_sigkill: true,
            deny_af_unix_connect: true,
            max_addfd_target: DEFAULT_MAX_ADDFD_TARGET,
            env_allowlist: EnvAllowlistPolicy::strict(),
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

    /// Build the default-deny seccomp-cBPF filter matching this policy for `spec`.
    pub fn build_seccomp_bpf(&self, spec: &SeccompProfileSpec, notify_connect: bool) -> Vec<BpfInsn> {
        let mode = if self.unshare_net {
            DoorMode::Sealed
        } else {
            DoorMode::ProviderNotify
        };
        build_hardened_seccomp_bpf(spec, mode, notify_connect)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strict_policy_flags() {
        let policy = ConfinementPolicy::strict();
        assert!(policy.pdeathsig_sigkill);
        assert!(policy.deny_af_unix_connect);
        let flags = policy.to_bwrap_flags();

        assert!(flags.contains(&"--die-with-parent".to_string()));
        assert!(flags.contains(&"--unshare-net".to_string()));
        assert!(flags.contains(&"--cap-drop".to_string()));
        assert!(flags.contains(&"--disable-userns".to_string()));
        assert!(flags.contains(&"--clearenv".to_string()));
    }

    #[test]
    fn test_env_allowlist_scrubs_parent_secrets_and_rejects_loader_injection() {
        let policy = EnvAllowlistPolicy::strict().with_passthrough_key("SAFE_LOCALE_HINT");
        let host_env = vec![
            ("AWS_SECRET_ACCESS_KEY".into(), "AKIA_SUPER_SECRET".into()),
            ("OPENAI_API_KEY".into(), "sk-live-secret".into()),
            ("GITHUB_TOKEN".into(), "ghp_secret".into()),
            ("LD_PRELOAD".into(), "/tmp/evil.so".into()),
            ("SAFE_LOCALE_HINT".into(), "en_US".into()),
        ];
        let resolved = policy.validate_and_resolve(host_env).unwrap();
        assert!(!resolved.contains_key("AWS_SECRET_ACCESS_KEY"));
        assert!(!resolved.contains_key("OPENAI_API_KEY"));
        assert!(!resolved.contains_key("GITHUB_TOKEN"));
        assert!(!resolved.contains_key("LD_PRELOAD"));
        assert_eq!(resolved.get("SAFE_LOCALE_HINT").map(String::as_str), Some("en_US"));
        assert_eq!(resolved.get("HOME").map(String::as_str), Some("/workspace"));

        // Attempting to allowlist LD_PRELOAD or DYLD_INSERT_LIBRARIES fails closed.
        for bad in ["LD_PRELOAD", "DYLD_INSERT_LIBRARIES", "BASH_ENV", "BAD=KEY", ""] {
            let p = EnvAllowlistPolicy::strict().with_passthrough_key(bad);
            assert!(p.validate_and_resolve(std::iter::empty()).is_err(), "must reject {bad}");
        }
    }

    #[test]
    fn test_seccomp_bpf_blocks_af_unix_and_non_null_sendto_on_both_arches() {
        for spec in [SeccompProfileSpec::linux_x86_64(), SeccompProfileSpec::linux_aarch64()] {
            let sealed = build_hardened_seccomp_bpf(&spec, DoorMode::Sealed, false);
            assert_eq!(
                eval_seccomp_bpf(&sealed, spec.arch, spec.socket_nr, [LINUX_AF_UNIX as u64, 1, 0, 0, 0, 0]),
                SECCOMP_RET_ERRNO_EPERM
            );
            assert_eq!(
                eval_seccomp_bpf(&sealed, spec.arch, spec.socket_nr, [LINUX_AF_INET as u64, 1, 0, 0, 0, 0]),
                SECCOMP_RET_ERRNO_EPERM
            );
            // Connected send(fd, buf, len, 0) -> sendto with args[4] == 0 is allowed; non-null dest_addr is EPERM!
            assert_eq!(
                eval_seccomp_bpf(&sealed, spec.arch, spec.sendto_nr, [3, 0x1000, 16, 0, 0, 0]),
                SECCOMP_RET_ALLOW
            );
            assert_eq!(
                eval_seccomp_bpf(&sealed, spec.arch, spec.sendto_nr, [3, 0x1000, 16, 0, 0x7fff_0000, 110]),
                SECCOMP_RET_ERRNO_EPERM
            );
            assert_eq!(
                eval_seccomp_bpf(&sealed, spec.arch, spec.sendto_nr, [3, 0x1000, 16, 0, 1u64 << 32, 110]),
                SECCOMP_RET_ERRNO_EPERM
            );

            // ProviderNotify allows ONLY AF_INET + SOCK_STREAM, rejecting AF_UNIX / SOCK_DGRAM / high-word smuggling.
            let notify = build_hardened_seccomp_bpf(&spec, DoorMode::ProviderNotify, true);
            assert_eq!(
                eval_seccomp_bpf(&notify, spec.arch, spec.socket_nr, [LINUX_AF_UNIX as u64, LINUX_SOCK_STREAM as u64, 0, 0, 0, 0]),
                SECCOMP_RET_ERRNO_EPERM,
                "AF_UNIX socket must be blocked in ProviderNotify"
            );
            assert_eq!(
                eval_seccomp_bpf(&notify, spec.arch, spec.socket_nr, [LINUX_AF_INET as u64, 2 /* SOCK_DGRAM */, 0, 0, 0, 0]),
                SECCOMP_RET_ERRNO_EPERM,
                "SOCK_DGRAM must be blocked in ProviderNotify"
            );
            assert_eq!(
                eval_seccomp_bpf(&notify, spec.arch, spec.socket_nr, [(1u64 << 32) | LINUX_AF_INET as u64, LINUX_SOCK_STREAM as u64, 0, 0, 0, 0]),
                SECCOMP_RET_ERRNO_EPERM,
                "64-bit high-word domain smuggling must be blocked"
            );
            assert_eq!(
                eval_seccomp_bpf(
                    &notify,
                    spec.arch,
                    spec.socket_nr,
                    [LINUX_AF_INET as u64, (LINUX_SOCK_STREAM | LINUX_SOCK_CLOEXEC | LINUX_SOCK_NONBLOCK) as u64, 0, 0, 0, 0]
                ),
                SECCOMP_RET_ALLOW
            );
            assert_eq!(
                eval_seccomp_bpf(&notify, spec.arch, spec.connect_nr, [4, 0x2000, 16, 0, 0, 0]),
                SECCOMP_RET_USER_NOTIF
            );
            // Foreign arch is killed immediately.
            let foreign = if spec.arch == AUDIT_ARCH_X86_64 {
                AUDIT_ARCH_AARCH64
            } else {
                AUDIT_ARCH_X86_64
            };
            assert_eq!(
                eval_seccomp_bpf(&notify, foreign, spec.unconditional_allows[0], [0; 6]),
                SECCOMP_RET_KILL_PROCESS
            );
        }
    }

    #[test]
    fn test_checked_addfd_bounds_and_connect_sockaddr_af_unix_rejection() {
        // Std streams 0..=2 rejected
        for std_fd in 0..=2 {
            assert_eq!(
                CheckedAddFdSpec::validate(std_fd, 10, &[3], 1024),
                Err(AddFdError::ReservedStdStreamFd(std_fd))
            );
        }
        // Protected endpoint fd rejected
        assert_eq!(
            CheckedAddFdSpec::validate(3, 10, &[3, 7], 1024),
            Err(AddFdError::ProtectedEndpointFdCollision(3))
        );
        // High-word truncation smuggling `(1u64 << 32) | 4` rejected
        assert!(matches!(
            CheckedAddFdSpec::validate((1u64 << 32) | 4, 10, &[3], 1024),
            Err(AddFdError::TargetFdOutOfBounds { .. })
        ));
        // Negative source fd rejected
        assert_eq!(
            CheckedAddFdSpec::validate(5, -1, &[3], 1024),
            Err(AddFdError::InvalidSourceFd(-1))
        );
        // Valid fd passes with O_CLOEXEC
        let ok = CheckedAddFdSpec::validate(5, 10, &[3], 1024).unwrap();
        assert_eq!(ok.target_fd, 5);
        assert_eq!(ok.newfd_flags, libc::O_CLOEXEC as u32);
        // Failed ioctl never reports success
        assert_eq!(check_addfd_ioctl_result(-1, Some(libc::EBADF)), Err(-libc::EBADF));
        assert_eq!(check_addfd_ioctl_result(-1, None), Err(-libc::EPERM));
        assert_eq!(check_addfd_ioctl_result(5, None), Ok(5));

        // AF_UNIX sockaddr rejected
        let mut sa_un = [0u8; 24];
        sa_un[0..2].copy_from_slice(&(LINUX_AF_UNIX as u16).to_ne_bytes());
        sa_un[2..12].copy_from_slice(b"/tmp/s.sock"[..10].as_ref());
        assert_eq!(
            validate_connect_sockaddr(&sa_un, 24, &[([127, 0, 0, 1], 8080)]),
            Err(ConnectFilterError::AfUnixForbidden)
        );
    }
}
