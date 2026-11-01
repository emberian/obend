//! Durable Linux per-operation systemd ExecStart gate for Obend grain workers.
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

#[cfg(target_os = "linux")]
pub const O_NOFOLLOW: i32 = 0o0400000;
#[cfg(not(target_os = "linux"))]
pub const O_NOFOLLOW: i32 = 0x01000000;

pub const LOCK_EX: i32 = 2;
pub const LOCK_UN: i32 = 8;

const SYS_PIDFD_OPEN: i64 = 434;

extern "C" {
    fn geteuid() -> u32;
    fn flock(fd: i32, operation: i32) -> i32;
    fn syscall(number: i64, ...) -> i64;
}

fn lock(file: &File, operation: i32) -> Result<(), String> {
    if unsafe { flock(file.as_raw_fd(), operation) } == 0 {
        Ok(())
    } else {
        Err(format!("flock: {}", std::io::Error::last_os_error()))
    }
}

fn private_dir(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("state dir must be absolute".into());
    }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.file_type().is_dir()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err("state dir must be an owned, real, private directory (mode 0700)".into());
    }
    Ok(())
}

fn gate_path(dir: &Path, unit: &str) -> Result<PathBuf, String> {
    let Some(rest) = unit.strip_prefix("obend-grain-t") else {
        return Err("bad unit name".into());
    };
    let Some((task, operation)) = rest.split_once("-o") else {
        return Err("bad unit name".into());
    };
    if task.is_empty()
        || operation.is_empty()
        || !task.bytes().all(|b| b.is_ascii_digit())
        || !operation.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("bad unit name".into());
    }
    Ok(dir.join(format!("{unit}.gate")))
}

fn open_gate(path: &Path, create: bool) -> Result<File, String> {
    let mut options = OpenOptions::new();
    options
        .read(true)
        .write(true)
        .custom_flags(O_NOFOLLOW)
        .mode(0o600);
    if create {
        options.create(true);
    }
    let file = options.open(path).map_err(|e| format!("gate open: {e}"))?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.file_type().is_file()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err("gate must be an owned private regular file (mode 0600)".into());
    }
    Ok(file)
}

fn read_state(file: &mut File) -> Result<String, String> {
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    let mut state = String::new();
    file.take(1024)
        .read_to_string(&mut state)
        .map_err(|e| e.to_string())?;
    Ok(state)
}

fn write_state(file: &mut File, state: &str) -> Result<(), String> {
    file.set_len(0).map_err(|e| e.to_string())?;
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    file.write_all(state.as_bytes()).map_err(|e| e.to_string())
}

#[derive(Clone, Debug)]
struct Controller {
    manager: String,
    unit: String,
    pid: u32,
    invocation: String,
    start: String,
}

impl Controller {
    fn from_env(unit: &str) -> Result<Option<Self>, String> {
        let manager = env::var("OBEND_GRAIN_CONTROLLER_MANAGER").unwrap_or_else(|_| "user".into());
        let pid = match env::var("OBEND_GRAIN_CONTROLLER_PID") {
            Ok(pid) => pid.parse::<u32>().map_err(|_| "invalid controller PID")?,
            Err(_) => return Ok(None),
        };
        let task = unit
            .strip_prefix("obend-grain-t")
            .and_then(|x| x.split_once("-o"))
            .ok_or("invalid worker unit")?
            .0;
        let expected = format!("obend-grain-controller@{task}.service");
        let invocation = env::var("OBEND_GRAIN_CONTROLLER_INVOCATION_ID").unwrap_or_default();
        let value = Self {
            manager,
            unit: expected,
            pid,
            invocation,
            start: process_start(pid)?,
        };
        Ok(Some(value))
    }

    fn encode(&self) -> String {
        format!(
            "{} {} {} {} {}",
            self.manager, self.unit, self.pid, self.invocation, self.start
        )
    }

    #[allow(dead_code)]
    fn decode(text: &str) -> Result<Self, String> {
        let words: Vec<_> = text.split(' ').collect();
        if words.len() != 5 {
            return Err("invalid retained controller identity".into());
        }
        let pid = words[2].parse().map_err(|_| "invalid retained PID")?;
        Ok(Self {
            manager: words[0].into(),
            unit: words[1].into(),
            pid,
            invocation: words[3].into(),
            start: words[4].into(),
        })
    }

    #[allow(dead_code)]
    fn open(&self) -> Result<File, String> {
        let fd = unsafe { syscall(SYS_PIDFD_OPEN, self.pid as i64, 0i64) };
        if fd < 0 {
            return Err(format!("controller pidfd: {}", std::io::Error::last_os_error()));
        }
        Ok(unsafe { File::from_raw_fd(fd as i32) })
    }
}

fn process_start(pid: u32) -> Result<String, String> {
    let text = fs::read_to_string(format!("/proc/{pid}/stat")).map_err(|e| e.to_string())?;
    text.rsplit_once(')')
        .and_then(|(_, tail)| tail.split_whitespace().nth(19))
        .map(str::to_owned)
        .ok_or_else(|| "invalid process stat".into())
}

fn unit_cpu_usec() -> Result<u64, String> {
    let cgroup =
        fs::read_to_string("/proc/self/cgroup").map_err(|e| format!("own cgroup: {e}"))?;
    let path = cgroup
        .lines()
        .find_map(|line| line.strip_prefix("0::"))
        .ok_or_else(|| "no cgroup v2 membership".to_string())?;
    if !path.starts_with('/') || path.contains("..") {
        return Err("cgroup path refused".into());
    }
    let stat = fs::read_to_string(format!("/sys/fs/cgroup{path}/cpu.stat"))
        .map_err(|e| format!("cpu.stat: {e}"))?;
    stat.lines()
        .find_map(|line| line.strip_prefix("usage_usec "))
        .and_then(|n| n.trim().parse::<u64>().ok())
        .ok_or_else(|| "cpu.stat has no usage_usec".into())
}

fn record_cpu(dir: &Path, unit: &str, usec: u64) -> Result<(), String> {
    let gate = gate_path(dir, unit)?;
    let path = gate.with_extension("cpu");
    let temporary = gate.with_extension("cpu.tmp");
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .custom_flags(O_NOFOLLOW)
        .mode(0o600)
        .open(&temporary)
        .map_err(|e| format!("cpu record: {e}"))?;
    file.write_all(format!("obend-grain-cpu-v1 {usec}\n").as_bytes())
        .map_err(|e| format!("cpu record write: {e}"))?;
    fs::hard_link(&temporary, &path).map_err(|e| format!("cpu record publish: {e}"))?;
    fs::remove_file(&temporary).map_err(|e| format!("cpu record publish: {e}"))?;
    Ok(())
}

fn supervise(_controller: Option<File>, mut command: Command, _gate: File) -> Result<(), String> {
    let mut child = command.spawn().map_err(|e| format!("worker spawn: {e}"))?;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                return if status.success() {
                    Ok(())
                } else {
                    Err(format!("worker exited: {status}"))
                };
            }
            Ok(None) => {}
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(e.to_string());
            }
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() == 2 && args[1] == "--controller-manager-protocol" {
        println!("obend-controller-manager-v1");
        return Ok(());
    }
    if args.len() == 2 && args[1] == "--launch-gate-protocol" {
        println!("obend-grain-launch-gate-v1");
        return Ok(());
    }
    if args.len() < 4 {
        return Err(
            "usage: launch-gate init|fence|run STATE_DIR UNIT [--meter] [-- ABS_COMMAND ...]".into(),
        );
    }
    let mode = args[1].to_str().ok_or_else(|| "mode UTF-8".to_string())?;
    let dir = Path::new(&args[2]);
    private_dir(dir)?;
    let unit = args[3].to_str().ok_or_else(|| "unit UTF-8".to_string())?;
    let path = gate_path(dir, unit)?;

    match mode {
        "init" => {
            let mut file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .custom_flags(O_NOFOLLOW)
                .mode(0o600)
                .open(&path)
                .map_err(|e| format!("gate init: {e}"))?;
            lock(&file, LOCK_EX)?;
            let controller = Controller::from_env(unit)?;
            let state = controller
                .map(|c| format!("armed\n{}\n", c.encode()))
                .unwrap_or_else(|| "armed\n".into());
            write_state(&mut file, &state)?;
            lock(&file, LOCK_UN)?;
            println!("armed {unit}");
        }
        "fence" => {
            let mut file = open_gate(&path, true)?;
            lock(&file, LOCK_EX)?;
            write_state(&mut file, "fenced\n")?;
            lock(&file, LOCK_UN)?;
            println!("fenced {unit}");
        }
        "run" => {
            let meter = args.get(4).map(|s| s == "--meter").unwrap_or(false);
            let first = if meter { 6 } else { 5 };
            let command = Path::new(&args[first]);
            let mut file = open_gate(&path, false)?;
            lock(&file, LOCK_EX)?;
            let state = read_state(&mut file)?;
            if !state.starts_with("armed") {
                return Err("worker launch fenced or already started".into());
            }
            write_state(&mut file, &state.replacen("armed", "started", 1))?;
            lock(&file, LOCK_UN)?;

            let mut command = Command::new(command);
            command.args(&args[first + 1..]);
            if meter {
                let result = supervise(None, command, file);
                let recorded = unit_cpu_usec().and_then(|usec| record_cpu(dir, unit, usec));
                return match (result, recorded) {
                    (Ok(()), Ok(())) => Ok(()),
                    (Err(e), _) => Err(e),
                    (Ok(()), Err(r)) => Err(r),
                };
            }
            let err = command.exec();
            return Err(format!("exec error: {err}"));
        }
        _ => return Err("invalid mode".into()),
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("launch-gate: {e}");
            ExitCode::FAILURE
        }
    }
}
