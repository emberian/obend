use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::io::AsRawFd;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static TMP_NONCE: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateStatus {
    Armed,
    Started,
    Fenced,
}

impl GateStatus {
    pub fn parse(s: &str) -> Option<Self> {
        let first_line = s.lines().next()?.trim();
        if first_line == "armed" || first_line.starts_with("armed ") {
            Some(GateStatus::Armed)
        } else if first_line == "started" || first_line.starts_with("started ") {
            Some(GateStatus::Started)
        } else if first_line == "fenced" || first_line.starts_with("fenced ") {
            Some(GateStatus::Fenced)
        } else {
            None
        }
    }
}

/// Strictly validate `unit` against `[A-Za-z0-9_.-]`, rejecting empty strings, `.`, `..`, and path separators.
pub fn validate_gate_unit(unit: &str) -> Result<(), String> {
    if unit.is_empty() {
        return Err("invalid gate unit: must not be empty".to_string());
    }
    if unit == "." || unit == ".." || unit.contains("..") {
        return Err(format!(
            "invalid gate unit '{unit}': path traversal segments forbidden"
        ));
    }
    if !unit
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'))
    {
        return Err(format!(
            "invalid gate unit '{unit}': only [A-Za-z0-9_.-] permitted"
        ));
    }
    Ok(())
}

struct FlockGuard {
    file: File,
}

impl FlockGuard {
    fn acquire(lock_path: &std::path::Path, operation: libc::c_int) -> Result<Self, String> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(lock_path)
            .map_err(|e| format!("gate lock open ({}): {e}", lock_path.display()))?;
        let rc = unsafe { libc::flock(file.as_raw_fd(), operation) };
        if rc != 0 {
            return Err(format!(
                "gate flock failed: {}",
                std::io::Error::last_os_error()
            ));
        }
        Ok(Self { file })
    }
}

impl Drop for FlockGuard {
    fn drop(&mut self) {
        let _ = unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}

pub struct LaunchGate {
    pub state_dir: PathBuf,
    pub unit: String,
}

impl LaunchGate {
    pub fn new(state_dir: impl Into<PathBuf>, unit: impl Into<String>) -> Self {
        Self {
            state_dir: state_dir.into(),
            unit: unit.into(),
        }
    }

    pub fn try_new(state_dir: impl Into<PathBuf>, unit: impl Into<String>) -> Result<Self, String> {
        let unit_str = unit.into();
        validate_gate_unit(&unit_str)?;
        Ok(Self {
            state_dir: state_dir.into(),
            unit: unit_str,
        })
    }

    pub fn gate_path(&self) -> PathBuf {
        self.state_dir.join(format!("{}.gate", self.unit))
    }

    fn checked_paths(&self) -> Result<(PathBuf, PathBuf), String> {
        validate_gate_unit(&self.unit)?;
        let gate_path = self.state_dir.join(format!("{}.gate", self.unit));
        let lock_path = self.state_dir.join(format!(".{}.gate.lock", self.unit));
        Ok((gate_path, lock_path))
    }

    fn atomic_write_gate(&self, gate_path: &std::path::Path, payload: &[u8]) -> Result<(), String> {
        let seq = TMP_NONCE.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let tmp_path = self
            .state_dir
            .join(format!(".{}.gate.tmp.{pid}.{seq}", self.unit));

        let mut tmp_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&tmp_path)
            .map_err(|e| format!("gate temp create: {e}"))?;

        if let Err(e) = tmp_file
            .write_all(payload)
            .and_then(|()| tmp_file.sync_all())
        {
            let _ = fs::remove_file(&tmp_path);
            return Err(format!("gate temp write/sync: {e}"));
        }
        drop(tmp_file);

        if let Err(e) = fs::rename(&tmp_path, gate_path) {
            let _ = fs::remove_file(&tmp_path);
            return Err(format!("gate atomic rename: {e}"));
        }
        fs::File::open(&self.state_dir)
            .and_then(|dir| dir.sync_all())
            .map_err(|e| format!("gate dir sync: {e}"))?;
        Ok(())
    }

    fn read_gate_nofollow(gate_path: &std::path::Path) -> Result<String, String> {
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(gate_path)
            .map_err(|e| format!("gate read: {e}"))?;
        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| format!("gate read: {e}"))?;
        Ok(content)
    }

    pub fn init(&self) -> Result<(), String> {
        let (path, lock_path) = self.checked_paths()?;
        let _lock = FlockGuard::acquire(&lock_path, libc::LOCK_EX)?;
        match fs::symlink_metadata(&path) {
            Ok(_) => return Err(format!("gate already exists: {}", path.display())),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(format!("gate metadata: {e}")),
        }
        self.atomic_write_gate(&path, b"armed\n")
    }

    pub fn fence(&self) -> Result<(), String> {
        let (path, lock_path) = self.checked_paths()?;
        let _lock = FlockGuard::acquire(&lock_path, libc::LOCK_EX)?;
        self.atomic_write_gate(&path, b"fenced\n")
    }

    pub fn status(&self) -> Result<GateStatus, String> {
        let (path, lock_path) = self.checked_paths()?;
        let _lock = FlockGuard::acquire(&lock_path, libc::LOCK_SH)?;
        let content = Self::read_gate_nofollow(&path)?;
        GateStatus::parse(&content).ok_or_else(|| "unknown gate state".to_string())
    }

    pub fn transition_to_started(&self) -> Result<(), String> {
        let (path, lock_path) = self.checked_paths()?;
        let _lock = FlockGuard::acquire(&lock_path, libc::LOCK_EX)?;
        let content = Self::read_gate_nofollow(&path)?;
        let st = GateStatus::parse(&content).ok_or_else(|| "unknown gate state".to_string())?;
        if st != GateStatus::Armed {
            return Err("gate is not armed".to_string());
        }
        let new_content = content.replacen("armed", "started", 1);
        self.atomic_write_gate(&path, new_content.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_gate_lifecycle() {
        let tmp = std::env::temp_dir().join(format!("obend_test_gate_{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp).unwrap();
        let gate = LaunchGate::new(&tmp, "obend-grain-t1-o1");

        assert!(gate.init().is_ok());
        assert_eq!(gate.status().unwrap(), GateStatus::Armed);

        assert!(gate.transition_to_started().is_ok());
        assert_eq!(gate.status().unwrap(), GateStatus::Started);

        // Cannot start again
        assert!(gate.transition_to_started().is_err());

        // Fence
        assert!(gate.fence().is_ok());
        assert_eq!(gate.status().unwrap(), GateStatus::Fenced);

        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_gate_rejects_traversal_and_metachar_units() {
        let tmp = std::env::temp_dir().join(format!("obend_test_gate_val_{}", std::process::id()));
        let _ = fs::create_dir_all(&tmp);
        for bad in [
            "",
            ".",
            "..",
            "../escape",
            "sub/unit",
            "sub\\unit",
            "unit..two",
            "unit space",
            "unit;rm",
        ] {
            assert!(LaunchGate::try_new(&tmp, bad).is_err(), "must reject '{bad}'");
            let g = LaunchGate::new(&tmp, bad);
            assert!(g.init().is_err());
            assert!(g.status().is_err());
            assert!(g.transition_to_started().is_err());
            assert!(g.fence().is_err());
        }
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_gate_concurrent_race_allows_exactly_one_winner() {
        let tmp = std::env::temp_dir().join(format!("obend_test_gate_race_{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp).unwrap();
        let gate = LaunchGate::new(&tmp, "race-unit.v1");
        gate.init().unwrap();

        let barrier = Arc::new(std::sync::Barrier::new(16));
        let mut handles = Vec::new();
        for _ in 0..16 {
            let dir = tmp.clone();
            let b = Arc::clone(&barrier);
            handles.push(std::thread::spawn(move || {
                let g = LaunchGate::new(dir, "race-unit.v1");
                b.wait();
                g.transition_to_started().is_ok()
            }));
        }
        let wins: usize = handles
            .into_iter()
            .map(|h| usize::from(h.join().unwrap()))
            .sum();
        assert_eq!(wins, 1, "TOCTOU race check: exactly 1 contender may transition Armed -> Started");
        assert_eq!(gate.status().unwrap(), GateStatus::Started);
        let _ = fs::remove_dir_all(&tmp);
    }
}
