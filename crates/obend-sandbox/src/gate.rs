use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateStatus {
    Armed,
    Started,
    Fenced,
}

impl GateStatus {
    pub fn parse(s: &str) -> Option<Self> {
        let first_line = s.lines().next()?.trim();
        if first_line.starts_with("armed") {
            Some(GateStatus::Armed)
        } else if first_line.starts_with("started") {
            Some(GateStatus::Started)
        } else if first_line.starts_with("fenced") {
            Some(GateStatus::Fenced)
        } else {
            None
        }
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

    pub fn gate_path(&self) -> PathBuf {
        self.state_dir.join(format!("{}.gate", self.unit))
    }

    pub fn init(&self) -> Result<(), String> {
        let path = self.gate_path();
        if path.exists() {
            return Err(format!("gate already exists: {}", path.display()));
        }
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .map_err(|e| format!("gate create: {e}"))?;
        file.write_all(b"armed\n")
            .map_err(|e| format!("gate write: {e}"))?;
        Ok(())
    }

    pub fn fence(&self) -> Result<(), String> {
        let path = self.gate_path();
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .open(&path)
            .map_err(|e| format!("gate open: {e}"))?;
        file.write_all(b"fenced\n")
            .map_err(|e| format!("gate write: {e}"))?;
        Ok(())
    }

    pub fn status(&self) -> Result<GateStatus, String> {
        let path = self.gate_path();
        let mut file = File::open(&path).map_err(|e| format!("gate read: {e}"))?;
        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| format!("gate read: {e}"))?;
        GateStatus::parse(&content).ok_or_else(|| "unknown gate state".to_string())
    }

    pub fn transition_to_started(&self) -> Result<(), String> {
        let path = self.gate_path();
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .mode(0o600)
            .open(&path)
            .map_err(|e| format!("gate open: {e}"))?;
        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| format!("gate read: {e}"))?;
        let st = GateStatus::parse(&content).ok_or_else(|| "unknown gate state".to_string())?;
        if st != GateStatus::Armed {
            return Err("gate is not armed".to_string());
        }
        file.set_len(0).map_err(|e| e.to_string())?;
        file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
        let new_content = content.replacen("armed", "started", 1);
        file.write_all(new_content.as_bytes())
            .map_err(|e| format!("gate write: {e}"))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_gate_lifecycle() {
        let tmp = std::env::temp_dir().join(format!("obend_test_gate_{}", std::process::id()));
        let _ = fs::create_dir_all(&tmp);
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
}
