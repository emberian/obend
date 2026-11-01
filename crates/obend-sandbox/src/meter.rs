use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};

pub struct CpuMeter;

impl CpuMeter {
    pub fn parse_cpu_stat(content: &str) -> Option<u64> {
        for line in content.lines() {
            if let Some(rest) = line.strip_prefix("usage_usec ") {
                if let Ok(val) = rest.trim().parse::<u64>() {
                    return Some(val);
                }
            }
        }
        None
    }

    pub fn read_cgroup_cpu_usec(cgroup_cpu_stat: &Path) -> Result<u64, String> {
        let content = fs::read_to_string(cgroup_cpu_stat).map_err(|e| format!("cpu.stat read: {e}"))?;
        Self::parse_cpu_stat(&content).ok_or_else(|| "usage_usec not found in cpu.stat".to_string())
    }

    pub fn write_cpu_record(dir: &Path, unit: &str, usec: u64) -> Result<PathBuf, String> {
        let path = dir.join(format!("{unit}.cpu"));
        let tmp = dir.join(format!("{unit}.cpu.tmp"));
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .open(&tmp)
            .map_err(|e| format!("cpu temp file open: {e}"))?;
        writeln!(file, "obend-grain-cpu-v1 {usec}").map_err(|e| format!("cpu write: {e}"))?;
        fs::rename(&tmp, &path).map_err(|e| format!("cpu file rename: {e}"))?;
        Ok(path)
    }

    pub fn read_cpu_record(record_path: &Path) -> Result<u64, String> {
        let content = fs::read_to_string(record_path).map_err(|e| format!("cpu record read: {e}"))?;
        let first = content.lines().next().ok_or_else(|| "empty cpu record".to_string())?;
        if let Some(rest) = first.strip_prefix("obend-grain-cpu-v1 ") {
            rest.trim()
                .parse::<u64>()
                .map_err(|e| format!("invalid cpu usec: {e}"))
        } else {
            Err("invalid cpu record header".to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_cpu_stat() {
        let stat = "usage_usec 421950\nuser_usec 300000\nsystem_usec 121950\n";
        assert_eq!(CpuMeter::parse_cpu_stat(stat), Some(421950));
    }

    #[test]
    fn test_cpu_record_roundtrip() {
        let tmp = std::env::temp_dir().join(format!("obend_test_cpu_{}", std::process::id()));
        let _ = fs::create_dir_all(&tmp);

        let path = CpuMeter::write_cpu_record(&tmp, "obend-grain-t1-o1", 85000).unwrap();
        let read = CpuMeter::read_cpu_record(&path).unwrap();
        assert_eq!(read, 85000);

        let _ = fs::remove_dir_all(&tmp);
    }
}
