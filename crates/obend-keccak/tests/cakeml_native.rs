//! Differential against the CakeML-compiled Pancake kernels in `lean/Obend/Lower/Pancake`.
//!
//! Set `OBEND_CAKEML_KMAC256` and `OBEND_CAKEML_CSHAKE256` to the native binaries built as the
//! headers of `kmac256.c` and `cshake256.c` describe, then run
//! `cargo test -p obend-keccak --test cakeml_native -- --ignored`.

use std::path::{Path, PathBuf};
use std::process::Command;

use obend_keccak::{kmac256_32, Cshake256, Kmac256};

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!("obend-keccak-cakeml-{}", std::process::id()));
        std::fs::create_dir(&dir).expect("scratch directory");
        Self(dir)
    }

    fn file(&self, name: &str, contents: &[u8]) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, contents).expect("scratch file");
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn run(binary: &Path, args: &[&std::ffi::OsStr]) -> Vec<u8> {
    let output = Command::new(binary)
        .args(args)
        .output()
        .expect("spawn native kernel");
    assert!(
        output.status.success(),
        "{} failed: {}",
        binary.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn state_bytes(lanes: &[u64; 25]) -> Vec<u8> {
    lanes.iter().flat_map(|lane| lane.to_le_bytes()).collect()
}

fn range(len: usize) -> Vec<u8> {
    (0..len).map(|i| i as u8).collect()
}

#[test]
#[ignore = "requires native CakeML binaries"]
fn matches_the_cakeml_native_kernels() {
    let kernel = |name| PathBuf::from(std::env::var_os(name).expect(name));
    let kmac = kernel("OBEND_CAKEML_KMAC256");
    let cshake = kernel("OBEND_CAKEML_CSHAKE256");

    let scratch = Scratch::new();
    let customs = [Vec::new(), b"OBEND.KMAC/v1".to_vec(), range(140)];
    let names = [Vec::new(), b"KMAC".to_vec(), range(140)];
    let message_lens = [0, 3, 133, 134, 135, 136, 137, 271, 272, 409];
    let mut compared = 0usize;

    for custom in &customs {
        let custom_path = scratch.file("custom", custom);
        for len in message_lens {
            let message = range(len);
            let message_path = scratch.file("message", &message);

            for key_len in [0, 32, 128, 131, 136, 200] {
                let key = range(key_len);
                let key_path = scratch.file("key", &key);
                let expected = kmac256_32(&key, custom, &message);

                let one_shot = run(
                    &kmac,
                    &[
                        key_path.as_os_str(),
                        custom_path.as_os_str(),
                        message_path.as_os_str(),
                    ],
                );
                assert_eq!(one_shot, expected, "KMAC |K|={key_len} |X|={len}");

                let midstate = Kmac256::new(&key, custom).midstate().expect("keyed state");
                let state_path = scratch.file("state", &state_bytes(midstate.lanes()));
                let resumed = run(
                    &kmac,
                    &[
                        "--resume".as_ref(),
                        state_path.as_os_str(),
                        "1".as_ref(),
                        message_path.as_os_str(),
                    ],
                );
                assert_eq!(resumed, expected, "KMAC resume |K|={key_len} |X|={len}");
                compared += 2;
            }

            for name in &names {
                let name_path = scratch.file("name", name);
                let mut xof = Cshake256::new(name, custom);
                let midstate = xof.midstate().expect("prefix ends on a rate boundary");
                xof.absorb(&message);
                let expected = xof.finalize_32();

                let one_shot = run(
                    &cshake,
                    &[
                        name_path.as_os_str(),
                        custom_path.as_os_str(),
                        message_path.as_os_str(),
                    ],
                );
                assert_eq!(one_shot, expected, "cSHAKE |N|={} |X|={len}", name.len());
                compared += 1;

                if !(name.is_empty() && custom.is_empty()) {
                    let state_path = scratch.file("state", &state_bytes(midstate.lanes()));
                    let resumed = run(
                        &kmac,
                        &[
                            "--resume".as_ref(),
                            state_path.as_os_str(),
                            "0".as_ref(),
                            message_path.as_os_str(),
                        ],
                    );
                    assert_eq!(resumed, expected, "cSHAKE resume |N|={}", name.len());
                    compared += 1;
                }
            }
        }
    }
    eprintln!("{compared} native comparisons agreed");
    assert_eq!(
        compared,
        customs.len() * message_lens.len() * (6 * 2 + names.len() * 2) - message_lens.len()
    );
}
