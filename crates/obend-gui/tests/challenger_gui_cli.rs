use obend_gui::evaluator::{NotebookCell, NotebookRunner};
use std::fs;
use std::process::Command;

#[test]
fn test_challenger_runner_empty_cell_list() {
    let mut runner = NotebookRunner::new().expect("Init runner");
    let results = runner.execute_cells(&[]);
    assert!(results.is_empty());
}

#[test]
fn test_challenger_runner_mixed_valid_and_invalid_cells() {
    let mut runner = NotebookRunner::new().expect("Init runner");
    let cells = vec![
        NotebookCell {
            id: "good1".to_string(),
            kind: "obendCode".to_string(),
            source: "let x = 1".to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "bad_empty".to_string(),
            kind: "obendCode".to_string(),
            source: "".to_string(), // Empty payload fails evaluation
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "good2".to_string(),
            kind: "casSymbolic".to_string(),
            source: "x * 2".to_string(),
            status: "ready".to_string(),
        },
    ];

    let results = runner.execute_cells(&cells);
    assert_eq!(results.len(), 3);
    assert_eq!(results[0].0, "good1");
    assert!(results[0].1.is_ok());

    assert_eq!(results[1].0, "bad_empty");
    assert!(results[1].1.is_err(), "Empty cell must report error");

    // Execution must continue past the failing cell
    assert_eq!(results[2].0, "good2");
    assert!(results[2].1.is_ok());
}

#[test]
fn test_challenger_runner_large_batch() {
    let mut runner = NotebookRunner::new().expect("Init runner");
    let count = 200;
    let mut cells = Vec::with_capacity(count);
    for i in 0..count {
        cells.push(NotebookCell {
            id: format!("cell_{}", i),
            kind: "obendCode".to_string(),
            source: format!("val_{}", i),
            status: "ready".to_string(),
        });
    }

    let results = runner.execute_cells(&cells);
    assert_eq!(results.len(), count);
    for (i, (id, res)) in results.into_iter().enumerate() {
        assert_eq!(id, format!("cell_{}", i));
        assert!(res.is_ok());
    }
}

#[test]
fn test_challenger_cli_nonexistent_files_fail() {
    let bin_path = env!("CARGO_BIN_EXE_obend-gui");

    // Missing file on 'run'
    let output = Command::new(bin_path)
        .args(["run", "/path/to/definitely_nonexistent_notebook.obnb"])
        .output()
        .expect("Failed to execute obend-gui binary");
    assert!(!output.status.success(), "CLI must return non-zero on missing notebook");

    // Missing file on 'inspect'
    let output = Command::new(bin_path)
        .args(["inspect", "/path/to/definitely_nonexistent_file.obnb"])
        .output()
        .expect("Failed to execute obend-gui binary");
    assert!(!output.status.success(), "CLI must return non-zero on missing file");

    // Missing file on 'project-hw'
    let output = Command::new(bin_path)
        .args(["project-hw", "/path/to/definitely_nonexistent_cert.bin"])
        .output()
        .expect("Failed to execute obend-gui binary");
    assert!(!output.status.success(), "CLI must return non-zero on missing certificate");
}

#[test]
fn test_challenger_cli_empty_file_fails_eval() {
    let bin_path = env!("CARGO_BIN_EXE_obend-gui");
    let temp_dir = std::env::temp_dir();
    let empty_file = temp_dir.join("empty_test_notebook.obnb");
    fs::write(&empty_file, b"").expect("write empty file");

    let output = Command::new(bin_path)
        .args(["run", empty_file.to_str().unwrap()])
        .output()
        .expect("Failed to execute obend-gui binary");

    let _ = fs::remove_file(&empty_file);
    assert!(!output.status.success(), "CLI run on empty file must fail evaluation");
}

#[test]
fn test_challenger_cli_invalid_subcommand() {
    let bin_path = env!("CARGO_BIN_EXE_obend-gui");
    let output = Command::new(bin_path)
        .arg("unknown-subcommand")
        .output()
        .expect("Failed to execute obend-gui binary");
    assert!(!output.status.success(), "CLI must exit with error on unknown subcommand");
}
