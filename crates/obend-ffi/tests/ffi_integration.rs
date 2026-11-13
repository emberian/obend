use obend_ffi::pool::{ensure_lean_thread_initialized, LeanWorkerPool};
use obend_ffi::session::ObendSession;
use serde_json::{json, Value};

#[test]
fn test_session_lifecycle_elaborates_obend_and_refuses_non_obend() {
    let mut session = ObendSession::new().expect("init session");

    // Arbitrary non-.obend bytes fail closed rather than echoing.
    assert!(session.eval_cell(b"42").is_err());

    let obend_src = b"edition ObjectiveBend 1\nlaw bounded_x: new.x <= 64\ndef answer() -> Nat:\n  42n\n";
    let out = session.eval_cell(obend_src).expect("elaborate .obend cell");
    let parsed: Value = serde_json::from_slice(&out).expect("JSON summary");
    assert_eq!(parsed["schema"], "obend.ffi.elaboration.v1");
    assert_eq!(parsed["status"], "accepted");
    assert!(!parsed["declarations"].as_array().unwrap().is_empty());
}

#[test]
fn test_replay_world_turn_proposal_and_commit() {
    let mut session = ObendSession::new().unwrap();

    // Open a page in `Obend.Vault.Replay.World` via a genuine `Replay.Turn` JSON payload.
    let open_turn = br##"{"turn":"open","files":[["note.md","# Note\n\ncount: 1\n"]],"environment":null}"##;
    let tid = session.propose_turn(open_turn).expect("propose Replay open turn");
    assert_eq!(tid.len(), 32);
    session.commit_turn(&tid).expect("commit Replay open turn");

    // Writing to a nonexistent page in `Replay.World` must fail closed at proposal time.
    let bad_write = br#"{"turn":"write","page":"missing.md","text":"hello\n"}"#;
    assert!(session.propose_turn(bad_write).is_err());

    // Writing to the opened page succeeds and steps `Replay.World`.
    let good_write = br##"{"turn":"write","page":"note.md","text":"# Note\n\ncount: 2\n"}"##;
    let tid2 = session.propose_turn(good_write).expect("propose Replay write turn");
    session.commit_turn(&tid2).expect("commit Replay write turn");
}

#[test]
fn test_hardware_projection_verifies_cam_witness_and_refuses_arbitrary_bytes() {
    let mut session = ObendSession::new().unwrap();

    // Arbitrary bytes are refused fail-closed (-7).
    assert!(session.project_hardware(b"mock_hw_certificate").is_err());

    // Planted gouging CAM witness (`camGougeBad`) is refused fail-closed (-7).
    let bad_cam = json!({
        "format": "cam-gouge",
        "version": "1",
        "grade": 0,
        "obj": "part c -5\nbox 0 4 0 4 0 4\ntool 1 2\nchunk 0 0 1 1 2 2 1 2 2 1\n",
        "cert": "1:T\n"
    });
    assert!(session
        .project_hardware(bad_cam.to_string().as_bytes())
        .is_err());

    // Verified gouge-free CAM witness (`part = .const 10 > 0` across `[0, 4]^3`, leaf `P`) passes.
    let valid_cam = json!({
        "format": "cam-gouge",
        "version": "1",
        "grade": 0,
        "obj": "part c 10\nbox 0 4 0 4 0 4\ntool 1 2\nchunk 0 0 1 1 2 2 10 2 2 10\n",
        "cert": "1:P\n"
    });
    let proj = session
        .project_hardware(valid_cam.to_string().as_bytes())
        .expect("verified cam-gouge@1 witness");
    let summary: Value = serde_json::from_slice(&proj).expect("JSON projection summary");
    assert_eq!(summary["schema"], "obend.ffi.hardware_projection.v1");
    assert_eq!(summary["status"], "verified");
    assert_eq!(summary["format"], "cam-gouge");
}

#[test]
fn test_receipt_verification() {
    let mut session = ObendSession::new().unwrap();
    let bare_root = vec![0xAB; 32];
    assert!(!session.verify_receipt(&bare_root).unwrap());

    let tid = session.propose_turn(b"turn_for_receipt").unwrap();
    assert!(!session.verify_receipt(&tid).unwrap());
    let valid_receipt = session.commit_payload(b"turn_for_receipt").unwrap();
    assert!(session.verify_receipt(&valid_receipt).unwrap());

    let invalid_receipt = vec![0xAB; 16];
    assert!(!session.verify_receipt(&invalid_receipt).unwrap());
}

#[test]
fn test_worker_pool_concurrency() {
    ensure_lean_thread_initialized();
    let pool = LeanWorkerPool::new(4);
    let rx1 = pool.execute(|| 10 * 2);
    let rx2 = pool.execute(|| 20 * 2);
    assert_eq!(rx1.recv().unwrap(), 20);
    assert_eq!(rx2.recv().unwrap(), 40);
}
