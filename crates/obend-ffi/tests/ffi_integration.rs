use obend_ffi::pool::{ensure_lean_thread_initialized, LeanWorkerPool};
use obend_ffi::session::ObendSession;

#[test]
fn test_session_lifecycle() {
    let session = ObendSession::new();
    assert!(session.is_ok());
    let mut session = session.unwrap();

    let res = session.eval_cell(b"42");
    assert!(res.is_ok());
    assert_eq!(res.unwrap(), b"42");
}

#[test]
fn test_turn_proposal_and_commit() {
    let mut session = ObendSession::new().unwrap();
    let turn_payload = b"turn_test_data";
    let tid = session.propose_turn(turn_payload).unwrap();
    assert_eq!(tid.len(), 32);

    let commit_res = session.commit_turn(&tid);
    assert!(commit_res.is_ok());
}

#[test]
fn test_hardware_projection() {
    let mut session = ObendSession::new().unwrap();
    let hw_bytes = b"mock_hw_certificate";
    let proj = session.project_hardware(hw_bytes).unwrap();
    assert!(!proj.is_empty());
}

#[test]
fn test_receipt_verification() {
    let mut session = ObendSession::new().unwrap();
    // A bare 32-byte value is not a receipt, whether or not the session has seen it.
    let bare_root = vec![0xAB; 32];
    assert_eq!(session.verify_receipt(&bare_root).unwrap(), false);

    // Proposing admits nothing; committing yields the receipt that verifies.
    let tid = session.propose_turn(b"turn_for_receipt").unwrap();
    assert_eq!(session.verify_receipt(&tid).unwrap(), false);
    let valid_receipt = session.commit_payload(b"turn_for_receipt").unwrap();
    assert_eq!(session.verify_receipt(&valid_receipt).unwrap(), true);

    let invalid_receipt = vec![0xAB; 16];
    assert_eq!(session.verify_receipt(&invalid_receipt).unwrap(), false);
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
