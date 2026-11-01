use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use obend_ffi::sys;
use std::ptr;
use std::thread;

#[test]
fn test_cabi_zero_length_buffers() {
    let mut session = ObendSession::new().expect("Init session");

    // Empty cell payload should fail with DecodeFailed (-3)
    let res_cell = session.eval_cell(&[]);
    assert!(res_cell.is_err());
    match res_cell.err().unwrap() {
        ObendError::DecodeFailed | ObendError::WithDetail(_, _) => {}
        other => panic!("Expected DecodeFailed, got {:?}", other),
    }

    // Empty turn payload should fail with -3
    let res_turn = session.propose_turn(&[]);
    assert!(res_turn.is_err());

    // Empty hardware certificate should fail with -7
    let res_hw = session.project_hardware(&[]);
    assert!(res_hw.is_err());

    // Empty receipt should return false (invalid)
    let res_rcpt = session.verify_receipt(&[]);
    assert_eq!(res_rcpt.unwrap(), false);

    // Turn commit with empty ID is allowed (empty turn id)
    let res_commit = session.commit_turn(&[]);
    assert!(res_commit.is_ok());
}

#[test]
fn test_cabi_truncated_and_invalid_turn_commits() {
    let mut session = ObendSession::new().expect("Init session");

    // Valid turn ID must be exactly 32 bytes (or empty)
    for len in [1, 7, 16, 31, 33, 64, 128] {
        let invalid_id = vec![0xAA; len];
        let res = session.commit_turn(&invalid_id);
        assert!(res.is_err(), "Length {} should be rejected", len);
    }

    let valid_id = vec![0xBB; 32];
    assert!(session.commit_turn(&valid_id).is_ok());
}

#[test]
fn test_cabi_truncated_receipts() {
    let mut session = ObendSession::new().expect("Init session");

    // Receipts < 32 bytes must evaluate to false
    for len in [1, 15, 31] {
        let malformed = vec![0xCC; len];
        assert_eq!(session.verify_receipt(&malformed).unwrap(), false);
    }

    let valid_rcpt = vec![0xDD; 32];
    assert_eq!(session.verify_receipt(&valid_rcpt).unwrap(), true);

    let large_rcpt = vec![0xEE; 128];
    assert_eq!(session.verify_receipt(&large_rcpt).unwrap(), true);
}

#[test]
fn test_cabi_oversized_buffers_and_scratch_realloc() {
    let mut session = ObendSession::new().expect("Init session");

    // Rapidly switch between small, huge, and medium buffers to stress scratch allocation
    let sizes = [16, 1024, 65536, 1024 * 1024, 32, 2 * 1024 * 1024, 8];
    for (i, &sz) in sizes.iter().enumerate() {
        let payload = vec![(i % 255) as u8; sz];
        let res = session.eval_cell(&payload).expect("Eval cell should handle size");
        assert_eq!(res.len(), sz);
        assert_eq!(res[0], (i % 255) as u8);
        assert_eq!(res[sz - 1], (i % 255) as u8);
    }
}

#[test]
fn test_cabi_lowlevel_null_pointer_rejection() {
    unsafe {
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;

        // Null session handle
        assert_eq!(
            sys::obend_eval_cell(ptr::null_mut(), b"abc".as_ptr(), 3, &mut out_ptr, &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_turn_propose(ptr::null_mut(), b"abc".as_ptr(), 3, &mut out_ptr, &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_turn_commit(ptr::null_mut(), b"abc".as_ptr(), 32),
            -1
        );
        assert_eq!(
            sys::obend_project_hardware(ptr::null_mut(), b"abc".as_ptr(), 3, &mut out_ptr, &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_verify_receipt(ptr::null_mut(), b"abc".as_ptr(), 32),
            -1
        );
        assert_eq!(
            sys::obend_get_last_error(ptr::null_mut(), &mut out_ptr, &mut out_len),
            -1
        );

        // Null out pointers
        let sess = sys::obend_session_init(ptr::null(), 0);
        assert!(!sess.is_null());

        assert_eq!(
            sys::obend_eval_cell(sess, b"abc".as_ptr(), 3, ptr::null_mut(), &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_eval_cell(sess, b"abc".as_ptr(), 3, &mut out_ptr, ptr::null_mut()),
            -1
        );
        assert_eq!(
            sys::obend_turn_propose(sess, b"abc".as_ptr(), 3, ptr::null_mut(), &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_project_hardware(sess, b"abc".as_ptr(), 3, ptr::null_mut(), &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_get_last_error(sess, ptr::null_mut(), &mut out_len),
            -1
        );

        sys::obend_session_free(sess);
    }
}

#[test]
fn test_cabi_null_payload_pointer() {
    unsafe {
        let sess = sys::obend_session_init(ptr::null(), 0);
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0;
        // Providing null pointer with non-zero length:
        let rc = sys::obend_eval_cell(sess, ptr::null(), 16, &mut out_ptr, &mut out_len);
        assert_eq!(rc, -1, "Null payload pointer with non-zero length must return -1");
        sys::obend_session_free(sess);
    }
}

#[test]
fn test_cabi_session_free_null_is_safe() {
    unsafe {
        // Freeing null pointer must not crash
        sys::obend_session_free(ptr::null_mut());
    }
}

#[test]
fn test_cabi_concurrent_sessions_memory_corruption() {
    let handles: Vec<_> = (0..8)
        .map(|i| {
            thread::spawn(move || {
                let mut session = ObendSession::new().expect("Init session");
                for _ in 0..50 {
                    let payload = vec![i as u8; 1024 * (i + 1)];
                    let res = session.eval_cell(&payload).expect("Eval cell");
                    assert_eq!(res.len(), 1024 * (i + 1));
                    assert!(res.iter().all(|&b| b == i as u8));
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
