use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use obend_ffi::sys;
use serde_json::Value;
use std::ptr;
use std::thread;

fn build_padded_obend_cell(value: usize, min_bytes: usize) -> Vec<u8> {
    let mut text = format!(
        "edition ObjectiveBend 1\ndef cellValue() -> Nat:\n  {value}n\n"
    );
    while text.len() < min_bytes {
        let pad_len = (min_bytes - text.len()).min(120);
        text.push('#');
        for _ in 1..pad_len.saturating_sub(1) {
            text.push('x');
        }
        text.push('\n');
    }
    text.into_bytes()
}

#[test]
fn test_cabi_zero_length_and_non_obend_buffers() {
    let mut session = ObendSession::new().expect("Init session");

    let res_cell = session.eval_cell(&[]);
    assert!(res_cell.is_err());
    match res_cell.err().unwrap() {
        ObendError::DecodeFailed | ObendError::WithDetail(_, _) => {}
        other => panic!("Expected DecodeFailed, got {:?}", other),
    }

    // Non-.obend UTF-8 and invalid UTF-8 slices must fail closed.
    assert!(session.eval_cell(b"plain non-obend text").is_err());
    assert!(session.eval_cell(&[0xff, 0xfe, 0xfd]).is_err());

    assert!(session.propose_turn(&[]).is_err());
    assert!(session.project_hardware(&[]).is_err());
    assert_eq!(session.verify_receipt(&[]).unwrap(), false);
    assert!(session.commit_turn(&[]).is_err());
}

#[test]
fn test_cabi_truncated_and_invalid_turn_commits() {
    let mut session = ObendSession::new().expect("Init session");

    for len in [1, 7, 16, 31, 33, 64, 128] {
        let invalid_id = vec![0xAA; len];
        let res = session.commit_turn(&invalid_id);
        assert!(res.is_err(), "Length {} should be rejected", len);
    }

    let unproposed_id = vec![0xBB; 32];
    assert!(session.commit_turn(&unproposed_id).is_err());

    let proposed_id = session
        .propose_turn(b"valid_turn_payload")
        .expect("propose_turn");
    assert_eq!(proposed_id.len(), 32);
    assert!(session.commit_turn(&proposed_id).is_ok());
}

#[test]
fn test_cabi_truncated_receipts() {
    let mut session = ObendSession::new().expect("Init session");

    for len in [1, 15, 31] {
        let malformed = vec![0xCC; len];
        assert_eq!(session.verify_receipt(&malformed).unwrap(), false);
    }

    assert_eq!(session.verify_receipt(&vec![0xDD; 32]).unwrap(), false);
    assert_eq!(session.verify_receipt(&vec![0xEE; 128]).unwrap(), false);

    let tid = session.propose_turn(b"receipt_payload").expect("propose_turn");
    assert_eq!(session.verify_receipt(&tid).unwrap(), false);
    let committed = session
        .commit_payload(b"receipt_payload")
        .expect("commit_payload");
    assert_eq!(session.verify_receipt(&committed).unwrap(), true);
    let mut extended = committed.clone();
    extended.extend_from_slice(&[0xEE; 96]);
    assert_eq!(session.verify_receipt(&extended).unwrap(), false);
}

#[test]
fn test_cabi_oversized_buffers_and_scratch_realloc() {
    let mut session = ObendSession::new().expect("Init session");

    let sizes = [64, 1024, 16384, 65536, 128];
    for (i, &sz) in sizes.iter().enumerate() {
        let payload = build_padded_obend_cell(i + 1, sz);
        let res = session
            .eval_cell(&payload)
            .expect("Eval valid .obend cell across scratch reallocations");
        let parsed: Value = serde_json::from_slice(&res).expect("valid elaboration JSON");
        assert_eq!(parsed["status"], "accepted");
    }
}

#[test]
fn test_cabi_lowlevel_null_pointer_rejection() {
    unsafe {
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;

        assert_eq!(
            sys::obend_eval_cell(ptr::null_mut(), b"abc".as_ptr(), 3, &mut out_ptr, &mut out_len),
            -1
        );
        assert_eq!(
            sys::obend_turn_propose(
                ptr::null_mut(),
                b"abc".as_ptr(),
                3,
                &mut out_ptr,
                &mut out_len
            ),
            -1
        );
        assert_eq!(
            sys::obend_turn_commit(ptr::null_mut(), b"abc".as_ptr(), 32),
            -1
        );
        assert_eq!(
            sys::obend_project_hardware(
                ptr::null_mut(),
                b"abc".as_ptr(),
                3,
                &mut out_ptr,
                &mut out_len
            ),
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
        let rc = sys::obend_eval_cell(sess, ptr::null(), 16, &mut out_ptr, &mut out_len);
        assert_eq!(
            rc, -1,
            "Null payload pointer with non-zero length must return -1"
        );
        sys::obend_session_free(sess);
    }
}

#[test]
fn test_cabi_session_free_null_is_safe() {
    unsafe {
        sys::obend_session_free(ptr::null_mut());
    }
}

#[test]
fn test_cabi_concurrent_sessions_memory_corruption() {
    let handles: Vec<_> = (0..4)
        .map(|i| {
            thread::spawn(move || {
                let mut session = ObendSession::new().expect("Init session");
                for step in 0..8 {
                    let payload = build_padded_obend_cell(i * 100 + step, 256 * (i + 1));
                    let res = session.eval_cell(&payload).expect("Eval .obend cell");
                    let parsed: Value = serde_json::from_slice(&res).expect("JSON");
                    assert_eq!(parsed["status"], "accepted");
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
