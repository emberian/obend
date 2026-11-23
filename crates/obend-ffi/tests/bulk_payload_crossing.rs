//! The workbook entry points hand Lean each request in one bulk copy
//! (`obend_mk_byte_array_from_slice`, `lean/c/obend_bridge.c`). Lean's own answers show which
//! bytes it received, at lengths where an empty, truncated or shifted copy would differ.

use obend_ffi::{kernel_is_native, ObendError, ObendSession};

const NOT_UTF8: &str = "Workbook step payload is not valid UTF-8";

fn refusal(session: &mut ObendSession, payload: &[u8]) -> String {
    match session.step_workbook(payload) {
        Err(ObendError::WithDetail(code, why)) if *code == ObendError::DecodeFailed => why,
        other => panic!("expected a decode refusal, got {other:?}"),
    }
}

/// An `init` request of exactly `total` bytes whose title holds one-, two-, three- and
/// four-byte UTF-8 characters.
fn init_request(total: usize) -> (Vec<u8>, String) {
    let (head, tail) = (r#"{"op":"init","title":""#, r#"","cells":[]}"#);
    let room = total - head.len() - tail.len();
    let mut title = String::new();
    for c in ['a', 'λ', '€', '🜂', '~', '0'].iter().cycle() {
        if title.len() + c.len_utf8() > room {
            break;
        }
        title.push(*c);
    }
    while title.len() < room {
        title.push('.');
    }
    let request = [head, title.as_str(), tail].concat().into_bytes();
    assert_eq!(request.len(), total);
    (request, title)
}

#[test]
fn workbook_step_receives_every_request_byte() {
    let mut session = ObendSession::new().expect("init session");
    if !kernel_is_native() {
        return;
    }
    assert_eq!(refusal(&mut session, b""), "Empty workbook step payload");
    assert_eq!(refusal(&mut session, &[0x80]), NOT_UTF8);
    assert!(refusal(&mut session, b"{").starts_with("Invalid workbook step JSON"));

    // Only the final byte of each is outside UTF-8.
    for len in [32, 64 * 1024] {
        let mut payload = vec![b' '; len - 1];
        payload.push(0xff);
        assert_eq!(refusal(&mut session, &payload), NOT_UTF8, "{len} bytes");
    }

    let (request, title) = init_request(64 * 1024);
    let reply = session.step_workbook(&request).expect("64 KiB init");
    let reply: serde_json::Value = serde_json::from_slice(&reply).expect("reply is JSON");
    assert_eq!(reply["status"], "accepted");
    assert_eq!(reply["title"], title.as_str());
}
