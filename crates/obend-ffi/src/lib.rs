pub mod error;
pub mod pool;
pub mod session;
pub mod sys;

pub use error::ObendError;
pub use pool::{ensure_lean_thread_initialized, LeanWorkerPool};
pub use session::ObendSession;

/// Propose `turn_bytes` via `session.propose_turn` and immediately commit the returned
/// 32-byte proposal receipt via `session.commit_turn`, returning the committed 32-byte turn root.
///
/// `Bridge.lean` (`turnCommitCore_unproposed_tid_refused`) commits only an id it proposed, and
/// only `turnCommitCore` writes `committedRoots`; the receipt a verifier accepts is the frame
/// `ObendSession::commit_payload` returns, never the bare id.
pub fn propose_and_commit_turn(
    session: &mut ObendSession,
    turn_bytes: &[u8],
) -> Result<Vec<u8>, ObendError> {
    let tid = session.propose_turn(turn_bytes)?;
    session.commit_turn(&tid)?;
    Ok(tid)
}

/// `true` when this crate was linked against the Lean library (`lean/.lake/build/lib`), the
/// default; `false` when it was built with `OBEND_ALLOW_STUB_FFI=1` (or the `stub` feature), in
/// which case every verify and weave returns `ObendError::StubBackend` and a test that needs the
/// kernel's judgement should say so rather than fail on the refusal.
pub fn kernel_is_native() -> bool {
    !cfg!(feature = "stub")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_propose_and_commit_turn_admits_receipt() {
        let mut session = ObendSession::new().expect("init session");
        let tid =
            propose_and_commit_turn(&mut session, b"cell_alpha=42").expect("propose and commit");
        assert_eq!(tid.len(), 32);
        // A bare id is not a receipt: the verifier needs the frame with the payload it opens.
        assert!(!session.verify_receipt(&tid).expect("bare id"));
        let receipt = session.commit_payload(b"cell_alpha=42").expect("commit payload");
        assert!(session.verify_receipt(&receipt).expect("verify committed frame"));
    }

    #[test]
    fn test_invalid_turn_id_length_refused() {
        let mut session = ObendSession::new().expect("init session");
        assert!(session.commit_turn(&[0xAA; 16]).is_err());
        assert!(!session.verify_receipt(&[0xBB; 16]).expect("short receipt"));
    }
}
