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
/// This enforces the `Bridge.lean` (`turnCommitCore_unproposed_tid_refused`) invariant that every
/// committed turn ID must first be proposed in `pendingProposals` and admitted into `admittedRoots`.
pub fn propose_and_commit_turn(
    session: &mut ObendSession,
    turn_bytes: &[u8],
) -> Result<Vec<u8>, ObendError> {
    let tid = session.propose_turn(turn_bytes)?;
    session.commit_turn(&tid)?;
    Ok(tid)
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
        assert!(session.verify_receipt(&tid).expect("verify admitted tid"));
    }

    #[test]
    fn test_invalid_turn_id_length_refused() {
        let mut session = ObendSession::new().expect("init session");
        assert!(session.commit_turn(&[0xAA; 16]).is_err());
        assert!(!session.verify_receipt(&[0xBB; 16]).expect("short receipt"));
    }
}
