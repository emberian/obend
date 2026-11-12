//! Receipts are bound to the session that committed them, and nothing is admitted by being
//! proposed, hashed, or merely 32 bytes long (`turnProposeCore_committedRoots_unchanged`,
//! `verifyReceiptCore_sound`).

use obend_ffi::session::{encode_receipt, ObendSession};

#[test]
fn proposed_but_uncommitted_root_is_refused() {
    let mut session = ObendSession::new().expect("session");
    let payload = b"a turn that is proposed and never committed";
    let tid = session.propose_turn(payload).expect("propose");
    assert_eq!(tid.len(), 32);
    // The old path: proposing admitted the id and the payload as roots.
    let one_leaf = encode_receipt(&tid, 1, 0, &[], payload);
    assert!(!session.verify_receipt(&one_leaf).unwrap(), "a proposal admits no root");
    assert!(!session.verify_receipt(&tid).unwrap(), "a bare 32-byte root is not a receipt");
    assert!(!session.verify_receipt(payload).unwrap(), "the payload itself is not a receipt");
}

#[test]
fn committed_receipt_verifies_and_binds_its_payload() {
    let mut session = ObendSession::new().expect("session");
    let payload = b"the committed turn";
    let receipt = session.commit_payload(payload).expect("commit");
    assert!(session.verify_receipt(&receipt).unwrap());

    // The root alone, with no opening, is refused.
    assert!(!session.verify_receipt(&receipt[..32]).unwrap());
    // The frame with another payload under the same root is refused: the digest moved.
    let forged = encode_receipt(&receipt[..32], 1, 0, &[], b"another payload");
    assert!(!session.verify_receipt(&forged).unwrap());
    // A claimed position other than the committed one-leaf map is refused.
    let wrong_index = encode_receipt(&receipt[..32], 2, 1, &[], payload);
    assert!(!session.verify_receipt(&wrong_index).unwrap());
    // Truncated frames are refused.
    assert!(!session.verify_receipt(&receipt[..55]).unwrap());
    assert!(!session.verify_receipt(&[]).unwrap());
}

#[test]
fn receipt_is_bound_to_the_committing_session() {
    let mut a = ObendSession::new().expect("session a");
    let mut b = ObendSession::new().expect("session b");
    let receipt = a.commit_payload(b"committed in a").expect("commit");
    assert!(a.verify_receipt(&receipt).unwrap());
    assert!(!b.verify_receipt(&receipt).unwrap(), "b committed nothing");
    // b can re-derive the same receipt only by committing the same payload itself.
    let again = b.commit_payload(b"committed in a").expect("commit in b");
    assert_eq!(again, receipt, "the receipt is a function of the payload and the kernel's hash");
    assert!(b.verify_receipt(&again).unwrap());
}

#[test]
fn weave_refuses_anything_that_is_not_an_accepted_witness() {
    let mut session = ObendSession::new().expect("session");
    // Lean theorem text used to pass a prose gate; it is not a judge witness.
    let theorem = b"theorem cell_1_contract : (15 \xe2\x89\xa4 (28 : Int) \xe2\x88\xa7 (28 : Int) \xe2\x89\xa4 35) := by\n  obend_law\n";
    assert!(session.weave_cert(theorem).is_err());
    // A witness naming an unregistered format is refused.
    let unknown = br#"{"format":"no-such-format","version":"1","grade":1,"obj":"x","cert":"y"}"#;
    assert!(session.weave_cert(unknown).is_err());
    // A witness whose registered format refuses the certificate is refused: the planted bad
    // LRAT certificate of `Obend.Judge.Lrat.format` (clause 3 cites hints [1, 1]).
    let planted = br#"{"format":"lrat","version":"1","grade":1,"obj":"p cnf 1 2\n1 0\n-1 0\n","cert":"3 0 1 1 0\n"}"#;
    assert!(session.weave_cert(planted).is_err());
    // Nothing above left a committable proposal or a verifiable root.
    assert!(!session.verify_receipt(&[0u8; 80]).unwrap());
}

/// Only the native bridge has a judge registry; the stub refuses every weave.
#[cfg(not(feature = "stub"))]
#[test]
fn weave_of_an_accepted_lrat_witness_commits_a_turn_carrying_it() {
    let mut session = ObendSession::new().expect("session");
    // `p cnf 1 2; 1; -1` is refuted by resolving the two units: LRAT step `3 0 1 2 0`.
    let witness = br#"{"format":"lrat","version":"1","grade":4,"obj":"p cnf 1 2\n1 0\n-1 0\n","cert":"3 0 1 2 0\n"}"#;
    let tid = session.weave_cert(witness).expect("an accepted witness is proposed");
    assert_eq!(tid.len(), 32);
    // Proposed, not yet committed: its receipt does not verify.
    let receipt = encode_receipt(&tid, 1, 0, &[], witness);
    assert!(!session.verify_receipt(&receipt).unwrap());
    // Committing builds the `VaultTurn` with the witness in `witnesses` (checked again by
    // `checkTurnWitness` at commit) and records the root.
    session.commit_turn(&tid).expect("commit the woven turn");
    assert!(session.verify_receipt(&receipt).unwrap());
}
