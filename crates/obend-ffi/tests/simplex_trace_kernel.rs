//! End-to-end Rust FFI tests for the Lean `simplex-trace@1` certificate judge
//! (`Obend.Consensus.SimplexTrace.simplexTraceFormat`) through `ObendSession::weave_cert`
//! and `ObendSession::commit_turn`.

use obend_ffi::session::{encode_receipt, ObendSession};
use serde_json::{json, Value};

fn block_entry(view: u64, payload: u64) -> Value {
    json!({ "block": { "view": view, "payload": payload } })
}

fn msg_block(sender: u64, view: u64, kind: &str, chain: &[Value]) -> Value {
    json!({
        "sender": sender,
        "view": view,
        "kind": kind,
        "target": { "block": chain }
    })
}

fn msg_dummy(sender: u64, view: u64, kind: &str, dummy_view: u64) -> Value {
    json!({
        "sender": sender,
        "view": view,
        "kind": kind,
        "target": { "dummy": dummy_view }
    })
}

fn wrap_simplex_witness(committee: &[u64], f: u64, faulty: &[u64], trace: &[Value]) -> Vec<u8> {
    let obj = json!({
        "committee": committee,
        "f": f,
        "faulty": faulty,
    })
    .to_string();
    let cert = Value::Array(trace.to_vec()).to_string();
    json!({
        "format": "simplex-trace",
        "version": "1",
        "grade": 0,
        "obj": obj,
        "cert": cert,
    })
    .to_string()
    .into_bytes()
}

fn honest_two_view_trace() -> Vec<Value> {
    let c1 = vec![block_entry(1, 101)];
    let c2 = vec![block_entry(1, 101), block_entry(2, 202)];
    vec![
        // View 1: leader = committee[(1 - 1) % 4] = 0
        msg_block(0, 1, "propose", &c1),
        msg_block(0, 1, "vote", &c1),
        msg_block(1, 1, "vote", &c1),
        msg_block(2, 1, "vote", &c1),
        msg_block(0, 1, "finalize", &c1),
        msg_block(1, 1, "finalize", &c1),
        msg_block(2, 1, "finalize", &c1),
        // View 2: leader = committee[(2 - 1) % 4] = 1
        msg_block(1, 2, "propose", &c2),
        msg_block(0, 2, "vote", &c2),
        msg_block(1, 2, "vote", &c2),
        msg_block(3, 2, "vote", &c2),
        msg_block(0, 2, "finalize", &c2),
        msg_block(1, 2, "finalize", &c2),
        msg_block(3, 2, "finalize", &c2),
    ]
}

#[cfg(not(feature = "stub"))]
#[test]
fn honest_four_validator_multi_view_trace_weaves_commits_and_opens_receipt() {
    let mut session = ObendSession::new().expect("session");
    let trace = honest_two_view_trace();
    let witness = wrap_simplex_witness(&[0, 1, 2, 3], 1, &[], &trace);

    let tid = session
        .weave_cert(&witness)
        .expect("Lean kernel accepts reachable multi-view Simplex trace");
    assert_eq!(tid.len(), 32);

    let receipt = encode_receipt(&tid, 1, 0, &[], &witness);
    assert!(
        !session.verify_receipt(&receipt).unwrap(),
        "proposal alone must not verify before commit"
    );

    session.commit_turn(&tid).expect("commit woven Simplex turn");
    assert!(
        session.verify_receipt(&receipt).unwrap(),
        "committed Simplex trace witness opens against session root"
    );
}

#[cfg(not(feature = "stub"))]
#[test]
fn equivocating_second_vote_is_slashed_when_undeclared_and_accepted_when_declared_faulty() {
    let mut session = ObendSession::new().expect("session");
    let mut trace = honest_two_view_trace();
    // Node 3 already voted for `c2` in view 2; casting a conflicting dummy vote in view 2 is equivocation.
    trace.push(msg_dummy(3, 2, "vote", 2));

    let undeclared = wrap_simplex_witness(&[0, 1, 2, 3], 1, &[], &trace);
    let err = session
        .weave_cert(&undeclared)
        .expect_err("undeclared equivocation must be refused by checkTrace")
        .to_string();
    assert!(
        err.contains("equivocation") && err.contains("[3]") && err.contains("view 2"),
        "expected slashing receipt detail naming node [3] in view 2, got: {err}"
    );

    // Declaring node 3 faulty (`|faulty| = 1 <= f = 1`) models adversarial injection (`Step.inject`).
    let declared = wrap_simplex_witness(&[0, 1, 2, 3], 1, &[3], &trace);
    let tid = session
        .weave_cert(&declared)
        .expect("same trace is reachable when node 3 is in the declared faulty set");
    session.commit_turn(&tid).expect("commit declared-faulty trace");
}

#[cfg(not(feature = "stub"))]
#[test]
fn unknown_sender_and_non_leader_proposals_fail_closed() {
    let mut session = ObendSession::new().expect("session");

    // Planted bad trace: sender 7 outside committee [0, 1, 2, 3].
    let unknown = wrap_simplex_witness(&[0, 1, 2, 3], 1, &[], &[msg_dummy(7, 1, "vote", 1)]);
    let err_unknown = session
        .weave_cert(&unknown)
        .expect_err("sender 7 must be refused")
        .to_string();
    assert!(
        err_unknown.contains("node 7"),
        "expected unknown-sender detail, got: {err_unknown}"
    );

    // Node 2 is not leader of view 1 (leader is 0).
    let c1 = vec![block_entry(1, 999)];
    let non_leader = wrap_simplex_witness(&[0, 1, 2, 3], 1, &[], &[msg_block(2, 1, "propose", &c1)]);
    let err_leader = session
        .weave_cert(&non_leader)
        .expect_err("non-leader proposal must be refused")
        .to_string();
    assert!(
        err_leader.contains("not its leader"),
        "expected non-leader detail, got: {err_leader}"
    );
}
