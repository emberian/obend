//! "obend-node is an in-process simulator of the Lean theorems" as a checked sentence
//! (2026-11-04): the cluster emits its run as a trace in the message shape of
//! `lean/Obend/Consensus/SimplexProtocol.lean`, and the Lean kernel's `simplex-trace@1` judge
//! (`Obend.Consensus.SimplexTrace.checkTrace`, sound for `Reach`) decides whether every message
//! was a step of the relation. These tests need the Lean library; under the opt-in stub they say
//! so and stop.

use obend_ffi::ObendSession;
use obend_node::{
    judge_witness_wire, ConsensusNetMessage, IpcAuth, SignedSimplexVote, SimplexCluster,
    SimplexVoteKind, TransportProtocol, VaultCellRecord, VaultTurn,
};

fn genesis() -> Vec<VaultCellRecord> {
    vec![
        VaultCellRecord {
            id: 1,
            required: vec![IpcAuth::Read],
            salt: [0x11; 32],
            content: b"slot-1-genesis".to_vec(),
        },
        VaultCellRecord {
            id: 2,
            required: vec![IpcAuth::Read],
            salt: [0x22; 32],
            content: b"slot-2-genesis".to_vec(),
        },
    ]
}

/// The `simplex-trace@1` witness of the run so far, declaring `faulty` as the faulty set.
fn witness(cluster: &SimplexCluster, faulty: &[usize]) -> Vec<u8> {
    judge_witness_wire(
        "simplex-trace",
        "1",
        1,
        &cluster.protocol_json(faulty),
        &cluster.trace_json(),
    )
}

fn kernel() -> bool {
    if !obend_ffi::kernel_is_native() {
        eprintln!("skipped: the trace is judged by the Lean kernel; the stub FFI has no judge registry");
        return false;
    }
    true
}

/// An honest run of two blocks is a reachable trace: every proposal is the leader's, every vote
/// is one per view on notarized ground, every finalize vote follows a notarization.
#[test]
fn honest_run_trace_is_reachable_by_the_kernel() {
    if !kernel() {
        return;
    }
    let mut cluster = SimplexCluster::with_transport(4, 1, genesis(), TransportProtocol::Tcp)
        .expect("spawn 4-validator cluster");
    for (h, name) in [(1u8, "alice"), (2u8, "bob")] {
        let turn = VaultTurn::new(
            [h; 32],
            name,
            vec![h as u64],
            vec![(h as u64, format!("slot-{h}").into_bytes())],
        );
        cluster.stage_contended_or_inflight_turn(turn).expect("stage turn");
        let blk = cluster.run_simplex_block().expect("finalize block");
        assert_eq!(blk.height, h as u64);
    }
    let trace = cluster.trace_json();
    assert!(trace.contains("\"kind\":\"propose\""), "{trace}");
    assert!(trace.contains("\"kind\":\"vote\""), "{trace}");
    assert!(trace.contains("\"kind\":\"finalize\""), "{trace}");

    let mut session = ObendSession::new().expect("session");
    let tid = session
        .weave_cert(&witness(&cluster, &[]))
        .unwrap_or_else(|e| panic!("the honest run must be a reachable trace: {e}\n{trace}"));
    assert_eq!(tid.len(), 32);
    session.commit_turn(&tid).expect("commit the woven turn");
}

/// A node that votes for two blocks in one view. Node 3 votes honestly for view 2's proposal,
/// then sends one more vote in view 2 for another block. With no node declared faulty the trace
/// is refused at that vote and the refusal names the slashing receipt (the two votes, the view,
/// the signer); declared faulty, the same messages are the adversary's injections and the run is
/// reachable.
#[test]
fn injected_conflicting_votes_are_refused_naming_the_slashing_receipt() {
    if !kernel() {
        return;
    }
    let mut cluster = SimplexCluster::with_transport(4, 1, genesis(), TransportProtocol::Tcp)
        .expect("spawn 4-validator cluster");
    for (h, name) in [(1u8, "alice"), (2u8, "bob")] {
        let turn = VaultTurn::new(
            [h; 32],
            name,
            vec![h as u64],
            vec![(h as u64, format!("slot-{h}").into_bytes())],
        );
        cluster.stage_contended_or_inflight_turn(turn).expect("stage turn");
        let blk = cluster.run_simplex_block().expect("finalize block");
        assert_eq!(blk.view, h as u64);
    }

    // Node 3 voted for view 2's block above; now it votes in view 2 for another block.
    let conflicting = SignedSimplexVote::new(
        &cluster.nodes[3].keypair,
        2,
        SimplexVoteKind::Vote,
        [0xBB; 32],
    );
    cluster.nodes[3]
        .broadcast(ConsensusNetMessage::Vote(conflicting))
        .expect("broadcast the conflicting vote");

    let mut session = ObendSession::new().expect("session");
    let err = session
        .weave_cert(&witness(&cluster, &[]))
        .expect_err("with no node declared faulty, two votes in one view are not a step");
    let detail = err.to_string();
    assert!(detail.contains("equivocation"), "{detail}");
    assert!(detail.contains("signers := [3]"), "{detail}");
    assert!(detail.contains("view := 2"), "{detail}");

    session
        .weave_cert(&witness(&cluster, &[3]))
        .unwrap_or_else(|e| panic!("with node 3 declared faulty the trace must be reachable: {e}"));
}
