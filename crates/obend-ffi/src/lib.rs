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
        if !kernel_is_native() {
            assert!(session.verify_receipt(&tid).is_err());
            return;
        }
        // A bare id is not a receipt: the verifier needs the frame with the payload it opens.
        assert!(!session.verify_receipt(&tid).expect("bare id"));
        let receipt = session.commit_payload(b"cell_alpha=42").expect("commit payload");
        assert!(session.verify_receipt(&receipt).expect("verify committed frame"));
    }

    #[test]
    fn test_invalid_turn_id_length_refused() {
        let mut session = ObendSession::new().expect("init session");
        assert!(session.commit_turn(&[0xAA; 16]).is_err());
        if !kernel_is_native() {
            assert!(session.verify_receipt(&[0xBB; 16]).is_err());
            return;
        }
        assert!(!session.verify_receipt(&[0xBB; 16]).expect("short receipt"));
    }

    #[test]
    fn test_workbook_step_and_scrub_ffi_roundtrip_and_refusals() {
        let mut session = ObendSession::new().expect("init session");
        assert!(session.step_workbook(b"").is_err());
        assert!(session.scrub_projection_cell(b"").is_err());

        if !kernel_is_native() {
            assert_eq!(
                session.step_workbook(br#"{"op":"init","cells":[]}"#),
                Err(ObendError::WithDetail(
                    Box::new(ObendError::StubBackend),
                    "stub FFI: no Lean kernel is linked (built with OBEND_ALLOW_STUB_FFI); nothing is verified here".to_string()
                ))
            );
            return;
        }

        // Corrupted JSON and cyclic DAGs fail closed
        assert!(session.step_workbook(b"{not valid json").is_err());
        let cyclic_init = br#"{
            "op":"init",
            "title":"CyclicTest",
            "cells":[
                {"cellKey":"self_loop","id":1,"kind":"pcbMultiphysicsDfm","note":"![[self_loop]]","literalValue":10}
            ]
        }"#;
        assert!(session.step_workbook(cyclic_init).is_err());

        // Valid multi-projection workbook init + bidirectional scrub + read-only badge refusal
        let init_req = br#"{
            "op":"init",
            "title":"PcbAndPdeWorkbook",
            "sections":[{"sectionKey":"BoardSpec","markdown":"Baseline board","blocks":[["margin",5]]}],
            "cells":[
                {
                    "cellKey":"pcb_cell",
                    "id":1,
                    "kind":"pcbMultiphysicsDfm",
                    "fields":{"traceWidthUm":150,"clearanceUm":120,"drcVerified":true},
                    "defs":["trace_w"],
                    "literalValue":150
                },
                {
                    "cellKey":"pde_cell",
                    "id":2,
                    "kind":"pdeConservation",
                    "fields":{"cflMilli":800,"entropyResidual":0},
                    "reads":["trace_w"],
                    "defs":["scaled_w"],
                    "body":[[{"op":"input","arg":0},{"op":"literal","arg":2},{"op":"mul","arg":0}]]
                },
                {
                    "cellKey":"unrelated_cell",
                    "id":3,
                    "kind":"zkCustodyReceipt",
                    "fields":{"epochLimit":10,"custodyProof":true},
                    "defs":["epoch_out"],
                    "literalValue":10
                }
            ]
        }"#;
        let init_bytes = session.step_workbook(init_req).expect("init workbook");
        let init_json: serde_json::Value = serde_json::from_slice(&init_bytes).unwrap();
        assert_eq!(init_json["status"], "accepted");
        assert_eq!(init_json["cellCount"], 3);
        assert_eq!(init_json["cells"][1]["values"][0], 300);
        let clean_receipt_before = init_json["cells"][2]["receiptHex"].as_str().unwrap().to_string();

        // Scrubbing a read-only proof badge MUST fail closed (`TurnRefused`)
        let bad_scrub = br#"{"cellKey":"pcb_cell","fieldName":"drcVerified","newValue":false}"#;
        let bad_err = session.scrub_projection_cell(bad_scrub).unwrap_err();
        assert!(format!("{bad_err}").contains("read-only"));

        // Scrubbing editable `traceWidthUm` updates `pcb_cell` (id 1) and downstream `pde_cell` (id 2),
        // while `unrelated_cell` (id 3) stays outside `dirtyCone` with its exact cached 256-bit receipt!
        let ok_scrub = br#"{"cellKey":"pcb_cell","fieldName":"traceWidthUm","newValue":200}"#;
        let scrub_bytes = session.scrub_projection_cell(ok_scrub).expect("scrub traceWidthUm");
        let scrub_json: serde_json::Value = serde_json::from_slice(&scrub_bytes).unwrap();
        assert_eq!(scrub_json["status"], "accepted");
        assert_eq!(scrub_json["dirtyCone"], serde_json::json!([1, 2]));
        assert_eq!(scrub_json["cells"][0]["values"][0], 200);
        assert_eq!(scrub_json["cells"][1]["values"][0], 400);
        assert_eq!(scrub_json["cells"][2]["receiptHex"], clean_receipt_before);
    }
}
