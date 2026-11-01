use obend_gui::{
    golden_cnc_5axis_waypoints, golden_openusd_prims, golden_stator_flowpipe_slices,
    golden_stator_telemetry, render_cnc_5axis_viewport, render_openusd_scene_viewport,
    render_physical_viewport, render_stator_multiphysics_viewport, DialResponse, EvalResponse,
    FieldRepairSuggestion, LawDialControl, LawDialMode, LeanBridgeResponse, NotebookStateResponse,
    PhysicalViewportKind, WorkbenchServer,
};

#[test]
fn test_ws30_physical_world_viewports_svg_html_ansi() {
    let dial = LawDialControl {
        cell_id: "cell-ws30".to_string(),
        mode: LawDialMode::Locked,
        invariant_expr: "T in [15.0, 35.0]".to_string(),
        margin_lo: 15.0,
        margin_hi: 35.0,
        current_value: 28.0,
    };

    // 1. 5-Axis CNC Kinematic Toolpath (Abbe compensation + Featherstone Coriolis W=0 + Ruckig S-curve)
    let waypoints = golden_cnc_5axis_waypoints();
    assert_eq!(waypoints.len(), 3);
    for wp in &waypoints {
        assert!(
            wp.is_abbe_exact_cancelled(),
            "Abbe 21-param compensation must cancel volumetric error at step {}",
            wp.step
        );
        assert!(
            wp.is_coriolis_workless(),
            "Featherstone Coriolis wrench must perform zero work at step {}",
            wp.step
        );
    }
    let cnc_vp = render_cnc_5axis_viewport("Hermle_C42U_5Axis", &waypoints, &dial);
    assert!(cnc_vp.svg.contains("data-projection=\"physical-cnc-5axis\""));
    assert!(cnc_vp.svg.contains("Abbe-Certified"));
    assert!(cnc_vp.svg.contains("abbe-error-vector"));
    assert!(cnc_vp.svg.contains("ruckig-scurve-vec"));
    assert!(cnc_vp.html_controls.contains("data-physical-kind=\"cnc_5axis\""));
    assert!(cnc_vp.terminal_canvas.contains("physical_cnc_5axis"));

    // 2. OpenUSD Scene Graph (SdfPath, LIVERPS relocates, AffineForm1D SDF intervals, timeSamples)
    let prims = golden_openusd_prims();
    assert_eq!(prims.len(), 3);
    assert_eq!(prims[0].sdf_interval_um(), (1475, 1525));
    let usd_vp = render_openusd_scene_viewport("LcDrives_Production_Stator", &prims, &dial);
    assert!(usd_vp.svg.contains("data-projection=\"physical-openusd-scene\""));
    assert!(usd_vp.svg.contains("/Factory/Draft/Stator/Slot01 -&gt; /Prod/LCDrives/Stator/Slot01"));
    assert!(usd_vp.svg.contains("data-self-cancel=\"[0,0]\""));
    assert!(usd_vp.html_controls.contains("data-physical-kind=\"openusd_scene\""));
    assert!(usd_vp.terminal_canvas.contains("physical_openusd_scene"));

    // 3. Coupled LC-Drive Stator Multiphysics (Darcy-Weisbach cooling + continuous ODE flowpipes)
    let telemetry = golden_stator_telemetry();
    let slices = golden_stator_flowpipe_slices();
    assert!(telemetry.is_multiphysics_certified());
    let stator_vp = render_stator_multiphysics_viewport(&telemetry, &slices, &dial);
    assert!(stator_vp.svg.contains("data-projection=\"physical-stator-multiphysics\""));
    assert!(stator_vp.svg.contains("MULTIPHYSICS_CERTIFIED"));
    assert!(stator_vp.svg.contains("flowpipe-box"));
    assert!(stator_vp.html_controls.contains("data-physical-kind=\"stator_multiphysics\""));
    assert!(stator_vp.terminal_canvas.contains("physical_stator_multiphysics"));

    // Verify generic dispatcher across all 3 PhysicalViewportKinds
    for kind in PhysicalViewportKind::ALL {
        let vp = render_physical_viewport(kind, "DispatchTest", &dial);
        assert!(vp.svg.starts_with("<svg"));
        assert!(vp.svg.ends_with("</svg>"));
    }
}

#[test]
fn test_ws31_workbench_server_notebook_and_dial_bellman_ford_sub5ms() {
    let server = WorkbenchServer::start_ephemeral().expect("Start ephemeral WorkbenchServer");
    assert_ne!(server.local_addr().port(), 0);

    // 1. GET /notebook
    let (status, body) = server
        .request("GET", "/notebook", None)
        .expect("GET /notebook");
    assert_eq!(status, 200);
    let nb: NotebookStateResponse = serde_json::from_str(&body).expect("Parse NotebookStateResponse");
    assert_eq!(nb.notebook_id, "obend-interactive-workbench.obnb");
    assert!(nb.html.contains("<!DOCTYPE html>"));
    assert!(nb.html.contains("Pop Out to Lean 4"));
    assert!(nb.cells.len() >= 4);

    // 2. POST /dial on coupled multi-field law in .press mode with violating write {a: 2, b: 1}
    let dial_payload = r#"{
        "cell_id": "cell-coupled-law",
        "mode": "press",
        "current_value": 2.0,
        "fields": { "a": 2, "b": 1 }
    }"#;
    let (status, body) = server
        .request("POST", "/dial", Some(dial_payload))
        .expect("POST /dial");
    assert_eq!(status, 200);
    let dial_resp: DialResponse = serde_json::from_str(&body).expect("Parse DialResponse");
    assert_eq!(dial_resp.cell_id, "cell-coupled-law");
    assert_eq!(dial_resp.mode, LawDialMode::Press);
    assert!(!dial_resp.admitted);
    assert_eq!(dial_resp.verdict, "PRESS_VIOLATION_REPAIR_SUGGESTED");
    assert!(
        dial_resp.elapsed_micros < 5_000,
        "POST /dial Bellman-Ford synthesis must complete in sub-5ms, took {} us",
        dial_resp.elapsed_micros
    );
    assert_eq!(
        dial_resp.repair_suggestions,
        vec![
            FieldRepairSuggestion {
                field: "a".to_string(),
                current_value: 2,
                suggested_value: 4,
            },
            FieldRepairSuggestion {
                field: "b".to_string(),
                current_value: 1,
                suggested_value: 4,
            },
        ]
    );
    assert_eq!(
        dial_resp.repair_summary.as_deref(),
        Some("the multi-field change `a = 4, b = 4` would pass")
    );

    // 3. Toggle to .free mode: exploratory excursion is admitted with FREE_WARNING
    let free_payload = r#"{
        "cell_id": "cell-coupled-law",
        "mode": "free",
        "current_value": 2.0,
        "fields": { "a": 2, "b": 1 }
    }"#;
    let (status, body) = server
        .request("POST", "/dial", Some(free_payload))
        .expect("POST /dial free");
    assert_eq!(status, 200);
    let free_resp: DialResponse = serde_json::from_str(&body).expect("Parse DialResponse");
    assert!(free_resp.admitted);
    assert_eq!(free_resp.verdict, "FREE_WARNING");

    // 4. Apply the suggested Bellman-Ford repair {a: 4, b: 4} in .locked mode -> ADMITTED
    let locked_payload = r#"{
        "cell_id": "cell-coupled-law",
        "mode": "locked",
        "current_value": 4.0,
        "fields": { "a": 4, "b": 4 }
    }"#;
    let (status, body) = server
        .request("POST", "/dial", Some(locked_payload))
        .expect("POST /dial locked");
    assert_eq!(status, 200);
    let locked_resp: DialResponse = serde_json::from_str(&body).expect("Parse DialResponse");
    assert!(locked_resp.admitted);
    assert_eq!(locked_resp.verdict, "ADMITTED");
    assert!(locked_resp.repair_suggestions.is_empty());
}

#[test]
fn test_ws31_eval_lean_bridge_weave_and_stale_pin_propagation() {
    let server = WorkbenchServer::start_ephemeral().expect("Start ephemeral WorkbenchServer");

    // 1. Pop Out to Lean 4 & Weave Certificate on `cell-cnc-5axis` (which depends on `cell-thermal-ode`)
    let bridge_req = r#"{
        "cell_id": "cell-cnc-5axis",
        "action": "pop_and_weave",
        "tactic": "obend_law",
        "verify_subprocess": true
    }"#;
    let (status, body) = server
        .request("POST", "/lean-bridge", Some(bridge_req))
        .expect("POST /lean-bridge");
    assert_eq!(status, 200);
    let bridge_resp: LeanBridgeResponse =
        serde_json::from_str(&body).expect("Parse LeanBridgeResponse");
    assert_eq!(bridge_resp.cell_id, "cell-cnc-5axis");
    assert!(bridge_resp.verified);
    assert_eq!(bridge_resp.tactic_used, "obend_law");
    assert_eq!(bridge_resp.cell_status, "certified");
    assert!(bridge_resp.lean_snippet.contains("import Obend.Tactic.Weave"));
    assert!(bridge_resp.lean_snippet.contains("obend_unfold"));
    assert!(bridge_resp.lean_snippet.contains("obend_law"));
    let cert = bridge_resp.woven_cert.expect("Expected woven certificate");
    assert_eq!(cert.justification, "byLoweredLean");
    assert_eq!(cert.receipt_hex.len(), 64);

    // 2. Scrub ODE parameter on upstream `cell-thermal-ode` via POST /eval
    let eval_req = r#"{
        "cell_id": "cell-thermal-ode",
        "parameter": "T",
        "value": 31.5
    }"#;
    let (status, body) = server
        .request("POST", "/eval", Some(eval_req))
        .expect("POST /eval");
    assert_eq!(status, 200);
    let eval_resp: EvalResponse = serde_json::from_str(&body).expect("Parse EvalResponse");
    assert_eq!(eval_resp.cell_id, "cell-thermal-ode");
    assert_eq!(eval_resp.status, "evaluated");
    assert_eq!(eval_resp.turn_receipt_hex.len(), 64);
    // Must re-render both `cell-thermal-ode` and downstream dependent `cell-cnc-5axis`
    assert!(eval_resp.rerendered_cells.contains(&"cell-thermal-ode".to_string()));
    assert!(eval_resp.rerendered_cells.contains(&"cell-cnc-5axis".to_string()));

    // 3. Verify `moved_pin_blocks` transitioned `cell-cnc-5axis` to `blocked (stale support: cell-thermal-ode)`
    let (_, nb_body) = server.request("GET", "/notebook", None).unwrap();
    let nb: NotebookStateResponse = serde_json::from_str(&nb_body).unwrap();
    let cnc_cell = nb
        .cells
        .iter()
        .find(|c| c.id == "cell-cnc-5axis")
        .expect("find cell-cnc-5axis");
    assert_eq!(
        cnc_cell.status,
        "blocked (stale support: cell-thermal-ode)"
    );

    // 4. Test `obend_tooth` counterexample synthesis when a cell violates its invariant
    let _ = server
        .request(
            "POST",
            "/dial",
            Some(r#"{"cell_id": "cell-thermal-ode", "mode": "press", "current_value": 48.0}"#),
        )
        .unwrap();
    let (status, tooth_body) = server
        .request(
            "POST",
            "/lean-bridge",
            Some(r#"{"cell_id": "cell-thermal-ode", "action": "pop_and_weave", "tactic": "obend_tooth"}"#),
        )
        .unwrap();
    assert_eq!(status, 200);
    let tooth_resp: LeanBridgeResponse = serde_json::from_str(&tooth_body).unwrap();
    assert_eq!(tooth_resp.tactic_used, "obend_tooth");
    assert!(!tooth_resp.verified);
    assert!(tooth_resp.tooth_counterexample.is_some());
    assert_eq!(
        tooth_resp
            .tooth_counterexample
            .as_ref()
            .unwrap()
            .get("violating_value"),
        Some(&48)
    );
}

#[test]
fn test_ws31_server_error_handling_and_parallel_ephemeral_ports() {
    let s1 = WorkbenchServer::start_ephemeral().expect("Server 1");
    let s2 = WorkbenchServer::start_ephemeral().expect("Server 2");
    assert_ne!(
        s1.local_addr().port(),
        s2.local_addr().port(),
        "Ephemeral ports on 127.0.0.1:0 must not collide"
    );

    // Unknown route -> 404
    let (status, _) = s1.request("GET", "/nonexistent", None).unwrap();
    assert_eq!(status, 404);

    // Unknown cell_id on /dial -> 404
    let (status, _) = s1
        .request(
            "POST",
            "/dial",
            Some(r#"{"cell_id": "missing-cell", "mode": "free"}"#),
        )
        .unwrap();
    assert_eq!(status, 404);

    // Malformed JSON on /eval -> 400
    let (status, _) = s1.request("POST", "/eval", Some("{bad_json")).unwrap();
    assert_eq!(status, 400);

    // Empty source on /eval -> 400
    let (status, _) = s1
        .request(
            "POST",
            "/eval",
            Some(r#"{"cell_id": "cell-thermal-ode", "source": "   "}"#),
        )
        .unwrap();
    assert_eq!(status, 400);
}

#[test]
fn test_ws30_cli_physical_viewport_subcommands() {
    let bin_path = env!("CARGO_BIN_EXE_obend-gui");
    for (kind, expected_marker) in [
        ("cnc_5axis", "physical_cnc_5axis"),
        ("openusd_scene", "physical_openusd_scene"),
        ("stator_multiphysics", "physical_stator_multiphysics"),
    ] {
        let output = std::process::Command::new(bin_path)
            .args(["viewport", "--kind", kind, "--title", "WS30-CLI-Test"])
            .output()
            .expect("Failed to execute obend-gui viewport command");
        assert!(
            output.status.success(),
            "CLI viewport --kind {kind} must succeed"
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains(expected_marker),
            "Expected {expected_marker} in stdout: {stdout}"
        );
    }
}

#[test]
fn test_ws31_unsatisfiable_negative_cycle_and_conflicting_bounds_refused() {
    use obend_gui::{evaluate_multi_field_admitted, suggest_multi_field_admits};
    use std::collections::BTreeMap;

    // 1. Negative cyclic difference constraint: `a < b && b < a` (`a <= b - 1 && b <= a - 1`)
    let neg_cycle_dial = LawDialControl {
        cell_id: "cell-neg-cycle".to_string(),
        mode: LawDialMode::Press,
        invariant_expr: "a < b && b < a".to_string(),
        margin_lo: 0.0,
        margin_hi: 10.0,
        current_value: 4.0,
    };
    let mut old_fields = BTreeMap::new();
    old_fields.insert("a".to_string(), 4);
    old_fields.insert("b".to_string(), 4);
    let new_fields = old_fields.clone();

    assert!(
        !evaluate_multi_field_admitted(&neg_cycle_dial, &old_fields, &new_fields),
        "Negative cycle `a < b && b < a` must never be admitted"
    );
    let (repairs, summary) =
        suggest_multi_field_admits(&neg_cycle_dial, &old_fields, &new_fields);
    assert!(
        repairs.is_empty(),
        "Unsatisfiable negative cycle must not emit a bogus repair suggestion"
    );
    assert_eq!(
        summary.as_deref(),
        Some("no change of one field passes")
    );

    // 2. Conflicting monotonicity + upper bound: `monotone(a) && a <= b && b <= 2` when `old.a = 4`
    let conflict_dial = LawDialControl {
        cell_id: "cell-conflict".to_string(),
        mode: LawDialMode::Press,
        invariant_expr: "monotone(a) && a <= b && b <= 2".to_string(),
        margin_lo: 0.0,
        margin_hi: 2.0,
        current_value: 2.0,
    };
    let mut old_conflict = BTreeMap::new();
    old_conflict.insert("a".to_string(), 4);
    old_conflict.insert("b".to_string(), 1);
    let mut new_conflict = BTreeMap::new();
    new_conflict.insert("a".to_string(), 2);
    new_conflict.insert("b".to_string(), 1);

    assert!(!evaluate_multi_field_admitted(
        &conflict_dial,
        &old_conflict,
        &new_conflict
    ));
    let (repairs2, summary2) =
        suggest_multi_field_admits(&conflict_dial, &old_conflict, &new_conflict);
    assert!(
        repairs2.is_empty(),
        "Conflicting `monotone(a)` (old=4) vs `b <= 2` must not emit a repair that violates `monotone(a)`"
    );
    assert_eq!(
        summary2.as_deref(),
        Some("no change of one field passes")
    );
}

#[test]
fn test_ws31_real_lean_subprocess_rejects_false_theorems_and_chunked_concurrent_http() {
    use std::io::{Read, Write};
    use std::net::TcpStream;
    use std::time::{Duration, Instant};

    let server = WorkbenchServer::start_ephemeral().expect("Start ephemeral server");

    // 1. Real `lean --stdin` subprocess verification must REJECT a false theorem `1 = 2`
    let false_bridge_req = r#"{
        "cell_id": "cell-cnc-5axis",
        "action": "pop_and_weave",
        "custom_lean_snippet": "theorem bogus_claim : (1 : Int) = 2 := by decide",
        "verify_subprocess": true
    }"#;
    let (status, body) = server
        .request("POST", "/lean-bridge", Some(false_bridge_req))
        .expect("POST /lean-bridge with false theorem");
    assert_eq!(status, 200);
    let false_resp: LeanBridgeResponse = serde_json::from_str(&body).unwrap();
    assert!(
        !false_resp.verified,
        "Real Lean 4 subprocess verification must reject `(1 : Int) = 2`"
    );
    assert!(false_resp.woven_cert.is_none());

    // 2. Invalid action on `/lean-bridge` -> 400 Bad Request
    let (status, _) = server
        .request(
            "POST",
            "/lean-bridge",
            Some(r#"{"cell_id": "cell-cnc-5axis", "action": "bogus_action"}"#),
        )
        .unwrap();
    assert_eq!(status, 400);

    // 3. Concurrent non-blocking HTTP connections: holding an idle socket open must not block a second client
    let _idle_stream = TcpStream::connect(server.local_addr()).expect("Open idle stream");
    let t0 = Instant::now();
    let (status, _) = server
        .request("GET", "/notebook", None)
        .expect("Concurrent GET /notebook");
    assert_eq!(status, 200);
    assert!(
        t0.elapsed() < Duration::from_millis(500),
        "Idle TCP client must not head-of-line block concurrent HTTP requests"
    );

    // 4. `Transfer-Encoding: chunked` request body on `POST /dial`
    let mut chunk_stream = TcpStream::connect(server.local_addr()).expect("Connect chunked");
    let payload = br#"{"cell_id":"cell-thermal-ode","mode":"press","current_value":27.0}"#;
    let chunk1 = &payload[..24];
    let chunk2 = &payload[24..];
    let raw_req = format!(
        "POST /dial HTTP/1.1\r\nHost: {}\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n{:x}\r\n{}\r\n{:x}\r\n{}\r\n0\r\n\r\n",
        server.local_addr(),
        chunk1.len(),
        std::str::from_utf8(chunk1).unwrap(),
        chunk2.len(),
        std::str::from_utf8(chunk2).unwrap(),
    );
    chunk_stream.write_all(raw_req.as_bytes()).unwrap();
    chunk_stream.flush().unwrap();
    let mut resp_buf = Vec::new();
    chunk_stream.read_to_end(&mut resp_buf).unwrap();
    let resp_str = String::from_utf8_lossy(&resp_buf);
    assert!(
        resp_str.starts_with("HTTP/1.1 200 OK"),
        "Chunked POST /dial must return 200 OK, got: {resp_str}"
    );
    let (_, json_body) = resp_str.split_once("\r\n\r\n").unwrap();
    let dial_resp: DialResponse = serde_json::from_str(json_body).unwrap();
    assert!(dial_resp.admitted);

    // 5. Physical viewport violation badges when `LawDialControl` is out of bounds (`Cnc5Axis`, `OpenUsdScene`, `StatorMultiphysics`)
    let violating_cnc_dial = LawDialControl {
        cell_id: "cell-cnc-5axis".to_string(),
        mode: LawDialMode::Locked,
        invariant_expr: "abbe_err_nm in [0.0, 5.0]".to_string(),
        margin_lo: 0.0,
        margin_hi: 5.0,
        current_value: 45.0,
    };
    let cnc_viol_vp = render_physical_viewport(
        PhysicalViewportKind::Cnc5Axis,
        "Hermle_C42U_5Axis",
        &violating_cnc_dial,
    );
    assert!(cnc_viol_vp.svg.contains("Abbe-Uncompensated"));

    let violating_usd_dial = LawDialControl {
        cell_id: "cell-openusd-sdf".to_string(),
        mode: LawDialMode::Locked,
        invariant_expr: "wall_um in [1200.0, 5000.0]".to_string(),
        margin_lo: 1200.0,
        margin_hi: 5000.0,
        current_value: 50.0, // < 100.0 and < 1200.0
    };
    let usd_viol_vp = render_physical_viewport(
        PhysicalViewportKind::OpenUsdScene,
        "LcDrives_Production_Stator",
        &violating_usd_dial,
    );
    assert!(usd_viol_vp.svg.contains("LCA VIOLATION"));
}

