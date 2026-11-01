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
