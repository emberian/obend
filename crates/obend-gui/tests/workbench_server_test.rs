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

#[test]
fn test_literate_pide_workbench_spa_and_surgical_slider_dom_update() {
    let server = WorkbenchServer::start_ephemeral().expect("Start ephemeral WorkbenchServer");

    // 1. GET / must serve the Literate .obend Workbook & PIDE Explorer as Tab 1 default experience
    let (status, html) = server.request("GET", "/", None).expect("GET /");
    assert_eq!(status, 200);
    assert!(html.contains("<!DOCTYPE html>"));
    assert!(html.contains("1. Literate .obend Workbook &amp; PIDE Explorer"));
    assert!(html.contains("workspace-file-tree"));
    assert!(html.contains("pide-source-editor"));
    assert!(html.contains("pide-literate-stream"));
    assert!(html.contains("world/physical/Cnc5AxisMill.obend"));
    assert!(html.contains("world/physical/LcDrivesStatorUsd.obend"));
    assert!(html.contains("world/market/Demonstration.obend"));

    // 2. Verify slider drag DOM-destruction bug is fixed:
    //    - Must NOT contain `grid.innerHTML = ''`
    //    - Must use `scrubDialSlider` on `<input type="range">` and surgical `updateCellDomInPlace`
    assert!(
        !html.contains("grid.innerHTML = ''"),
        "Slider oninput must never destroy #cells-grid via grid.innerHTML = ''"
    );
    assert!(html.contains("scrubDialSlider("));
    assert!(html.contains("updateCellDomInPlace("));
}

#[test]
fn test_workspace_tree_and_real_obend_pide_elaboration_routes() {
    use obend_gui::server::{WorkspaceElaborateResponse, WorkspaceTreeResponse};

    let server = WorkbenchServer::start_ephemeral().expect("Start ephemeral WorkbenchServer");

    // 1. GET /workspace/tree — must discover real .obend files across categories
    let (status, tree_body) = server
        .request("GET", "/workspace/tree", None)
        .expect("GET /workspace/tree");
    assert_eq!(status, 200);
    let tree: WorkspaceTreeResponse =
        serde_json::from_str(&tree_body).expect("Parse WorkspaceTreeResponse");
    assert!(
        tree.total_files >= 20,
        "Expected at least 20 real .obend files in lean/tests/obend-source, found {}",
        tree.total_files
    );
    for expected_cat in ["world/physical", "world/market", "tutorial", "examples", "ltuo"] {
        assert!(
            tree.categories.contains(&expected_cat.to_string()),
            "Missing category {expected_cat} in {:?}",
            tree.categories
        );
    }
    for expected_path in [
        "world/physical/Cnc5AxisMill.obend",
        "world/physical/LcDrivesStatorUsd.obend",
        "world/market/Demonstration.obend",
        "world/market/UniformProRata.obend",
        "tutorial/ch5-ancestry.obend",
        "DeosCounter.obend",
        "ltuo/LawSpecification.obend",
    ] {
        assert!(
            tree.files.iter().any(|f| f.path == expected_path),
            "Expected workspace tree to contain {expected_path}"
        );
    }

    // 2. GET /workspace/file?path=world/physical/Cnc5AxisMill.obend
    let (status, cnc_body) = server
        .request(
            "GET",
            "/workspace/file?path=world/physical/Cnc5AxisMill.obend",
            None,
        )
        .expect("GET /workspace/file Cnc5AxisMill.obend");
    assert_eq!(status, 200);
    let cnc: WorkspaceElaborateResponse =
        serde_json::from_str(&cnc_body).expect("Parse WorkspaceElaborateResponse for Cnc5AxisMill");
    assert_eq!(cnc.schema, "obend.ffi.elaboration.v1");
    assert_eq!(cnc.module_name, "Cnc5AxisMill");
    assert_eq!(cnc.status, "accepted");
    assert_eq!(cnc.turn_receipt_hex.len(), 64);
    assert!(cnc.source.contains("edition ObjectiveBend 1"));
    assert!(!cnc.literate_sections.is_empty());

    // Verify declarations extracted & elaborated by Lean FFI
    let uncomp_spec = cnc
        .declarations
        .iter()
        .find(|d| d.name == "Uncompensated5AxisMill")
        .unwrap_or_else(|| panic!("Missing Uncompensated5AxisMill in cnc.raw_ffi_json: {}", cnc.raw_ffi_json));
    assert_eq!(uncomp_spec.kind, "spec");
    assert_eq!(uncomp_spec.status, "accepted");
    assert!(uncomp_spec.type_text.contains("Spec<"));
    let spec_details = uncomp_spec
        .spec_details
        .as_ref()
        .expect("SurfaceSpecDetails for Uncompensated5AxisMill");
    assert!(spec_details
        .inherits
        .contains(&"Cnc5AxisMill".to_string()));
    assert!(!spec_details.requires_methods.is_empty());
    assert!(!spec_details.def_methods.is_empty());
    assert!(!spec_details.claims.is_empty());

    let abbe_spec = cnc
        .declarations
        .iter()
        .find(|d| d.name == "AbbeAndRuckigCompensatedMill")
        .expect("AbbeAndRuckigCompensatedMill declaration");
    assert_eq!(abbe_spec.kind, "spec");
    assert_eq!(abbe_spec.status, "accepted");
    assert!(abbe_spec.type_text.contains("Spec<"));

    // Verify Lean-proved claim `Uncompensated5AxisMill.volumetric_decomposition`
    let claim = cnc
        .claims
        .iter()
        .find(|c| c.name == "volumetric_decomposition")
        .expect("volumetric_decomposition claim");
    assert_eq!(claim.status, "verified");
    assert!(claim.steps > 0);

    // Verify emitted Leaf.Book for `compensated5AxisMill`
    let book = cnc
        .leaf_books
        .iter()
        .find(|b| b.object == "compensated5AxisMill")
        .expect("Leaf.Book for compensated5AxisMill");
    assert!(book.closed);
    assert!(book.slot_count >= 5);

    // Verify demand-machine previews for 0-arg entry functions (`104` and `26`)
    let uncomp_prev = cnc
        .previews
        .iter()
        .find(|p| p.entry == "uncompensatedErrorSample")
        .expect("preview for uncompensatedErrorSample");
    assert_eq!(uncomp_prev.status, "finished");
    assert_eq!(
        uncomp_prev.result.get("value").and_then(|v| v.as_str()),
        Some("104")
    );
    let comp_prev = cnc
        .previews
        .iter()
        .find(|p| p.entry == "compensatedErrorSample")
        .expect("preview for compensatedErrorSample");
    assert_eq!(comp_prev.status, "finished");
    assert_eq!(
        comp_prev.result.get("value").and_then(|v| v.as_str()),
        Some("26")
    );

    // 3. POST /workspace/elaborate on `world/physical/LcDrivesStatorUsd.obend`
    let stator_req = serde_json::json!({
        "path": "world/physical/LcDrivesStatorUsd.obend",
        "entry": "lcDrivesInSlotPeakTemp8kW"
    })
    .to_string();
    let (status, stator_body) = server
        .request("POST", "/workspace/elaborate", Some(&stator_req))
        .expect("POST /workspace/elaborate LcDrivesStatorUsd.obend");
    assert_eq!(status, 200);
    let stator: WorkspaceElaborateResponse = serde_json::from_str(&stator_body)
        .expect("Parse WorkspaceElaborateResponse for LcDrivesStatorUsd");
    assert_eq!(stator.module_name, "LcDrivesStatorUsd");
    assert_eq!(stator.status, "accepted");
    assert!(stator
        .claims
        .iter()
        .any(|c| c.name == "peak_temp_open_recursion" && c.status == "verified"));
    assert!(stator
        .leaf_books
        .iter()
        .any(|b| b.object == "lcDrivesProductionStator" && b.slot_count >= 5));
    let temp_prev = stator
        .previews
        .iter()
        .find(|p| p.entry == "lcDrivesInSlotPeakTemp8kW")
        .expect("preview for lcDrivesInSlotPeakTemp8kW");
    assert_eq!(temp_prev.status, "finished");
    assert_eq!(
        temp_prev.result.get("value").and_then(|v| v.as_str()),
        Some("122")
    );

    // 4. POST /workspace/elaborate on multi-module `world/market/Demonstration.obend` (imports `./UniformProRata.obend` -> `./MarketMath.obend`)
    let demo_req = serde_json::json!({
        "path": "world/market/Demonstration.obend"
    })
    .to_string();
    let (status, demo_body) = server
        .request("POST", "/workspace/elaborate", Some(&demo_req))
        .expect("POST /workspace/elaborate Demonstration.obend");
    assert_eq!(status, 200);
    let demo: WorkspaceElaborateResponse = serde_json::from_str(&demo_body).unwrap();
    assert_eq!(demo.module_name, "Demonstration");
    assert_eq!(demo.status, "accepted");
    assert!(demo.declarations.iter().any(|d| d.name == "divideQuotient" && d.status == "accepted"));
    assert!(demo.declarations.iter().any(|d| d.name == "rationedBook" && d.status == "accepted"));

    // 5. POST /workspace/elaborate on `ltuo/LawSpecification.obend` + custom law confluence regime classification
    let law_req = serde_json::json!({
        "path": "ltuo/LawSpecification.obend"
    })
    .to_string();
    let (status, law_body) = server
        .request("POST", "/workspace/elaborate", Some(&law_req))
        .expect("POST /workspace/elaborate LawSpecification.obend");
    assert_eq!(status, 200);
    let law_elab: WorkspaceElaborateResponse = serde_json::from_str(&law_body).unwrap();
    assert_eq!(law_elab.status, "accepted");
    assert!(!law_elab.claims.is_empty());
    assert!(law_elab
        .claims
        .iter()
        .any(|c| c.name == "positive" && c.status == "verified"));

    // Custom `.obend` source with `law` declarations that parse via `Obend.Spec.Law.parse` and classify via `LawDial.dial`
    let custom_law_src = r#"edition ObjectiveBend 1
# Custom PIDE live elaboration test with .free, .stepShaped, and .ordering laws
law monotone_temp: monotone(T) and new.T <= 35
law seal_once: writeOnce(T) and new.T <= 35
law coupled_diff: new.a <= new.b + 5

def answer() -> Nat:
  42n
"#;
    let custom_req = serde_json::json!({
        "module_name": "LivePideCustom",
        "source": custom_law_src,
        "entry": "answer"
    })
    .to_string();
    let (status, custom_body) = server
        .request("POST", "/workspace/elaborate", Some(&custom_req))
        .expect("POST /workspace/elaborate custom");
    assert_eq!(status, 200);
    let custom_elab: WorkspaceElaborateResponse = serde_json::from_str(&custom_body).unwrap();
    assert_eq!(custom_elab.status, "accepted");
    assert_eq!(custom_elab.laws.len(), 3);
    assert!(custom_elab.laws.iter().all(|l| l.parsed));
    assert_eq!(custom_elab.laws[0].confluence_regime, "free");
    assert_eq!(custom_elab.laws[0].dial_verdict, ".free");
    assert_eq!(custom_elab.laws[1].confluence_regime, "stepShaped");
    assert_eq!(custom_elab.laws[1].dial_verdict, ".stepShaped");
    assert_eq!(custom_elab.laws[2].confluence_regime, "ordering");
    assert_eq!(custom_elab.laws[2].dial_verdict, ".ordering");
    assert!(custom_elab
        .previews
        .iter()
        .any(|p| p.entry == "answer" && p.result.get("value").and_then(|v| v.as_str()) == Some("42")));

    // 6. Error & refusal paths on `/workspace/file` and `/workspace/elaborate`
    let (status, _) = server.request("GET", "/workspace/file", None).unwrap();
    assert_eq!(status, 400);
    let (status, _) = server
        .request("GET", "/workspace/file?path=../Cargo.toml", None)
        .unwrap();
    assert_eq!(status, 400);
    let (status, _) = server
        .request("GET", "/workspace/file?path=nonexistent/Missing.obend", None)
        .unwrap();
    assert_eq!(status, 404);

    let bad_obend_req = serde_json::json!({
        "module_name": "BrokenModule",
        "source": "edition ObjectiveBend 1\ndef broken(x: Nat) -> Bool:\n  x + 1n\n"
    })
    .to_string();
    let (status, bad_body) = server
        .request("POST", "/workspace/elaborate", Some(&bad_obend_req))
        .unwrap();
    assert_eq!(status, 200);
    let bad_elab: WorkspaceElaborateResponse = serde_json::from_str(&bad_body).unwrap();
    assert_eq!(bad_elab.status, "refused");
}

