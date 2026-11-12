use obend_gui::{
    discover_apps, extract_wikilink_owners, parse_ngc_text, parse_obend_layer_source,
    parse_smt2_text, parse_stl_bytes, parse_sv_summary, parse_vcd_reader, validate_app_slug,
    vcd_bits_to_hex, FeecSimplicialFemCard, FrustumRedactedViewCard, NotebookCell, NotebookRunner,
    PcbMultiphysicsDfmCard, PdeConservationCard, ProjectionCard, Vehicle6DofTrajectoryCard,
    VerifiedProofBadge, ZkCustodyReceiptCard,
};
use std::collections::BTreeMap;
use std::io::Cursor;

#[test]
fn streaming_vcd_parser_and_svg_renderer_handle_scalars_buses_and_scopes() {
    let vcd = b"$version Verilator 5.0 $end
$timescale 1ns $end
$scope module top $end
$var wire 1 ! clk $end
$var wire 8 \" pc_out [7:0] $end
$upscope $end
$enddefinitions $end
#0
0!
b00000000 \"
#5
1!
b00000100 \"
#10
0!
#15
1!
b00101010 \"
";
    let digest = parse_vcd_reader(
        Cursor::new(&vcd[..]),
        Some("sim/trace.vcd".to_string()),
        vcd.len() as u64,
        true,
    )
    .expect("parse VCD");

    assert!(digest.present);
    assert_eq!(digest.version.as_deref(), Some("Verilator 5.0"));
    assert_eq!(digest.timescale.as_deref(), Some("1ns"));
    assert_eq!(digest.start_time, 0);
    assert_eq!(digest.end_time, 15);
    assert_eq!(digest.signal_count, 2);
    assert_eq!(digest.total_transitions, 5);

    let pc = digest
        .signals
        .iter()
        .find(|s| s.name == "pc_out")
        .expect("pc_out signal");
    assert_eq!(pc.width, 8);
    assert_eq!(pc.initial_value_hex, "0x0");
    assert_eq!(pc.last_value_hex, "0x2a");
    assert_eq!(vcd_bits_to_hex(b"00101010"), "0x2a");
    assert_eq!(vcd_bits_to_hex(b"01xz"), "0xZ");

    let svg = digest.waveform_svg.expect("rendered SVG");
    assert!(svg.starts_with("<svg "));
    assert!(svg.contains("pc_out[8]"));
}

#[test]
fn stl_binary_and_ascii_parsers_extract_exact_triangle_counts_and_bounds() {
    let mut bin_stl = vec![0u8; 84 + 50];
    bin_stl[..11].copy_from_slice(b"OBEND_PART\0");
    bin_stl[80..84].copy_from_slice(&1u32.to_le_bytes());
    let vertices: [[f32; 3]; 3] = [[-1.0, 2.0, 0.5], [4.0, -3.0, 1.5], [0.0, 5.0, 8.0]];
    for (vi, v) in vertices.iter().enumerate() {
        for (ai, &coord) in v.iter().enumerate() {
            let off = 84 + 12 + vi * 12 + ai * 4;
            bin_stl[off..off + 4].copy_from_slice(&coord.to_le_bytes());
        }
    }
    let stats = parse_stl_bytes("mesh/part.stl".to_string(), &bin_stl);
    assert_eq!(stats.format, "binary");
    assert_eq!(stats.header_text, "OBEND_PART");
    assert_eq!(stats.triangle_count, 1);
    assert!(stats.binary_size_consistent);
    assert_eq!(stats.bbox_min, [-1.0, -3.0, 0.5]);
    assert_eq!(stats.bbox_max, [4.0, 5.0, 8.0]);

    let ascii_stl = b"solid cube
  facet normal 0 0 1
    outer loop
      vertex 0 0 0
      vertex 2 0 0
      vertex 0 3 4
    endloop
  endfacet
endsolid cube
";
    let ascii_stats = parse_stl_bytes("mesh/ascii.stl".to_string(), ascii_stl);
    assert_eq!(ascii_stats.format, "ascii");
    assert_eq!(ascii_stats.triangle_count, 1);
    assert_eq!(ascii_stats.bbox_min, [0.0, 0.0, 0.0]);
    assert_eq!(ascii_stats.bbox_max, [2.0, 3.0, 4.0]);
}

#[test]
fn ngc_smt2_sv_and_obend_parsers_and_slug_validation_work() {
    let ngc = "(5-axis toolpath)\nS12000 M03\nG00 X0 Y0 Z10\nG01 X1 Y2 Z3 (NO_GOUGE=1 TOOL_SDF=14)\nG01 X2 Y3 Z4 (NO_GOUGE=1 TOOL_SDF=9)\n";
    let ngc_stats = parse_ngc_text("cam/path.ngc".to_string(), ngc.len() as u64, ngc);
    assert_eq!(ngc_stats.spindle_rpm, Some(12000));
    assert_eq!(ngc_stats.rapid_g00_moves, 1);
    assert_eq!(ngc_stats.linear_g01_moves, 2);
    assert_eq!(ngc_stats.no_gouge_verified_points, 2);
    assert_eq!(ngc_stats.min_tool_sdf, Some(9));
    assert_eq!(ngc_stats.max_tool_sdf, Some(14));

    let smt = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n(define-fun id ((x (_ BitVec 8))) (_ BitVec 8) x)\n(assert (distinct a (id a)))\n(check-sat)\n";
    let smt_stats = parse_smt2_text(
        "lec.smt2".to_string(),
        "apps/lec.smt2".to_string(),
        smt.len() as u64,
        smt.to_string(),
    );
    assert_eq!(smt_stats.logic.as_deref(), Some("QF_BV"));
    assert_eq!(smt_stats.declare_const_count, 1);
    assert_eq!(smt_stats.define_fun_count, 1);
    assert_eq!(smt_stats.assert_count, 1);
    assert_eq!(smt_stats.check_sat_count, 1);

    let sv = "module top_core(input logic clk);\n  always_ff @(posedge clk) begin end\nendmodule\n";
    let sv_stats = parse_sv_summary("top.sv".to_string(), "apps/top.sv".to_string(), sv.len() as u64, sv);
    assert_eq!(sv_stats.module_names, vec!["top_core"]);
    assert_eq!(sv_stats.always_ff_count, 1);

    let ob = "edition ObjectiveBend 1\nlaw cap: new.x <= 10\nspec Counter for Target:\n  claim inc(n: Nat): true\n";
    let ob_stats = parse_obend_layer_source(
        "Counter.obend".to_string(),
        "apps/Counter.obend".to_string(),
        ob.len() as u64,
        ob.to_string(),
    );
    assert_eq!(ob_stats.laws, vec!["cap"]);
    assert_eq!(ob_stats.specs, vec!["Counter"]);
    assert_eq!(ob_stats.claims, vec!["inc"]);

    assert!(validate_app_slug("../etc/passwd").is_err());
    assert_eq!(validate_app_slug("fidget-cam").unwrap(), "fidget-cam");
    let discovered = discover_apps();
    assert!(discovered.total_apps >= 1);
}

#[test]
fn pide_notebook_runner_elaborates_obend_cells_and_refuses_non_obend() {
    let mut runner = NotebookRunner::new().expect("init NotebookRunner");
    let cells = vec![
        NotebookCell {
            id: "c1".to_string(),
            kind: "obendCode".to_string(),
            source: "edition ObjectiveBend 1\nlaw cap: new.count <= 100\ndef mainVal() -> Nat:\n  7n\n"
                .to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "c2".to_string(),
            kind: "obendCode".to_string(),
            source: "not valid obend source".to_string(),
            status: "ready".to_string(),
        },
    ];

    let results = runner.execute_cells(&cells);
    assert_eq!(results.len(), 2);
    let summary = results[0].1.as_ref().expect("c1 elaborates");
    assert_eq!(summary.schema, "obend.ffi.elaboration.v1");
    assert_eq!(summary.status, "accepted");
    assert_eq!(summary.laws.len(), 1);
    assert_eq!(summary.laws[0].name, "cap");
    assert!(results[1].1.is_err(), "non-.obend cell must fail closed");

    let aff = runner
        .query_law_affordances("law cap: new.count <= 100")
        .expect("law affordances");
    assert!(aff.parsed);
    assert_eq!(aff.fields, vec!["count"]);
    assert!(
        runner.query_law_affordances("membrane:true:true").is_err(),
        "retired membrane string queries must fail closed"
    );
}

#[test]
fn incremental_dirty_cone_transclusion_and_bidirectional_scrubbing_preserve_clean_cells() {
    let mut runner = NotebookRunner::new().expect("init NotebookRunner");
    runner.set_section("SpecRoot", "Baseline thermal limit ^limit");
    runner.set_section("TranscludedBridge", "Pulls from ![[SpecRoot#^limit]]");

    let mut pcb_params = BTreeMap::new();
    pcb_params.insert("traceWidthUm".to_string(), 150);
    pcb_params.insert("clearanceUm".to_string(), 120);
    runner.register_cell_lens("c_pcb", "pcbMultiphysicsDfm", pcb_params, &[]);

    let mut cells = vec![
        NotebookCell {
            id: "c_pcb".to_string(),
            kind: "pcbMultiphysicsDfm".to_string(),
            source: "# @module: PcbBase\n# @param traceWidthUm=150\nedition ObjectiveBend 1\ndef traceW() -> Nat:\n  150n\n"
                .to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "c_downstream".to_string(),
            kind: "pdeConservation".to_string(),
            source: "# @depends: c_pcb\nedition ObjectiveBend 1\ndef fluxCap() -> Nat:\n  300n\n"
                .to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "c_transcluded".to_string(),
            kind: "feecSimplicialFem".to_string(),
            source: "# cites [[TranscludedBridge#Summary]]\nedition ObjectiveBend 1\ndef meshOrder() -> Nat:\n  3n\n"
                .to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "c_isolated".to_string(),
            kind: "zkCustodyReceipt".to_string(),
            source: "edition ObjectiveBend 1\ndef custodyEpoch() -> Nat:\n  9n\n".to_string(),
            status: "ready".to_string(),
        },
    ];

    assert_eq!(
        extract_wikilink_owners("See [[PageA#Sec]] and ![[PageB#^blk|alias]]"),
        vec!["PageA".to_string(), "PageB".to_string()]
    );

    // Pass 1: cold cache evaluates all 4 cells
    let r1 = runner.execute_workbook_incremental(&cells);
    assert_eq!(r1.dirty_cone.len(), 4);
    assert!(r1.clean_reused.is_empty());
    assert_eq!(runner.cell_eval_count("c_pcb"), 1);
    assert_eq!(runner.cell_eval_count("c_downstream"), 1);
    assert_eq!(runner.cell_eval_count("c_transcluded"), 1);
    assert_eq!(runner.cell_eval_count("c_isolated"), 1);
    let isolated_digest = r1.cell_digests["c_isolated"];

    // Pass 2: unchanged workbook recomputes 0 cells!
    let r2 = runner.execute_workbook_incremental(&cells);
    assert!(r2.dirty_cone.is_empty());
    assert_eq!(r2.clean_reused.len(), 4);
    assert_eq!(runner.cell_eval_count("c_pcb"), 1);

    // Pass 3: scrubbing a read-only proof badge (`drcVerified`) MUST fail closed without mutating cache
    let badge_err = runner
        .scrub_cell_parameter(&mut cells, "c_pcb", "drcVerified", 0)
        .expect_err("read-only badge scrub must fail closed");
    assert!(format!("{badge_err}").contains("read-only"));
    assert_eq!(runner.cell_eval_count("c_pcb"), 1);

    // Pass 4: scrubbing `traceWidthUm` on `c_pcb` recomputes ONLY `c_pcb` and `c_downstream`!
    let r3 = runner
        .scrub_cell_parameter(&mut cells, "c_pcb", "traceWidthUm", 220)
        .expect("scrub traceWidthUm");
    assert_eq!(r3.dirty_cone, vec!["c_pcb", "c_downstream"]);
    assert_eq!(r3.clean_reused, vec!["c_transcluded", "c_isolated"]);
    assert_eq!(runner.cell_eval_count("c_pcb"), 2);
    assert_eq!(runner.cell_eval_count("c_downstream"), 2);
    assert_eq!(runner.cell_eval_count("c_transcluded"), 1);
    assert_eq!(runner.cell_eval_count("c_isolated"), 1);
    assert_eq!(r3.cell_digests["c_isolated"], isolated_digest);

    // Pass 5: editing `SpecRoot` propagates 2 hops (`SpecRoot -> TranscludedBridge -> c_transcluded`)
    // and recomputes ONLY `c_transcluded`!
    runner.set_section("SpecRoot", "Updated thermal limit ^limit = 85C");
    let r4 = runner.execute_workbook_incremental(&cells);
    assert_eq!(r4.dirty_cone, vec!["c_transcluded"]);
    assert_eq!(runner.cell_eval_count("c_transcluded"), 2);
    assert_eq!(runner.cell_eval_count("c_pcb"), 2);
    assert_eq!(runner.cell_eval_count("c_isolated"), 1);

    // Pass 6: cyclic / self-citing cell fails closed without corrupting clean cells
    let mut cyclic_cells = cells.clone();
    cyclic_cells.push(NotebookCell {
        id: "c_self_cycle".to_string(),
        kind: "obendCode".to_string(),
        source: "# cites ![[c_self_cycle]]\nedition ObjectiveBend 1\ndef x() -> Nat:\n  1n\n"
            .to_string(),
        status: "ready".to_string(),
    });
    let r5 = runner.execute_workbook_incremental(&cyclic_cells);
    assert!(r5.results[4].1.is_err(), "self-citation cycle must be refused");
    assert_eq!(runner.cell_eval_count("c_isolated"), 1);

    // Pass 7 (Stage-2/3 Astra hardening): unregistered lens scrub must fail closed,
    // and resolving a previously dangling transclusion must invalidate its citing cell!
    assert!(
        runner
            .scrub_cell_parameter(&mut cells, "c_isolated", "bogusParam", 42)
            .is_err(),
        "unregistered lens cell must refuse arbitrary parameter injection"
    );
    runner.set_section("TranscludedBridge", "Pulls from ![[DanglingLateSec]]");
    let r6 = runner.execute_workbook_incremental(&cells);
    assert_eq!(r6.dirty_cone, vec!["c_transcluded"]);
    runner.set_section("DanglingLateSec", "Now resolved! Cyclic [[TranscludedBridge]]");
    let r7 = runner.execute_workbook_incremental(&cells);
    assert_eq!(
        r7.dirty_cone,
        vec!["c_transcluded"],
        "resolving dangling transclusion + cyclic markdown link must invalidate citing cell cleanly"
    );
}

#[test]
fn kernel_workbook_ffi_and_multi_projection_cards_end_to_end() {
    let mut runner = NotebookRunner::new().expect("init NotebookRunner");

    // 1. Exercise Lean `WorkbookEngine` via `step_kernel_workbook_json` & `scrub_kernel_cell_json`
    let init_resp = runner
        .step_kernel_workbook_json(&serde_json::json!({
            "op": "init",
            "title": "HouyhnhnmMultiProjection",
            "sections": [
                {"sectionKey": "AeroSpec", "markdown": "Wing root load", "blocks": [["loadN", 40]]},
                {"sectionKey": "ControlDoc", "markdown": "Embeds ![[AeroSpec#^loadN]]", "blocks": []}
            ],
            "cells": [
                {
                    "cellKey": "veh_6dof",
                    "id": 10,
                    "kind": "vehicle6DofTrajectory",
                    "fields": {"thrustN": 500, "massKg": 25, "se3SymplecticCert": true},
                    "note": "Reads [[ControlDoc]]",
                    "defs": ["accel_est"],
                    "body": [[{"op": "input", "arg": 0}, {"op": "literal", "arg": 20}, {"op": "add", "arg": 0}]]
                },
                {
                    "cellKey": "sealed_key_material",
                    "id": 20,
                    "kind": "zkCustodyReceipt",
                    "fields": {"epochLimit": 12, "thresholdK": 3, "custodyProof": true},
                    "visibility": {"sealed": "top-secret-clearance", "salt": 99991},
                    "defs": ["secret_bias"],
                    "literalValue": 7
                },
                {
                    "cellKey": "feec_mesh",
                    "id": 30,
                    "kind": "feecSimplicialFem",
                    "fields": {"polynomialOrder": 2, "meshRefinement": 4, "pragerSyngeGap": 0},
                    "reads": ["secret_bias"],
                    "defs": ["total_order"],
                    "body": [[{"op": "input", "arg": 0}, {"op": "literal", "arg": 2}, {"op": "add", "arg": 0}]]
                }
            ]
        }))
        .expect("kernel workbook init");
    assert_eq!(init_resp["status"], "accepted");
    assert_eq!(init_resp["cells"][2]["values"][0], 9);

    // Edit upstream markdown section `AeroSpec`: dirty cone hits `veh_6dof` (id 10) via 2-hop transclusion,
    // leaving `sealed_key_material` (20) and `feec_mesh` (30) untouched!
    let sec_resp = runner
        .step_kernel_workbook_json(&serde_json::json!({
            "op": "editSection",
            "sectionKey": "AeroSpec",
            "markdown": "Updated wing root load",
            "blocks": [["loadN", 95]]
        }))
        .expect("kernel editSection");
    assert_eq!(sec_resp["dirtyCone"], serde_json::json!([10]));

    // Capability-scoped redacted export for an uncleared collaborator: cell 20 is redacted while
    // Merkle + downstream `feec_mesh` verification succeeds!
    let redact_resp = runner
        .step_kernel_workbook_json(&serde_json::json!({
            "op": "exportRedacted",
            "clearances": ["public-viewer"]
        }))
        .expect("kernel exportRedacted");
    assert_eq!(redact_resp["verified"], true);
    assert_eq!(redact_resp["entries"][0]["mode"], "visible");
    assert_eq!(redact_resp["entries"][1]["mode"], "redacted");
    assert_eq!(redact_resp["entries"][2]["mode"], "visible");

    // 2. Exercise all 6 new CAE/PDE/PCB/FEEC/6DOF/ZK/Redacted `ProjectionCard`s
    let badge = |field: &str, fmt: &str| VerifiedProofBadge {
        badge_field: field.to_string(),
        judge_format: fmt.to_string(),
        verified: true,
        commitment_hex: "ab".repeat(32),
    };
    let mut cards = vec![
        ProjectionCard::PcbMultiphysicsDfm(PcbMultiphysicsDfmCard {
            cell_key: "pcb1".into(),
            trace_width_um: 170,
            clearance_um: 140,
            copper_weight_oz: 1,
            impedance_ohm: 50,
            tempest_margin_db: 47,
            drc_badge: badge("drcVerified", "openpdk-drc-sta@1"),
        }),
        ProjectionCard::FeecSimplicialFem(FeecSimplicialFemCard {
            cell_key: "fem1".into(),
            polynomial_order: 2,
            mesh_refinement: 4,
            prager_synge_gap_ppm: 125,
            cohomology_betti_1: 1,
            feec_badge: badge("pragerSyngeGap", "feec-prager-synge@1"),
        }),
        ProjectionCard::PdeConservation(PdeConservationCard {
            cell_key: "pde1".into(),
            cfl_milli: 450,
            grid_cells: 1024,
            entropy_residual_ppb: 0,
            hyperbolic_badge: badge("hyperbolicCert", "hyperbolic-fvm@1"),
        }),
        ProjectionCard::Vehicle6DofTrajectory(Vehicle6DofTrajectoryCard {
            cell_key: "veh1".into(),
            thrust_n: 800,
            mass_kg: 40,
            horizon_steps: 200,
            energy_drift_ppm: 2,
            se3_badge: badge("se3SymplecticCert", "se3-vehicle-6dof@1"),
        }),
        ProjectionCard::ZkCustodyReceipt(ZkCustodyReceiptCard {
            cell_key: "zk1".into(),
            epoch_limit: 50,
            threshold_k: 3,
            merkle_root_hex: "cd".repeat(32),
            custody_badge: badge("custodyProof", "tempest-glitch-emc@1"),
        }),
        ProjectionCard::FrustumRedactedView(FrustumRedactedViewCard {
            cell_key: "frustum1".into(),
            viewer_clearance: "partner-tier-1".into(),
            max_depth: 4,
            redacted_cell_count: 1,
            visible_cell_count: 2,
            commitment_badge: badge("commitmentRoot", "mna-dae@1"),
        }),
    ];

    assert!(cards[0].scrub_field("drcVerified", 0).is_err());
    assert!(cards[1].scrub_field("pragerSyngeGap", 0).is_err());
    assert!(cards[2].scrub_field("hyperbolicCert", 0).is_err());
    assert!(cards[3].scrub_field("se3SymplecticCert", 0).is_err());
    assert!(cards[4].scrub_field("custodyProof", 0).is_err());
    assert!(cards[5].scrub_field("commitmentRoot", 0).is_err());

    cards[0].scrub_field("traceWidthUm", 100).expect("scrub pcb width");
    cards[1].scrub_field("polynomialOrder", 4).expect("scrub feec order");
    cards[2].scrub_field("cflMilli", 500).expect("scrub pde cfl");
    cards[3].scrub_field("thrustN", 1200).expect("scrub thrust");
    cards[4].scrub_field("epochLimit", 64).expect("scrub epoch");
    cards[5].scrub_field("maxDepth", 8).expect("scrub depth");

    for card in &cards {
        let svg = card.render_svg_card();
        assert!(svg.starts_with("<svg ") && svg.contains(card.kind_label()));
    }

    // 3. Adversarial FFI boundary checks: invalid UTF-8, undeclared cite:: read, and read-only kernel scrub
    assert!(
        runner.session_mut().step_workbook(&[0xFF, 0xFE, 0xFD]).is_err(),
        "invalid UTF-8 bytes must fail closed"
    );
    assert!(
        runner.session_mut().scrub_projection_cell(&[0xFF, 0xFE]).is_err(),
        "invalid UTF-8 scrub bytes must fail closed"
    );
    assert!(
        runner
            .step_kernel_workbook_json(&serde_json::json!({
                "op": "init",
                "cells": [{
                    "cellKey": "spoof",
                    "id": 1,
                    "kind": "obendCode",
                    "reads": ["cite::AeroSpec"]
                }]
            }))
            .is_err(),
        "undeclared cite:: symbol in reactive reads must be refused"
    );
    assert!(
        runner
            .scrub_kernel_cell_json(&serde_json::json!({
                "cellKey": "veh_6dof",
                "fieldName": "se3SymplecticCert",
                "newValue": false
            }))
            .is_err(),
        "kernel Putnam/Foster lens must refuse read-only proof badge scrub"
    );
}
