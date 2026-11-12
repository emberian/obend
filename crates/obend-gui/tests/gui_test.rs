use obend_gui::{
    discover_apps, parse_ngc_text, parse_obend_layer_source, parse_smt2_text, parse_stl_bytes,
    parse_sv_summary, parse_vcd_reader, validate_app_slug, vcd_bits_to_hex, NotebookCell,
    NotebookRunner,
};
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
