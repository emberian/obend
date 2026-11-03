/* verilator lint_off UNUSED */
/* verilator lint_off DECLFILENAME */
// Canonical Verilator Top-Level Testbench (`tb_top.sv`)
// Instantiates ONLY compiler-emitted SystemVerilog modules:
//   1. `cleanroom_tcad_stack`       (`CleanroomTcadStack.obend` 5-stage pipelined RTL)
//   2. `lc_drives_userspace_stator` (`LcDrivesStator.obend` 3-layer stator RTL)
//   3. `cnc_5axis_userspace_mill`   (`Cnc5AxisMill.obend` 2-layer 5-axis mill RTL)
//   4. `obend_retimed_mac2`         (`Synth.lean` retimed 2-stage DSP MAC)
//   5. `silicon_elab_top`           (4-zone Silicon Elaborator Fabric + 5 hierarchical macros)

`include "cleanroom_tcad_stack.sv"
`include "lc_drives_userspace_stator.sv"
`include "cnc_5axis_userspace_mill.sv"
`include "obend_retimed_mac2.sv"
`include "silicon_elab_top.sv"

module tb_top (
  input  logic        clk,
  input  logic        rst,

  // 1. CleanroomTcadStack inputs & outputs
  input  logic [63:0] tcad_in_0,
  output logic [63:0] tcad_out_oxideEotPicometers,
  output logic [63:0] tcad_out_vthMilliV,
  output logic [63:0] tcad_out_drainCurrentUa,
  output logic [63:0] tcad_out_gateDelayPs,
  output logic [63:0] tcad_out_calibratedDelayPs,

  // 2. LcDrivesStator inputs & outputs
  input  logic [63:0] stator_in_0,
  output logic [63:0] stator_out_massKg,
  output logic [63:0] stator_out_camSurfaceErrorUm,
  output logic [63:0] stator_out_thermalResistance,
  output logic [63:0] stator_out_sdfMargin,
  output logic [63:0] stator_out_peakWindingTemp,

  // 3. Cnc5AxisMill inputs & outputs
  input  logic [63:0] mill_in_0,
  output logic [63:0] mill_out_servoLagUm,
  output logic [63:0] mill_out_endMillDeflectionUm,
  output logic [63:0] mill_out_abbeAngularDriftUm,
  output logic [63:0] mill_out_commandedAxisAt10mmUm,
  output logic [63:0] mill_out_totalVolumetricErrorUm,

  // 4. Retimed MAC2 inputs & outputs
  input  logic [63:0] mac_in_a,
  input  logic [63:0] mac_in_b,
  input  logic [63:0] mac_in_c,
  output logic [63:0] mac_out_y,

  // 5. 4-Zone Silicon Elaborator Fabric + ICAP DPR inputs & outputs
  input  logic        elab_ap_start,
  input  logic        elab_dpr_isolate_en,
  input  logic        elab_dpr_load_we,
  input  logic [63:0] elab_dpr_frame_word,
  input  logic [63:0] elab_dpr_expected_digest,
  input  logic [63:0] elab_dpr_computed_digest,
  input  logic        elab_dpr_moved_pin,
  input  logic [31:0] elab_target_expr_h,
  input  logic [31:0] elab_target_type_h,
  input  logic [31:0] elab_target_decl_sym,
  input  logic [31:0] elab_fuel_budget,
  output logic        elab_ap_done,
  output logic        elab_ap_idle,
  output logic [31:0] elab_result_status,
  output logic [31:0] elab_perf_cycles,
  output logic [31:0] elab_perf_cam_hits,
  output logic [31:0] elab_perf_cam_allocs,
  output logic [31:0] elab_perf_bypass_cnt,
  output logic [31:0] elab_perf_noc_flits,
  output logic [31:0] elab_perf_lut_hits,
  output logic [31:0] elab_zone3_match_thm,
  output logic        elab_dpr_commit_ok,
  output logic        elab_dpr_fallback_active
);

  cleanroom_tcad_stack u_tcad (
    .clk(clk),
    .rst(rst),
    .arg(tcad_in_0),
    .out_oxideEotPicometers(tcad_out_oxideEotPicometers),
    .out_vthMilliV(tcad_out_vthMilliV),
    .out_drainCurrentUa(tcad_out_drainCurrentUa),
    .out_gateDelayPs(tcad_out_gateDelayPs),
    .out_calibratedDelayPs(tcad_out_calibratedDelayPs)
  );

  lc_drives_userspace_stator u_stator (
    .clk(clk),
    .rst(rst),
    .arg(stator_in_0),
    .out_massKg(stator_out_massKg),
    .out_camSurfaceErrorUm(stator_out_camSurfaceErrorUm),
    .out_thermalResistance(stator_out_thermalResistance),
    .out_sdfMargin(stator_out_sdfMargin),
    .out_peakWindingTemp(stator_out_peakWindingTemp)
  );

  cnc_5axis_userspace_mill u_mill (
    .clk(clk),
    .rst(rst),
    .arg(mill_in_0),
    .out_servoLagUm(mill_out_servoLagUm),
    .out_endMillDeflectionUm(mill_out_endMillDeflectionUm),
    .out_abbeAngularDriftUm(mill_out_abbeAngularDriftUm),
    .out_commandedAxisAt10mmUm(mill_out_commandedAxisAt10mmUm),
    .out_totalVolumetricErrorUm(mill_out_totalVolumetricErrorUm)
  );

  obend_retimed_mac2 u_mac2 (
    .clk(clk),
    .rst(rst),
    .a(mac_in_a),
    .b(mac_in_b),
    .c(mac_in_c),
    .mac_out(mac_out_y)
  );

  silicon_elab_top u_silicon_elab (
    .clk(clk),
    .rst(rst),
    .ap_start(elab_ap_start),
    .dpr_isolate_en(elab_dpr_isolate_en),
    .dpr_load_we(elab_dpr_load_we),
    .dpr_frame_word(elab_dpr_frame_word),
    .dpr_expected_digest(elab_dpr_expected_digest),
    .dpr_computed_digest(elab_dpr_computed_digest),
    .dpr_moved_pin(elab_dpr_moved_pin),
    .target_expr_h(elab_target_expr_h),
    .target_type_h(elab_target_type_h),
    .target_decl_sym(elab_target_decl_sym),
    .fuel_budget(elab_fuel_budget),
    .ap_done(elab_ap_done),
    .ap_idle(elab_ap_idle),
    .result_status(elab_result_status),
    .perf_cycles(elab_perf_cycles),
    .perf_cam_hits(elab_perf_cam_hits),
    .perf_cam_allocs(elab_perf_cam_allocs),
    .perf_bypass_cnt(elab_perf_bypass_cnt),
    .perf_noc_flits(elab_perf_noc_flits),
    .perf_lut_hits(elab_perf_lut_hits),
    .zone3_match_thm(elab_zone3_match_thm),
    .dpr_commit_ok(elab_dpr_commit_ok),
    .dpr_fallback_active(elab_dpr_fallback_active)
  );

endmodule
