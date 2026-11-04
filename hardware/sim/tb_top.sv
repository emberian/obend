/* verilator lint_off UNUSED */
/* verilator lint_off DECLFILENAME */
// Top-level testbench wrapper for the four compiler-emitted modules in this directory. Hand-written;
// the modules it instantiates are regenerated from Lean by `obend-emit-sv` (see verify_sim.sh).

`include "cleanroom_tcad_stack.sv"
`include "lc_drives_userspace_stator.sv"
`include "cnc_5axis_userspace_mill.sv"
`include "obend_retimed_mac2.sv"

module tb_top (
  input  logic        clk,
  input  logic        rst,

  input  logic [63:0] tcad_in_0,
  output logic [63:0] tcad_out_oxideEotPicometers,
  output logic [63:0] tcad_out_vthMilliV,
  output logic [63:0] tcad_out_drainCurrentUa,
  output logic [63:0] tcad_out_gateDelayPs,
  output logic [63:0] tcad_out_calibratedDelayPs,

  input  logic [63:0] stator_in_0,
  output logic [63:0] stator_out_massKg,
  output logic [63:0] stator_out_camSurfaceErrorUm,
  output logic [63:0] stator_out_thermalResistance,
  output logic [63:0] stator_out_sdfMargin,
  output logic [63:0] stator_out_peakWindingTemp,

  input  logic [63:0] mill_in_0,
  output logic [63:0] mill_out_servoLagUm,
  output logic [63:0] mill_out_endMillDeflectionUm,
  output logic [63:0] mill_out_abbeAngularDriftUm,
  output logic [63:0] mill_out_commandedAxisAt10mmUm,
  output logic [63:0] mill_out_totalVolumetricErrorUm,

  input  logic [63:0] mac_in_a,
  input  logic [63:0] mac_in_b,
  input  logic [63:0] mac_in_c,
  output logic [63:0] mac_out_y
);

  cleanroom_tcad_stack u_tcad (
    .clk(clk), .rst(rst), .arg(tcad_in_0),
    .out_oxideEotPicometers(tcad_out_oxideEotPicometers),
    .out_vthMilliV(tcad_out_vthMilliV),
    .out_drainCurrentUa(tcad_out_drainCurrentUa),
    .out_gateDelayPs(tcad_out_gateDelayPs),
    .out_calibratedDelayPs(tcad_out_calibratedDelayPs)
  );

  lc_drives_userspace_stator u_stator (
    .clk(clk), .rst(rst), .arg(stator_in_0),
    .out_massKg(stator_out_massKg),
    .out_camSurfaceErrorUm(stator_out_camSurfaceErrorUm),
    .out_thermalResistance(stator_out_thermalResistance),
    .out_sdfMargin(stator_out_sdfMargin),
    .out_peakWindingTemp(stator_out_peakWindingTemp)
  );

  cnc_5axis_userspace_mill u_mill (
    .clk(clk), .rst(rst), .arg(mill_in_0),
    .out_servoLagUm(mill_out_servoLagUm),
    .out_endMillDeflectionUm(mill_out_endMillDeflectionUm),
    .out_abbeAngularDriftUm(mill_out_abbeAngularDriftUm),
    .out_commandedAxisAt10mmUm(mill_out_commandedAxisAt10mmUm),
    .out_totalVolumetricErrorUm(mill_out_totalVolumetricErrorUm)
  );

  obend_retimed_mac2 u_mac2 (
    .clk(clk), .rst(rst), .a(mac_in_a), .b(mac_in_b), .c(mac_in_c), .mac_out(mac_out_y)
  );

endmodule
