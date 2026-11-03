#include "Vtb_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>

static vluint64_t main_time = 0;
double sc_time_stamp() { return static_cast<double>(main_time); }

static void tick(Vtb_top* dut, VerilatedVcdC* tfp) {
  dut->clk = 0;
  dut->eval();
  if (tfp) tfp->dump(main_time);
  main_time += 5;
  dut->clk = 1;
  dut->eval();
  if (tfp) tfp->dump(main_time);
  main_time += 5;
}

int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Verilated::randReset(2); // Adversarial randomization of unreset registers
  Verilated::traceEverOn(true);

  Vtb_top* dut = new Vtb_top;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  dut->trace(tfp, 99);
  tfp->open("sim_Canonical.vcd");

  uint64_t mismatches = 0;

  // 2-cycle synchronous reset
  dut->rst = 1;
  dut->tcad_in_0 = 0;
  dut->stator_in_0 = 0;
  dut->mill_in_0 = 0;
  dut->mac_in_a = 0;
  dut->mac_in_b = 0;
  dut->mac_in_c = 0;
  dut->elab_ap_start = 0;
  dut->elab_dpr_isolate_en = 0;
  dut->elab_dpr_load_we = 0;
  dut->elab_dpr_frame_word = 0;
  dut->elab_dpr_expected_digest = 0;
  dut->elab_dpr_computed_digest = 0;
  dut->elab_dpr_moved_pin = 0;
  dut->elab_target_expr_h = 0;
  dut->elab_target_type_h = 0;
  dut->elab_target_decl_sym = 0;
  dut->elab_fuel_budget = 0;
  tick(dut, tfp);
  tick(dut, tfp);
  dut->rst = 0;

  // 1. Verify CleanroomTcadStack (5-stage pipelined RTL) at fanout=4 and overdrive=200
  dut->tcad_in_0 = 4ULL;
  tick(dut, tfp);
  tick(dut, tfp);
  if (dut->tcad_out_oxideEotPicometers != 700ULL ||
      dut->tcad_out_vthMilliV != 250ULL ||
      dut->tcad_out_gateDelayPs != 56ULL ||
      dut->tcad_out_drainCurrentUa != 270ULL ||
      dut->tcad_out_calibratedDelayPs != 72ULL) {
    std::fprintf(stderr, "MISMATCH cleanroom_tcad_stack @ in_0=4\n");
    mismatches++;
  }
  dut->tcad_in_0 = 200ULL;
  tick(dut, tfp);
  tick(dut, tfp);
  if (dut->tcad_out_oxideEotPicometers != 700ULL ||
      dut->tcad_out_vthMilliV != 250ULL ||
      dut->tcad_out_gateDelayPs != 1624ULL ||
      dut->tcad_out_drainCurrentUa != 1250ULL ||
      dut->tcad_out_calibratedDelayPs != 1640ULL) {
    std::fprintf(stderr, "MISMATCH cleanroom_tcad_stack @ in_0=200\n");
    mismatches++;
  }

  // 2. Verify LcDrivesStator (3-layer stator RTL) at current=8
  dut->stator_in_0 = 8ULL;
  tick(dut, tfp);
  if (dut->stator_out_massKg != 395ULL ||
      dut->stator_out_camSurfaceErrorUm != 34ULL ||
      dut->stator_out_thermalResistance != 9ULL ||
      dut->stator_out_sdfMargin != 24ULL ||
      dut->stator_out_peakWindingTemp != 122ULL) {
    std::fprintf(stderr, "MISMATCH lc_drives_userspace_stator @ in_0=8\n");
    mismatches++;
  }

  // 3. Verify Cnc5AxisMill (2-layer 5-axis mill RTL) at feed=6
  dut->mill_in_0 = 6ULL;
  tick(dut, tfp);
  if (dut->mill_out_servoLagUm != 6ULL ||
      dut->mill_out_endMillDeflectionUm != 12ULL ||
      dut->mill_out_abbeAngularDriftUm != 6ULL ||
      dut->mill_out_commandedAxisAt10mmUm != 10024ULL ||
      dut->mill_out_totalVolumetricErrorUm != 26ULL) {
    std::fprintf(stderr, "MISMATCH cnc_5axis_userspace_mill @ in_0=6\n");
    mismatches++;
  }

  // 4. Verify Retimed MAC2 (`obend_retimed_mac2`) at a=7, b=9, c=11 => 7*9 + 11 = 74
  dut->mac_in_a = 7ULL;
  dut->mac_in_b = 9ULL;
  dut->mac_in_c = 11ULL;
  tick(dut, tfp);
  tick(dut, tfp);
  if (dut->mac_out_y != 74ULL) {
    std::fprintf(stderr, "MISMATCH obend_retimed_mac2: got %llu expected 74\n",
                 static_cast<unsigned long long>(dut->mac_out_y));
    mismatches++;
  }

  // 5. Verify 4-Zone Silicon Elaborator Fabric + ICAP DPR hot-swap & 1-cycle fallback
  dut->elab_target_expr_h = 0x1001U;
  dut->elab_target_type_h = 0x1001U;
  dut->elab_target_decl_sym = 0x0204U;
  dut->elab_fuel_budget = 64U;
  dut->elab_ap_start = 1;
  tick(dut, tfp);
  tick(dut, tfp);
  tick(dut, tfp);
  if (!dut->elab_ap_done || (dut->elab_result_status & 0x3U) != 0x3U ||
      dut->elab_perf_cam_allocs == 0U || dut->elab_perf_noc_flits == 0U ||
      dut->elab_perf_lut_hits == 0U) {
    std::fprintf(stderr, "MISMATCH silicon_elab_top Zone 1-4 execution: status=0x%x\n",
                 dut->elab_result_status);
    mismatches++;
  }
  dut->elab_ap_start = 0;
  tick(dut, tfp);

  // Test ICAP DPR 3-phase glitch-free hot-swap (digest match, moved_pin=0)
  dut->elab_dpr_isolate_en = 1;
  dut->elab_dpr_load_we = 1;
  dut->elab_dpr_frame_word = 0xCAFEBABE12345678ULL;
  dut->elab_dpr_expected_digest = 0xABCDEF0123456789ULL;
  dut->elab_dpr_computed_digest = 0xABCDEF0123456789ULL;
  dut->elab_dpr_moved_pin = 0;
  tick(dut, tfp);
  dut->elab_dpr_load_we = 0;
  dut->elab_dpr_isolate_en = 0;
  tick(dut, tfp);
  if (!dut->elab_dpr_commit_ok || dut->elab_dpr_fallback_active) {
    std::fprintf(stderr, "MISMATCH silicon_elab_top ICAP DPR commit failed\n");
    mismatches++;
  }

  // Test ICAP DPR 1-cycle fallback when moved_pin=1 (symmetry broken)
  dut->elab_dpr_isolate_en = 1;
  dut->elab_dpr_moved_pin = 1;
  tick(dut, tfp);
  dut->elab_dpr_isolate_en = 0;
  tick(dut, tfp);
  if (!dut->elab_dpr_fallback_active) {
    std::fprintf(stderr, "MISMATCH silicon_elab_top ICAP DPR moved_pin fallback did not activate\n");
    mismatches++;
  }

  tfp->close();
  delete tfp;
  delete dut;

  std::printf("VERILATE_PASS module=tb_top mismatches=%llu\n",
              static_cast<unsigned long long>(mismatches));
  return (mismatches == 0) ? 0 : 1;
}
