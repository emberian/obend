// Verilator harness for tb_top.sv: the four compiler-emitted modules, checked against the values
// `obend verilate` derives from Lean's own evaluation of the same RtlModules (see verify_sim.sh,
// which also runs `obend verilate` for each module with 16x4 held-input cycles).
#include "Vtb_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>

static vluint64_t main_time = 0;
double sc_time_stamp() { return static_cast<double>(main_time); }

static void tick(Vtb_top* dut, VerilatedVcdC* tfp) {
  dut->clk = 0; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
  dut->clk = 1; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
}

int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Verilated::randReset(2);
  Verilated::traceEverOn(true);
  Vtb_top* dut = new Vtb_top;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  dut->trace(tfp, 99);
  tfp->open("sim_tb_top.vcd");
  uint64_t mismatches = 0;

  dut->rst = 1;
  dut->tcad_in_0 = 0; dut->stator_in_0 = 0; dut->mill_in_0 = 0;
  dut->mac_in_a = 0; dut->mac_in_b = 0; dut->mac_in_c = 0;
  tick(dut, tfp); tick(dut, tfp);
  dut->rst = 0;

  // cleanroom_tcad_stack: outputs are combinational in `arg` (the registers it carries are unread).
  dut->tcad_in_0 = 4ULL; tick(dut, tfp); tick(dut, tfp);
  if (dut->tcad_out_oxideEotPicometers != 700ULL || dut->tcad_out_vthMilliV != 250ULL ||
      dut->tcad_out_gateDelayPs != 56ULL || dut->tcad_out_drainCurrentUa != 270ULL ||
      dut->tcad_out_calibratedDelayPs != 72ULL) {
    std::fprintf(stderr, "MISMATCH cleanroom_tcad_stack @ arg=4\n"); mismatches++;
  }
  dut->tcad_in_0 = 200ULL; tick(dut, tfp); tick(dut, tfp);
  if (dut->tcad_out_gateDelayPs != 1624ULL || dut->tcad_out_drainCurrentUa != 1250ULL ||
      dut->tcad_out_calibratedDelayPs != 1640ULL) {
    std::fprintf(stderr, "MISMATCH cleanroom_tcad_stack @ arg=200\n"); mismatches++;
  }

  dut->stator_in_0 = 8ULL; tick(dut, tfp);
  if (dut->stator_out_massKg != 395ULL || dut->stator_out_camSurfaceErrorUm != 34ULL ||
      dut->stator_out_thermalResistance != 9ULL || dut->stator_out_sdfMargin != 24ULL ||
      dut->stator_out_peakWindingTemp != 122ULL) {
    std::fprintf(stderr, "MISMATCH lc_drives_userspace_stator @ arg=8\n"); mismatches++;
  }

  dut->mill_in_0 = 6ULL; tick(dut, tfp);
  if (dut->mill_out_servoLagUm != 6ULL || dut->mill_out_endMillDeflectionUm != 12ULL ||
      dut->mill_out_abbeAngularDriftUm != 6ULL || dut->mill_out_commandedAxisAt10mmUm != 10024ULL ||
      dut->mill_out_totalVolumetricErrorUm != 26ULL) {
    std::fprintf(stderr, "MISMATCH cnc_5axis_userspace_mill @ arg=6\n"); mismatches++;
  }

  // obend_retimed_mac2: two-cycle latency, a*b + c, reset-free (randReset(2) seeds its registers).
  dut->mac_in_a = 7ULL; dut->mac_in_b = 9ULL; dut->mac_in_c = 11ULL;
  tick(dut, tfp); tick(dut, tfp);
  if (dut->mac_out_y != 74ULL) {
    std::fprintf(stderr, "MISMATCH obend_retimed_mac2: got %llu expected 74\n",
                 static_cast<unsigned long long>(dut->mac_out_y)); mismatches++;
  }
  dut->mac_in_a = 0xFFFFFFFFULL; dut->mac_in_b = 0x100000001ULL; dut->mac_in_c = 1ULL;
  tick(dut, tfp); tick(dut, tfp);
  if (dut->mac_out_y != 0xFFFFFFFFFFFFFFFFULL + 0ULL - 0ULL + 1ULL - 1ULL) { /* 0xFFFFFFFF*0x100000001 = 0xFFFFFFFFFFFFFFFF, +1 wraps to 0 */ }
  if (dut->mac_out_y != 0ULL) {
    std::fprintf(stderr, "MISMATCH obend_retimed_mac2 wrap: got %llx expected 0\n",
                 static_cast<unsigned long long>(dut->mac_out_y)); mismatches++;
  }

  tfp->close(); delete tfp; delete dut;
  std::printf("VERILATE_PASS module=tb_top mismatches=%llu\n", static_cast<unsigned long long>(mismatches));
  return (mismatches == 0) ? 0 : 1;
}
