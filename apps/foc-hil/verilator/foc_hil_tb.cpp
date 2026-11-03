// Verilator Co-Simulation Testbench for Flagship App #2:
// Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML Inverter HIL (500,000 steps, dt = 100 ns)
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>

#include "Vfoc_drive_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "rk4_pmsm_plant.hpp"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    auto* dut = new Vfoc_drive_top;
    auto* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("foc_hil_trace.vcd");

    obend::foc_hil::Rk4PmsmFcmlPlant plant;

    constexpr uint64_t TOTAL_STEPS       = 500000; // 50 ms at dt = 100 ns
    constexpr uint64_t STEPS_PER_TICK    = 500;    // 50 us = 20 kHz control loop
    constexpr uint64_t TORQUE_STEP_IDX   = 10000;  // t = 1.0 ms: 0 -> 250 A torque step
    constexpr uint64_t DPR_SWAP_IDX      = 250000; // t = 25.0 ms: live ICAP DPR hot-swap
    constexpr uint64_t OVERTEMP_TRIP_IDX = 400000; // t = 40.0 ms: 155 C over-temp injection
    constexpr uint64_t COOL_CHECK_IDX    = 450000; // t = 45.0 ms: verify write-once latch holds

    uint64_t sim_time_ps = 0;
    auto tick_clock = [&](bool dump_vcd) {
        dut->clk = 0;
        dut->eval();
        if (dump_vcd) tfp->dump(sim_time_ps);
        sim_time_ps += 50000; // 50 ns half-period

        dut->clk = 1;
        dut->eval();
        if (dump_vcd) tfp->dump(sim_time_ps);
        sim_time_ps += 50000; // 50 ns half-period (100 ns per physics step)
    };

    // Synchronous reset
    dut->rst             = 1;
    dut->ctrl_tick_en    = 0;
    dut->id_ref_ma       = 0;
    dut->iq_ref_ma       = 0;
    dut->id_meas_ma      = 0;
    dut->iq_meas_ma      = 0;
    dut->omega_e_rads    = 1000;
    dut->cap_err_mv      = 15000; // +15.0 V initial flying-capacitor unbalance
    dut->winding_temp_c  = 65;
    dut->dpr_isolate_en  = 0;
    dut->dpr_high_bw_sel = 0;
    tick_clock(true);
    dut->rst = 0;

    int32_t pre_dpr_vd_mv  = 0;
    int32_t pre_dpr_vq_mv  = 0;
    int32_t pre_dpr_int_d  = 0;
    int32_t pre_dpr_int_q  = 0;
    bool dpr_verified      = false;
    bool trip_1cycle_ok    = false;
    bool latch_hold_ok     = false;
    double iq_at_24ms      = 0.0;
    double id_at_24ms      = 0.0;
    double iq_at_39ms      = 0.0;
    double id_at_39ms      = 0.0;
    double max_cap_ripple_steady = 0.0;

    for (uint64_t step = 0; step < TOTAL_STEPS; ++step) {
        const bool is_ctrl_tick = (step % STEPS_PER_TICK == 0);

        // Reference step at t = 1.0 ms: iq* = 250 A, id* = -100 A
        if (step >= TORQUE_STEP_IDX) {
            dut->id_ref_ma = -100000;
            dut->iq_ref_ma =  250000;
        } else {
            dut->id_ref_ma = 0;
            dut->iq_ref_ma = 0;
        }

        // Sensor feedback from continuous-time RK4 plant
        dut->id_meas_ma     = static_cast<int32_t>(std::llround(plant.state.id_amp * 1000.0));
        dut->iq_meas_ma     = static_cast<int32_t>(std::llround(plant.state.iq_amp * 1000.0));
        dut->omega_e_rads   = static_cast<int32_t>(std::llround(plant.state.omega_e_rads));
        dut->cap_err_mv     = static_cast<int32_t>(std::llround(plant.state.cap_unbal_volt * 1000.0));
        dut->winding_temp_c = static_cast<uint32_t>(std::llround(plant.state.winding_temp_c));
        dut->ctrl_tick_en   = is_ctrl_tick ? 1 : 0;

        // Capture pre-DPR outputs right before t = 25.0 ms
        if (step == DPR_SWAP_IDX - 1) {
            pre_dpr_vd_mv = dut->vd_cmd_mv;
            pre_dpr_vq_mv = dut->vq_cmd_mv;
            pre_dpr_int_d = dut->dbg_int_d_mv;
            pre_dpr_int_q = dut->dbg_int_q_mv;
        }

        // Scenario 3: Live mid-run ICAP DPR layer hot-swap at t = 25.0 ms (1 control tick fence)
        if (step >= DPR_SWAP_IDX && step < DPR_SWAP_IDX + STEPS_PER_TICK) {
            dut->dpr_isolate_en  = 1;
            dut->dpr_high_bw_sel = 1; // Swap in IcapDprHighBandwidthFocOverride bitstream
        } else if (step >= DPR_SWAP_IDX + STEPS_PER_TICK) {
            dut->dpr_isolate_en  = 0;
            dut->dpr_high_bw_sel = 1;
        }

        // Scenario 4: 155 C over-temperature fault injection at t = 40.0 ms
        if (step == OVERTEMP_TRIP_IDX) {
            plant.overtemp_injected = true;
            plant.state.winding_temp_c = 155.0;
            dut->winding_temp_c = 155;
        }
        // Cool down below 155 C at t = 45.0 ms to verify write-once latch remains tripped
        if (step == COOL_CHECK_IDX) {
            plant.overtemp_injected = false;
            plant.state.winding_temp_c = 90.0;
            dut->winding_temp_c = 90;
        }

        // Dump VCD around key events and every 20 kHz control tick
        const bool dump_vcd = is_ctrl_tick ||
                              (step < 2000) ||
                              (step >= TORQUE_STEP_IDX - 100 && step <= TORQUE_STEP_IDX + 500) ||
                              (step >= DPR_SWAP_IDX - 100 && step <= DPR_SWAP_IDX + 600) ||
                              (step >= OVERTEMP_TRIP_IDX - 100 && step <= OVERTEMP_TRIP_IDX + 200);

        tick_clock(dump_vcd);

        // Verify live ICAP DPR isolation holds skid outputs & freezes integrators without glitch
        if (step == DPR_SWAP_IDX) {
            if (dut->vd_cmd_mv == pre_dpr_vd_mv &&
                dut->vq_cmd_mv == pre_dpr_vq_mv &&
                dut->dbg_int_d_mv == pre_dpr_int_d &&
                dut->dbg_int_q_mv == pre_dpr_int_q &&
                dut->pwm_gate_en == 1) {
                dpr_verified = true;
            }
        }

        // Verify 1-cycle over-temperature hardware gate-kill at step == OVERTEMP_TRIP_IDX
        if (step == OVERTEMP_TRIP_IDX) {
            if (dut->fault_trip == 1 &&
                dut->pwm_gate_en == 0 &&
                dut->vd_cmd_mv == 0 &&
                dut->vq_cmd_mv == 0 &&
                dut->fcml_duty_permille == 0) {
                trip_1cycle_ok = true;
            }
        }

        // Verify write-once thermal latch remains tripped even after cooling to 90 C
        if (step == COOL_CHECK_IDX + 10) {
            if (dut->fault_trip == 1 && dut->pwm_gate_en == 0) {
                latch_hold_ok = true;
            }
        }

        // Advance continuous-time 100 ns RK4 motor + FCML physics
        plant.step_rk4(static_cast<double>(static_cast<int32_t>(dut->vd_cmd_mv)),
                       static_cast<double>(static_cast<int32_t>(dut->vq_cmd_mv)),
                       static_cast<double>(static_cast<int32_t>(dut->cap_bal_mv)),
                       dut->pwm_gate_en != 0,
                       step);

        // Sample steady-state tracking accuracy & FCML capacitor ripple
        if (step == 240000) { // t = 24.0 ms (pre-DPR steady state)
            id_at_24ms = plant.state.id_amp;
            iq_at_24ms = plant.state.iq_amp;
        }
        if (step == 390000) { // t = 39.0 ms (post-DPR steady state before thermal trip)
            id_at_39ms = plant.state.id_amp;
            iq_at_39ms = plant.state.iq_amp;
        }
        if (step >= 150000 && step < OVERTEMP_TRIP_IDX) {
            max_cap_ripple_steady = std::max(max_cap_ripple_steady,
                                             std::abs(plant.state.cap_unbal_volt));
        }
    }

    tfp->close();

    const double id_err_24ms = std::abs(id_at_24ms - (-100.0));
    const double iq_err_24ms = std::abs(iq_at_24ms - 250.0);
    const double id_err_39ms = std::abs(id_at_39ms - (-100.0));
    const double iq_err_39ms = std::abs(iq_at_39ms - 250.0);
    const uint32_t total_ctrl_ticks = dut->dbg_ctrl_tick_count;

    std::printf("=== Flagship App #2: 20 kHz FOC + 6-Level SiC FCML HIL Summary ===\n");
    std::printf("  Total RK4 steps (dt=100ns) : %llu (50.0 ms)\n",
                static_cast<unsigned long long>(TOTAL_STEPS));
    std::printf("  20 kHz control ticks       : %u / 1000 (0 dropped ticks)\n", total_ctrl_ticks);
    std::printf("  t=24ms (Nominal Layer)     : id = %.4f A (err %.4f A), iq = %.4f A (err %.4f A)\n",
                id_at_24ms, id_err_24ms, iq_at_24ms, iq_err_24ms);
    std::printf("  t=39ms (Post-DPR Hot-Swap) : id = %.4f A (err %.4f A), iq = %.4f A (err %.4f A)\n",
                id_at_39ms, id_err_39ms, iq_at_39ms, iq_err_39ms);
    std::printf("  FCML +15V unbal recovery   : max steady-state ripple = %.4f V (< 0.50 V)\n",
                max_cap_ripple_steady);
    std::printf("  Live ICAP DPR hot-swap     : %s\n", dpr_verified ? "PASS" : "FAIL");
    std::printf("  155 C 1-cycle gate-kill    : %s\n", trip_1cycle_ok ? "PASS" : "FAIL");
    std::printf("  Write-once fault latch     : %s\n", latch_hold_ok ? "PASS" : "FAIL");

    bool all_ok = (total_ctrl_ticks == 1000) &&
                  (id_err_24ms < 0.25) &&
                  (iq_err_24ms < 0.25) &&
                  (id_err_39ms < 0.25) &&
                  (iq_err_39ms < 0.25) &&
                  (max_cap_ripple_steady < 0.50) &&
                  dpr_verified &&
                  trip_1cycle_ok &&
                  latch_hold_ok;

    delete tfp;
    delete dut;

    if (!all_ok) {
        std::fprintf(stderr, "ERROR: FOC HIL verification failed one or more assertions!\n");
        return 1;
    }
    std::printf("ALL FOC HIL VERIFICATION CHECKS PASSED.\n");
    return 0;
}
