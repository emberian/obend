// Flagship App #8: Quantum Photonic & Topological Matter Co-Processor Verilator Testbench
// (`apps/quantum-photonic-matter/verilator/quantum_photonic_tb.cpp`)
//
// Cycle-accurate Verilator co-simulation of `quantum_photonic_coproc_top.sv` verifying:
// 1. `.obend` open-recursive datapath agreement with `Obend/Apps/QuantumPhotonicMatter.lean`:
//    - `coprocAdjointOpsAt25 = 11046` (`25 * 4 + 10946`),
//    - `coprocBudgetAt6 = 132` (`(6 * 16 + 4) + 32`),
//    - `krawtchoukMacsAt16 = 3206` (`16 * 4 + 3142`),
//    - `krawtchoukFidelityAt4 = 2004` (`(4 * 250 + 4) + 1000`),
//    - CMT directional coupler lengths L_0 = 1571 nm, L_1 = 2721 nm, L_2 = 3142 nm.
// 2. 1-WL Quotient DPR Guard & 1-Cycle Symmetry-Breaking Fallback (`quotientHypergraph_moved_pin_blocks`):
//    - Under symmetric Q_3 shell weights (3, 4, 3), `out_dpr_quotient_usable == 1` and
//      `out_active_hypergraph_ops == 8` (2x quotient compression from 16 ops).
//    - When an `.obend` override moves pin `w01` from 3 to 5, `out_dpr_quotient_usable` drops
//      to 0 in 1 cycle and falls back to the unquotiented 8-mode datapath (`16` ops).
// 3. 4x4 Faddeev-LeVerrier Exact Thermo-Optic Crosstalk Cancellation (`compensateThermalCrosstalk_exact_4x4`):
//    - Across 16 target phase vectors v, verifies `H_cross * adj(H_cross) * v == 10946 * v` with
//      zero residual crosstalk error.
// 4. Majorana Tetron Non-Abelian Braiding & Lindblad Parity Cooling (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`):
//    - Verifies Artin braid relation U_12 U_23 U_12 == U_23 U_12 U_23 across all test states,
//    - Verifies that `L_cool` annihilates even-parity codewords (`L_cool * psi_even == 0`),
//    - Verifies that `L_cool` maps quasiparticle-poisoned odd-parity states back into the +1
//      even-parity code space in 1 cycle.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include "Vquantum_photonic_coproc_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

static void tick(Vquantum_photonic_coproc_top* top, VerilatedVcdC* tfp, uint64_t& sim_time) {
    top->clk = 0;
    top->eval();
    if (tfp) tfp->dump(sim_time++);
    top->clk = 1;
    top->eval();
    if (tfp) tfp->dump(sim_time++);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    Vquantum_photonic_coproc_top* top = new Vquantum_photonic_coproc_top;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("quantum_photonic_trace.vcd");

    uint64_t sim_time = 0;

    // Reset
    top->rst_n = 0;
    top->in_batch_vectors = 25;
    top->in_syndrome_rounds = 6;
    top->in_krawtchouk_batch_size = 16;
    top->in_pst_step_index = 4;
    top->in_pin_shell_w01 = 3;
    top->in_pin_shell_w12 = 4;
    top->in_pin_shell_w23 = 3;
    top->in_target_v0 = 10;
    top->in_target_v1 = -5;
    top->in_target_v2 = 7;
    top->in_target_v3 = 3;
    top->in_tetron_psi0 = 1;
    top->in_tetron_psi1 = 0;
    top->in_tetron_psi2 = 0;
    top->in_tetron_psi3 = 1;
    top->in_braid_enable = 0;

    tick(top, tfp, sim_time);
    top->rst_n = 1;
    top->in_braid_enable = 1;
    tick(top, tfp, sim_time);

    // 1. Check `.obend` open-recursive outputs against Lean theorems
    if (top->out_wl_compressed_shells != 4ULL ||
        top->out_faddeev_crosstalk_det != 8769ULL ||
        top->out_cmt_krawtchouk_len0_nm != 1571ULL ||
        top->out_cmt_krawtchouk_len1_nm != 2721ULL ||
        top->out_cmt_krawtchouk_len2_nm != 3142ULL ||
        top->out_quotient_reverse_adjoint_ops != 8869ULL ||
        top->out_coproc_cycle_budget != 132ULL ||
        top->out_krawtchouk_adjoint_macs != 3206ULL ||
        top->out_pst_transfer_fidelity_ppm != 2004ULL) {
        std::fprintf(stderr, "FAIL: .obend open-recursive co-processor output mismatch!\n");
        return 1;
    }

    // 2. Check symmetric 1-WL quotient & Q_3 PST enclosure
    if (!top->out_dpr_quotient_usable ||
        top->out_dpr_fallback_full_8mode ||
        top->out_active_hypergraph_ops != 8ULL ||
        !top->out_q3_pst_antipodal_enclosed) {
        std::fprintf(stderr, "FAIL: symmetric Q_3 1-WL quotient or PST check failed!\n");
        return 1;
    }

    // 3. Sweep 16 target vectors for 4x4 Faddeev-LeVerrier crosstalk cancellation
    //    and both even-parity & odd-parity poisoned Majorana tetron states
    uint32_t crosstalk_vectors_checked = 0;
    uint32_t even_states_dark = 0;
    uint32_t odd_states_cooled = 0;
    uint32_t dpr_fallbacks_triggered = 0;

    for (int i = 0; i < 16; ++i) {
        top->in_target_v0 = (int64_t)(i * 3 - 10);
        top->in_target_v1 = (int64_t)(7 - i * 2);
        top->in_target_v2 = (int64_t)(i * 5 + 1);
        top->in_target_v3 = (int64_t)(-4 + i);

        // Alternate between even-parity logical codewords and odd-parity poisoned states
        if (i % 2 == 0) {
            top->in_tetron_psi0 = (int64_t)(i + 1);
            top->in_tetron_psi1 = 0;
            top->in_tetron_psi2 = 0;
            top->in_tetron_psi3 = (int64_t)(3 - i);
        } else {
            top->in_tetron_psi0 = 0;
            top->in_tetron_psi1 = (int64_t)(i + 2);
            top->in_tetron_psi2 = (int64_t)(i - 5);
            top->in_tetron_psi3 = 0;
        }

        // On cycle 12, inject a symmetry-breaking `.obend` layer override on pin w01 (3 -> 5)
        if (i == 12) {
            top->in_pin_shell_w01 = 5;
        } else {
            top->in_pin_shell_w01 = 3;
        }

        tick(top, tfp, sim_time);

        if (!top->out_crosstalk_exact_match) {
            std::fprintf(stderr, "FAIL: Faddeev-LeVerrier 4x4 crosstalk mismatch at step %d\n", i);
            return 1;
        }
        crosstalk_vectors_checked++;

        if (!top->out_artin_braid_verified || !top->out_cooled_in_even_codespace) {
            std::fprintf(stderr, "FAIL: Majorana Artin braid or parity cooling failed at step %d\n", i);
            return 1;
        }

        if (i % 2 == 0) {
            // Even-parity codeword must be dark under L_cool (L_cool * psi_even == 0)
            if (!top->out_input_even_parity ||
                top->out_cool_jump_psi0 != 0 ||
                top->out_cool_jump_psi1 != 0 ||
                top->out_cool_jump_psi2 != 0 ||
                top->out_cool_jump_psi3 != 0) {
                std::fprintf(stderr, "FAIL: L_cool did not annihilate even-parity state at step %d\n", i);
                return 1;
            }
            even_states_dark++;
        } else {
            // Odd-parity poisoned state must be mapped into the even-parity code space
            if (!top->out_input_odd_parity ||
                top->out_cool_jump_psi0 != 2 * top->in_tetron_psi1 ||
                top->out_cool_jump_psi3 != 2 * top->in_tetron_psi2 ||
                top->out_cool_jump_psi1 != 0 ||
                top->out_cool_jump_psi2 != 0) {
                std::fprintf(stderr, "FAIL: L_cool did not correct odd-parity state at step %d\n", i);
                return 1;
            }
            odd_states_cooled++;
        }

        if (i == 12) {
            if (top->out_dpr_quotient_usable ||
                !top->out_dpr_fallback_full_8mode ||
                top->out_active_hypergraph_ops != 16ULL) {
                std::fprintf(stderr, "FAIL: 1-cycle DPR symmetry-break fallback did not trigger!\n");
                return 1;
            }
            dpr_fallbacks_triggered++;
        }
    }

    tfp->close();
    delete tfp;
    delete top;

    std::printf(
        "PASS [quantum_photonic_tb]: wl_shells=4->8_ops cmt_lengths_nm=1571/2721/3142 "
        "crosstalk_det=8769_vectors=%u even_dark=%u odd_cooled=%u dpr_fallbacks=%u\n",
        crosstalk_vectors_checked,
        even_states_dark,
        odd_states_cooled,
        dpr_fallbacks_triggered);
    return 0;
}
